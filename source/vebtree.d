/**
    Copyright: Copyright (c) 2016- Alexander Orlov. All rights reserved.
    License: $(LINK2 https://opensource.org/licenses/MIT, MIT License).
    Authors: Alexander Orlov, $(LINK2 mailto:sascha.orlov@gmail.com, sascha.orlov@gmail.com) 
*/

/**
    This module implements a Van Emde Boas tree container.
    The module is still a work in progress. So, if you find an error by chance, please let me know in any way.
    The main idea of the container is, to restrict the capacity of the tree by the next power of two universe size,
    given an arbitrary size at the initialization. As long as the usage is intended to contains keys, as in the
    current version, this restriction is not only a restriction of the amount of elements but also on the contained
    element values. 
    For optimization purposes, the size limit is size_t.max/2 + 1. The tree was tested on 64- and 32-bit arch. 
    So the largest element which can be stored is 4.294.967.295 on a 64-bit architecture. 
*/

// (optional) todo: provide functionality to contain non-unique keys, i. e. exercise 20.3.1 from Cormen

/**
    The library is supposed to contain a tree on keys only, for the data could be managed outside. Then, there could be 
    a simple method to combine the keys and the data together. 
*/

/**
    The main advantage of the Van Emde Boas tree appears on a large amount of elements, as the provided standard
    operations of the tree are constant in time and of order O(lg2(lg2(U))), where U is the capacity of the tree. For
    small amount of elements the overhead coming along with the structure take over. For example, for a universe size of
    2^14 and 15872 insertion operatios the duration for the Van Emde Boas tree is about 1*10^(-3) times smaller. As one
    of the unittests shows. 
*/

/**
    Be aware, the current container is intended to be used with keys. This implies, that the capacity, fixed on its
    initialization has two meanings. As usual, it shows the maximum amount of elements the instanciated tree can keep.
    But also, it states, that no value bigger then capacity - 1 exists in the tree. This, and the fact, that only
    non-negative values can be used are infered from the term "key".
*/

/**
    See_also: Thomas H. Cormen, Clifford Stein, Ronald L. Rivest, and Charles E. Leiserson. 2001. <em>Introduction to
    Algorithms</em> (2nd ed.). McGraw-Hill Higher Education.
*/

/**
    As an important optimization a bottom out technique is used to compactify the tree to the level of nodes, where bit
    operations become possible. As a side effect, the optimization now relies on the underlying architecture. This leads
    to the fact, that the maximum of elements which can be stored is 
    2^16 on a 32-bit architecture and 
    2^32 on a 64-bit architecture. 
    This was intentionally chosen for two reasons: 
    i) to keep the size of a single node also depending from the underlying architecture. 
    ii) for bitoperations, which the tree is relying on, to use the native word size of the architecture without
    emulating bigger entities. 
*/

module vebtree; 

import std.typecons; // used for Nullable 
import core.bitop; // used for bit operations 
import std.bitmanip; // used for bitfields 
import std.traits; // used for generating the tree given an iterable
import std.range; 
import std.math : nextPow2; 
import core.stdc.limits : CHAR_BIT; 

private enum vdebug = false; 

version(unittest)
{
    static if(vdebug){import std.stdio;}
    import std.algorithm;
    import std.random; 
    import std.datetime.stopwatch; 
    import std.conv : to;
    import std.container; // red black tree may be used in unittests for comparison.
    import std.math : sqrt; 
    size_t[] powersOfTwo = iota(0, CHAR_BIT * size_t.sizeof).map!(a => size_t(1) << a).array; 
    Random rndGenInUse; 

    // helping function for output a given value in binary representation
    static if(vdebug)
    {
        void bin(size_t n)
        {
            /* step 1 */
            if (n > 1) bin(n/2);
            /* step 2 */
            write(n % 2);
        }
    }
    
    // during tests it is ok a tree with a random capacity not going up to the maximum one. 
    enum testedSize = 1 << 2 * size_t.sizeof; //3 * size_t.sizeof;
    // during tests helping static arrays are used, which have an absolute maximum of size_t.sizeof * 2^20 elements
    enum allowedArraySize = 1 << size_t.sizeof; //(2 * size_t.sizeof + size_t.sizeof/2); 
    // choosed arbitrary, to avoid seg. faults

    // some different filling functions for the tree. This simply tries to fill the tree with random numbers. Duplicates
    // will be ignored, the given tree is modified. 
    auto fill(ref VEBtree vT, size_t m, Random rndGenInUse)
    {
        size_t n; 
        for(size_t i; i < m; ++i)
        {
            auto x = uniform(0, vT.expectedSize, rndGenInUse);
            // the check for membership is done to add only on inserting to the counter, not just 
            // because visiting the the loop
            if(!(x in vT))
            {
                vT.insert(x); 
                ++n; 
            }
        }
        return n; 
    }

    // Ditto. This method asserts, that a given filling percentage is achieved. 
    auto fill(ref VEBtree vT, ref size_t[] arr, Random rndGenInUse, size_t fillPercentage = 31)
    {
        size_t n; 
        arr.length = fillPercentage * vT.capacity/32; 
        while(n != fillPercentage * vT.capacity/32)
        {
            auto x = uniform(0, vT.capacity - 1, rndGenInUse);
            // the check for membership is done to add only on inserting to the counter, not just 
            // because visiting the the loop
            if(!(x in vT))
            {
                vT.insert(x); 
                arr[n] = x; 
                ++n; 
            }
        }
        assert(n == fillPercentage*vT.capacity/32); 
        return n; 
    }
}

/**
    the baseSize defines the cutoff limit, where the node goes into the bit array mode. It is parametrized on the size
    of size_t and changes dynamically with the architecture used. 
*/
enum baseSize = CHAR_BIT * size_t.sizeof; 

/**
    the maxSizeBound defines the maximum the tree can be constructed with. It is parametrized on the size of size_t and
    changes dynamically with the architecture used. 
*/
enum maxSizeBound = (size_t(1) << baseSize/2) + 1; 

/**
    This function returns the higher square root of the given input. It is needed in the initialization step 
    of the VEB tree to calculate the number of children of a given layer. And this is the universe size of the
    summary of a node. The upper square root is defined by 2^{\lceil(\lg u)/2\rceil}
*/
@nogc nothrow size_t hSR(size_t value) 
{
    return size_t(1) << (bsr(value)/2 + ((bsr(value) & 1) || ((value != 0) && (value & (value - 1))))); 
}
///
unittest
{
    const size_t currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: hSR.              "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    auto hSR = hSR(M); 

    assert((hSR & (hSR - 1)) == 0); 
    if(hSR < uint.max) assert(hSR >= sqrt(to!float(M)));
    
    const auto check = powersOfTwo.until(hSR).array; 
    assert((check[$-1]) * (check[$-1]) < M); 
}

/**
    This function returns the lower square root of the given input. It is needed by the indexing functions
    high(x), low(x) and index(x,y) of elements in the tree. Also, this is the universe size of a child of a node. The
    lower square root is defined by 2^{\lfloor(\lgu)/2\rfloor}
*/
@nogc nothrow size_t lSR(size_t value) { return size_t(1) << (bsr(value)/2); }
///
unittest
{
    const size_t currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: lSR.              "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    auto lSR = lSR(M); 
    
    assert((lSR & (lSR - 1)) == 0); 
    assert(lSR * lSR < M);
    const auto check = powersOfTwo.find(lSR).array; 
    
    if(lSR < size_t.max/2) assert((check[1]) > sqrt(to!float(M))); 
}

/*
This is an index function defined as \lfloor x/lSR(u)\rfloor. It is needed to find the appropriate cluster
of a element in the tree. It is a part of the ideal indexing function. 
*/
private @nogc nothrow size_t high(size_t value, size_t uS) { return value >> (bsr(uS) / 2); }
//
unittest
{
    const size_t currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: high.             "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    const size_t U = nextPow2(M); 
    const size_t x = uniform(0U, U, rndGenInUse); 

    assert(high(x,U) == x / lSR(U)); 
}

/*
This is an index function defined as fmod(value, lSR(uS)). It is needed to find the appropriate
value inside a cluster. It is part of the ideal indexing function
*/
private @nogc nothrow size_t low(size_t value, size_t uS) { return value & ((size_t(1) << (bsr(uS) / 2)) - 1); }
//
unittest
{
    const size_t currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: low.              "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    const size_t U = nextPow2(M); 
    const size_t x = uniform(0U, U, rndGenInUse); 

    assert(low(x, U) == (x & (lSR(U) - 1)));
}

/*
This is an index function to retain the searched value. It is defined as x * lSR(u) + y. Beyond this, the
relation holds: x = index(high(x), low(x)). This is the ideal indexing function of the tree. 
*/
private @nogc nothrow size_t index(size_t uS, size_t x, size_t y){ return (x * lSR(uS) + y); }
//
unittest
{
    const size_t currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: index.            "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(0U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    
    const size_t U = nextPow2(M); 
    const size_t x = uniform(0U, U, rndGenInUse); 
    
    assert(index(U, high(x, U), low(x, U)) == x); 
}

/**
    This is the struct to represent a VEB tree node. As memebers it contains a value and a pointer to the children
    array. As the pointer does not know the size of the array, it has to be passed in all methods, which require an
    access to it. 
    Dependent from the (universe) size passed in a method the stored value will be interpretated in two different ways: 
    If the parameter passed shows, that the universe size is below the bit size of the stored value, then, it can be
    handled as a bit array and all operations decay to operations defined in core.bitop. This case correspond to
    the state of the node being a leaf. No children exist and the pointer should stay uninitialized
    Otherwise, the value is interpretated as two values, the minimum and maximum stored at the same place in memory. The
    minimum and maximum shows, which range is achievable through this node. The parameters passed to a function of the
    node have to be well chosen, to hit the appropriate child. 
    The first element of the children array, if present is handled different. According to literature, it has the role
    of the summary of the remaining children cluster. With it help it is possible to achieve a very small recursion
    level during an access. 
*/
struct VEBnode
{
    /*
        This pointer acts as an array to nodes like this one. As the universe size is not provided, the length of the
        array can not be used to calculate the most of operations, so no explicit array is needed. The only remaining
        property is whether the pointer is set at all. From this property the node can decide, whether it is a leaf or
        an intermediate node. 
    */
    private VEBnode* ptrArr; // the first member behaves different, as the others, as it is the summary node. 

    /// property returning the summary node 
    @nogc nothrow @property ref inout(VEBnode) summary() inout
    in { assert(!isLeaf); }
    body { return ptrArr[0]; }
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        static if(vdebug){write("UT: vN, summary.      "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        VEBnode vN = VEBnode(512); 
        assert(!vN.isLeaf); 
        vN.ptrArr[0]._val = 73; 
        assert(vN.summary._val == 73);
    }
    
    /// property returning the cluster array 
    @nogc nothrow @property inout(VEBnode*) cluster() inout
    in { assert(!isLeaf); }
    body { return (ptrArr + 1); }
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        static if(vdebug){write("UT: vN, cluster.      "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        const auto value = uniform!"[]"(2U, testedSize, rndGenInUse);
        const auto place = uniform(0U,baseSize, rndGenInUse);
        
        VEBnode vN = VEBnode(4096); 
        vN.ptrArr[place]._val = value; 
        assert(vN.ptrArr[place]._val == value); 
        assert(vN.cluster[place - 1]._val == value); // the right place: it is the (place - 1) location of clusters
        vN.cluster[place]._val = 73; 
    }
    
    /*
        An unnamed union defines the essential behavior of the node. It is either a real node with a min and a max, or
        it is a ulong which is handled as a bit array. 
    */ 
    union 
    {
        /*  
            as the underlying type size_t is chosen. It is the intended choice, as this delivers the maximum storage
            size without emulation of types, which size is not native to an architecture. 
            As the value behaves different depending on the node being a leaf. A special consideration should be done,
            how the unset state has to be stored. 
            In case of being a leaf, the value is interpreated as bit vector, storing a "zero" correspond to setting the
            least bit. So the unset state corresponds to value being zero. 
            In case of being an intermediate node, the both stored values min and max correspond to a range. In this
            case the state of being unset is modeled by a minimum set to a value greater then the maximum on
            initialization. 
            For the case a function is queried and the answer correnspond to a state being not set a Nullable.null is
            returned from the very method. The null value in the Nullable type doesn't need to enlarge it, as on every
            architecture all values beyond 2^(8 * size_t.sizeof / 2) - 1 stays unused It is not possible to construct
            a tree large enough to contain these values. Due this fact the null-value for the Nullable is chosen to
            2^(8 * size_t.sizeof / 2)
        */
        private size_t _val;  
        mixin(bitfields!(
            size_t, "_min", baseSize/2, // the default value of the min is greater then the max. 
            size_t, "_max", baseSize/2
        ));
    }

    /*
        It is not allowed to construct a node without providing the current universe size as it has to be known on
        creation whether the children nodes have to be constructed. So, the default case is forbidden, as the children
        may not appended beyond the knowledge of the constructor. 
    */
    @disable this(); 
    /**
        Node constructor. A universe size provided, if the size is below the cutoff there is nothing to be done, as the
        underlying value created and set to zero by default. 
        If otherwise create an array of children. This array has to be (according to Cormen) of size of higher square
        root of the current universe size + 1. The extra place is reserved for the summary. 
        For each just created child call its constructor.
        For the summary with the universe size of the higher square root of the current universe size. 
        For each other child with the universe size of the lower square root of the currennt universe size. 
        Then, assign the fully initialized children array to the pointer in the current node, doing approprate steps to
        show, that this node is an intermediate node, not containing any values yet. 
        The knowledge of the current universe size is lost at this moment. As this keeps every build up node smaller 
        (and there could be a lot of them). This is why, the VEBtree class continues to hold the global universe size,
        which is passed on every call to the root node. In this way this, extern saved value has the role of being
        outsourced array size for each (!) node in the tree, as its size is reconstructed during the access to them. 
    */
    nothrow this(size_t uS)
    {
        if(uS > baseSize)
        {
            VEBnode[] tmp; 
            tmp.reserve(hSR(uS) + 1); // reserve enough place for the summary and the children cluster
            tmp ~= VEBnode(hSR(uS)); // add the summary with its universe of higher squaure root of the current universe
            for(size_t i = 1; i <= hSR(uS); ++i)
                tmp ~= VEBnode(lSR(uS)); // add higher square root children with lower square root universe each.
            ptrArr = tmp.ptr; // save the pointer to the array, loosing the information about its length. 
            nullify; // set the value to the sentinel value to represent the empty state. 
        }
        // else nothing todo.
    }
    unittest
    {
        auto currentSeed = unpredictableSeed(); 
        static if(vdebug){write("UT: vN, __ctor.       "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        const auto uS = uniform!"[]"(2U, testedSize, rndGenInUse);
        
        const VEBnode vN = VEBnode(uS);
        if(uS <= baseSize)
        {
            assert(vN.isLeaf); 
            assert(vN._val == 0);
            assert(vN.ptrArr == null); 
        } 
        else
        {
            assert(!vN.isLeaf); 
            assert(vN._val == 1);
            assert(vN.ptrArr != null); 
        }
    }

    /** convinience method to check, if the node belongs to the lowest level in the tree */
    @nogc nothrow @property bool isLeaf() const { return ptrArr == null; }
    
    /** method to check whether the current node holds a value */
    @nogc nothrow @property bool isNull() const { return isLeaf ? (_val == 0) : (_min > _max); }

    /** method executing the appropriate steps to nullify the current node */
    @nogc nothrow @property void nullify() { _val = isLeaf ? 0 : 1; }  

    /**
        method returning either the lower part of the stored value (intermediate node) or the lowest bit set (bit vector
        mode. If the node does not contain any value (min > max or value == 0) Nullable.null is returned. 
    */
    @nogc nothrow @property Nullable!(size_t, maxSizeBound) min() const
    {
        // define the result as a nullable 
        Nullable!(size_t, maxSizeBound) retVal; 
        /*
            we have only a chance to get a value, if a value is present.
            if it is a leaf, handle the val as a bit array and find the first bit set from the right. 
            if it is not a leaf, get the minimum. 
        */ 
        if(!isNull) retVal = isLeaf ? bsf(_val) : _min; 
        // return the result, even if it was not set to a value. 
        return retVal;  
    }

    /**
        setter for the min, setting either the lowest bit or the min part of the value. 
    */
    @nogc nothrow @property void min(size_t value)
    {
        if(isLeaf)
        {
            assert(min > value);
            insert(value); 
        }
        else
        {
            // the passed value should not exceed the allowed size of a size/2
            assert(value < maxSizeBound); 
            _min = value; 
        }
    }

    /** 
        method returning either the higher part of the stored value (intermediate node) or the highest bit set (bit
        vector mode. If the node does not contain any value (min > max or value == 0) Nullable.null is returned. 
    */
    @nogc nothrow @property Nullable!(size_t, maxSizeBound) max() const
    {
        // define the result as a nullable
        Nullable!(size_t, maxSizeBound) retVal; 
        /*
            we have only a chance to get a value, if a value is present. 
            if it is a leaf, handle the val as a bit array and find the first bit set from the left. 
            if it is not a leaf, get the max. 
        */
        if(!isNull) retVal = isLeaf ? bsr(_val) : _max; 
        // return the result, even if it was not set to a value. 
        return retVal;  
    }

    /**
        setter for the max, setting either the highest bit or the max part of the value. 
    */
    @nogc nothrow @property void max(size_t value)
    {
        if(isLeaf) 
        {
            assert(max < value); 
            insert(value); 
        }
        else
        {
            // the passed value should not exceed the allowed size of a size/2
            assert(value < maxSizeBound); 
            _max = value; 
        }
    }

    /**
        member method for the case universe size < base size. Overloads by passing only one parameter, which is
        the bit number of interest. Returns whether the appropriate bit inside the bitvector is set.
    */
    @nogc nothrow bool opIn_r(size_t bitnum) const
    in
    {
        // method inside the node defined on leafs only. 
        assert(isLeaf); 
        // when a bitnum is passed to the leaf, then, it is an index to the bitarray and has to be in proper range
        assert(bitnum < baseSize);
    }
    body { return bt(&_val, bitnum) != 0; }
    //
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        static if(vdebug){write("UT: vN, opIn_r.       "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        const auto value = uniform(0U,size_t.max, rndGenInUse);
        const auto bitNum = uniform(0U,baseSize, rndGenInUse);
        VEBnode vN = VEBnode(baseSize); 
        vN._val = value; 
        
        if((vN._val & size_t(1) << bitNum) != 0 ) assert(bitNum in vN); 
        if((vN._val & size_t(1) << bitNum) == 0 ) assert(!(bitNum in vN)); 
    }

    /**
        member method. this method is called from class with a universe size given. It performs recursion calls until
        the universe size is reduced to the base size. Then the overloaded member method is called. 
    */
    @nogc nothrow bool member(size_t value, size_t uS) const
    {
        if(uS <= baseSize) return (value in this); // do not use other functionality any more, if descended so far. 

        if(this.isNull) return false; // if an empty intermediate node is found, nothing is stored below it. 
        if(value == this.min || value == this.max) return true; // case of a single valued range. 

        /*
            else we have to descend, using the recursive indexing: 
            1. take the high(value, uS)-th child and 
            2. ask it about the reduced low(value, uS) value
            3. use the lSR(uS) universe size of the childe node. 
        */
        return cluster[high(value, uS)].member(low(value, uS), lSR(uS)); 
    }

    /**
        insert method. given a leaf, sets the bit and returns, whether the bit was unset. Overloads by passing only one
        parameter, which is the bit number of interest.
    */
    @nogc nothrow bool insert(size_t bitnum)
    in
    {
        // method inside the node defined on leafs only. 
        assert(isLeaf); 
        // when a bitnum is passed to the leaf, then, it is an index to the bitarray and has to be in proper range
        assert(bitnum < baseSize);
    }
    body { return bts(&_val, bitnum) == 0; }

    /**
        insert method. this method is called from class with a universe size given. It performs recursion calls untill
        the universe size is reduced to the base size. Then the overloaded insert method is called. 
    */
    @nogc nothrow bool insert(size_t value, size_t uS)
    {
        import std.algorithm.comparison : min, max;
        
        if(uS <= baseSize) return this.insert(value); // if descended so far, do not use other functionality any more. 

        if(this.isNull) // if the current node does not contain anything put the value inside. 
        {
            this.min = value; // the setters of min handle the value appropriately and do not need the universe size
            this.max = value; // being explicitely provided, as they can check the isLeaf property. 
            assert(!this.isNull); 
            return true; 
        }

        assert(!this.isNull);
        assert(!this.min.isNull); 
        assert(!this.max.isNull); 

        if(value == this.min || value == this.max) return false; // return, if value is already here.

        if(this.min == this.max) // if the node contains a single value only, expand the node to a range and leave. 
        {
            this.min = min(this.min, value); 
            this.max = max(this.max, value); 
            return true; 
        }
        /*
            if none of the cases above was true (all of them are break conditions) we have to compare the given value
            with the values present and adapt the range limits. This replaces the value we want to insert. 
        */
        // a swap can not be used here, as min is itself a (property) method 
        if(value < this.min) {const auto tmp = value; value = this.min.get; this.min = tmp; }
        // a swap can not be used here, as max is itself a (property) method 
        if(value > this.max) {const auto tmp = value; value = this.max.get; this.max = tmp; }
        
        // calculate the index of the children cluster by high(value, uS) we want to descent to. 
        auto nextTreeIndex = high(value, uS); 
        
        // if the child is happened to be null we have to update the summary and insert value of high(value, uS) into it
        if(cluster[nextTreeIndex].isNull) summary.insert(high(value, uS), hSR(uS));
        
        // in any case we pass the lowered value low(value, uS) to the child. 
        auto res = cluster[nextTreeIndex].insert(low(value, uS), lSR(uS)); 
        return res;
    }

    /**
        remove method. given a leaf, remove the bit and returns, whether the bit was set. Overloads by passing only one
        parameter, which is the bit number of interest.
    */
    @nogc nothrow bool remove(size_t bitnum)
    in
    {
        assert(isLeaf); 
        assert(bitnum < baseSize); 
    }
    body { return btr(&_val, bitnum) != 0; }

    /**
        remove method. this method is called from class with a universe size given. It performs recursion calls untill
        the universe size is reduced to the base size. Then the overloaded remove method is called. 
    */
    @nogc nothrow bool remove(size_t value, size_t uS)
    {
        if(uS <= baseSize) return this.remove(value); // if descended so far, do not use other functionality any more. 
        if(this.isNull) return false; // if the current node is null, there is nothing to remove. 
        if(this.min == this.max) // if the current node contains only a single value
        {
            if(this.min != value) return false; // do nothing if the given value is not the stored one 
            this.nullify; // set this node to the sentinel-null if it does. 
            return true; 
        }
        if(value == this.min) // if we met the minimum of a node 
        {
            auto treeOffset = summary.min; // calculate an offset from the summary to continue with
            if(treeOffset.isNull) // if the offset is invalid, then there is no further hierarchy and we are going to 
            {
                this.min = this.max; // store a single value in this node. 
                return true; 
            }
            auto min = cluster[treeOffset].min; // otherwise we get the minimum from the offset child
            cluster[treeOffset].remove(min, lSR(uS)); // remove it from the child 

            // if it happens to become null during the remove process, we also remove the offset entry from the summary 
            if(cluster[treeOffset].isNull) summary.remove(treeOffset, hSR(uS)); 

            //anyway, the new min of the current node become the restored value of the calculated offset. 
            this.min = index(uS, treeOffset, min); 
            
            return true; 
        }
        if(value == this.max) // if we met the maximum of a node 
        {
            auto treeOffset = summary.max; // calculate an offset from the summary to contiue with 
            if(treeOffset.isNull) // if the offset is invalid, then there is no further hierarchy and we are going to 
            {
                this.max = this.min; // store a single value in this node. 
                return true; 
            }

            auto max = cluster[treeOffset].max; // otherwise we get maximum from the offset child 
            cluster[treeOffset].remove(max, lSR(uS)); // remove it from the child 

            // if it happens to become null during the remove process, we also remove the offset enty from the summary 
            if(cluster[treeOffset].isNull) summary.remove(treeOffset, hSR(uS)); 

            // anyway, the new max of the current node become the restored value of the calculated offset. 
            this.max = index(uS, treeOffset, max); 
            return true; 
        }

        // if no condition was met we have to descend deeper. We get the offset by reducing the value to high(value, uS)
        auto treeOffset = high(value, uS); 
        // and remove low(value, uS) from the offset child. 
        const bool retVal = cluster[treeOffset].remove(low(value, uS), lSR(uS)); 
        // if the cluster become null during the remove process we have to update the summary node. 
        if(cluster[treeOffset].isNull) summary.remove(treeOffset, hSR(uS)); 

        return retVal; 
    }

    /**
        predecessor method. given a leaf, returns the previous set bit if exists, otherwise Nullable.null. Overloads by
        passing only one parameter, which is the bit number of interest.
    */
    @nogc nothrow Nullable!(size_t, maxSizeBound) predecessor(size_t bitNum) const
    in
    {
        assert(isLeaf); 
        assert(bitNum < baseSize); 
    }
    body
    {
        Nullable!(size_t, maxSizeBound) retVal; 
        
        if(!isNull && (bitNum != 0))
        {
            // create a mask, which hides all higher bits of the stored value down to the given bit number, then apply
            // bit search from the highest bit. 
            auto maskedVal = _val & ((size_t(1) << bitNum) - 1); 
            if(maskedVal != 0) retVal = bsr(maskedVal);
        }
        return retVal; 
    }
    //
    unittest
    {
        const size_t currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vN, predecessor.  "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator
        const size_t v = uniform(2U, testedSize, rndGenInUse); //set universe size to some integer. 
        const size_t x = uniform(1U, baseSize, rndGenInUse);
        VEBnode vN = VEBnode(baseSize); 
        vN._val = v; 

        bool found; 

        for(size_t index = x - 1; index >= 0; --index)
        {
            if (v & (size_t(1) << index)) 
            {
                found = true; 
                assert(!vN.isNull);
                assert(vN.predecessor(x) == index); 
                break; 
            }
            if(!index) break; 
        }

        if(!found) assert(vN.predecessor(x).isNull); 
    }

    /**
        predecessor method. this method is called from class with a universe size given. It performs recursion calls
        until the universe size is reduced to the base size. Then the overloaded predecessor method is called. 
    */
    @nogc nothrow Nullable!(size_t, maxSizeBound) predecessor(size_t value, size_t uS) const
    {
        Nullable!(size_t, maxSizeBound) retVal; 
        
        if(uS <= baseSize) return predecessor(value); // if descended so far, do not use other functionality any more. 
        if(this.isNull) return retVal; // if this node is empty, no predecessor can be found here or deeper in the tree
        if(value > this.max) return this.max; // if given value is greater then the stored max, the predecessor is max
        if(value <= this.min) return retVal; // if given value is less then the min, no predecessor exists. 

        /*
            if none of the break conditions was met we have to descend further into the tree. 
        */
        const auto childIndex = high(value, uS); // calculate the child index by high(value, uS)
        const auto minlow = cluster[childIndex].min; // look into the child for its minimum
        // if the minimum exists and the lowered given value is greater then the child's minimum
        if(!minlow.isNull && low(value, uS) > minlow) 
        {
            // calculate an offset to continue with by asking the child on predecessor of the lowered value. 
            auto offset = cluster[childIndex].predecessor(low(value, uS), lSR(uS)); 
            // the result is given by reconstruction of the answer. 
            retVal = index(uS, childIndex, offset); 
        }
        else // otherwise we can not use the minimum of the child 
        {
            // ask the summary for the predecessor cluster. 
            auto predcluster = summary.predecessor(childIndex, hSR(uS));
            // if the predecessor cluster is null return the current min, as this is the last remaining value 
            if(predcluster.isNull) return this.min; 
            // if the predecessor cluster exists, the offset is given by its maximum
            // and the result by the reconstruction of the offset. 
            retVal = index(uS, predcluster, cluster[predcluster].max); 
        }
        return retVal; 
    }

    /**
        successor method. given a leaf, returns the next set bit if exists, otherwise Nullable.null. Overloads by
        passing only one parameter, which is the bit number of interest.
    */
    @nogc nothrow Nullable!(size_t, maxSizeBound) successor(size_t bitNum) const
    in
    {
        assert(isLeaf); 
        assert(bitNum < baseSize); 
    }
    body
    {
        Nullable!(size_t, maxSizeBound) retVal; 
        
        if(!isNull && (bitNum + 1 < baseSize)) 
        {
            // create a mask, which hides all lower bits of the stored value up to the given bit number, then apply
            // bit search from the lowest bit. 
            auto maskedVal = _val & ~((size_t(1) << (bitNum + 1)) - 1); 
            if(maskedVal != 0) retVal = bsf(maskedVal);
        }
        return retVal; 
    }
    //
    unittest
    {
        const size_t currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vN, successor.    "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator
        const size_t v = uniform(0U, size_t.max, rndGenInUse); //set universe size to some integer. 
        const size_t x = uniform(0U, baseSize, rndGenInUse);
        VEBnode vN = VEBnode(baseSize); 
        vN._val = v; 
      
        bool found; 

        for (size_t index = x + 1; index < baseSize; ++index)
        {
            if (v & (size_t(1) << index)) 
            {
                found = true; 
                assert(vN.successor(x) == index); 
                break; 
            }
        }
        if(!found) assert(vN.successor(x).isNull);
    }

    /**
        successor method. this method is called from class with a universe size given. It performs recursion calls until
        the universe size is reduced to the base size. Then the overloaded successor method is called. 
    */
    @nogc nothrow Nullable!(size_t, maxSizeBound) successor(size_t value, size_t uS) const
    {
        Nullable!(size_t, maxSizeBound) retVal; 
        if(uS <= baseSize) return successor(value); // if descended so far, do not use other functionality any more. 
        if(this.isNull) return retVal; // if this node is empty, no successor can be found here or deeper in the tree
        if(value < this.min) return this.min; // if given value is less then the min, return the min as successor
        if(value >= this.max) return retVal; // if given value is greater then the max, no predecessor exists

        /*
            if none of the break conditions was met, we have to descent further into the tree. 
        */
        const auto childIndex = high(value, uS); // calculate the child index by high(value, uS)
        const auto maxlow = cluster[childIndex].max; // look into the child for its maximum
        // if the maximum exists and the lowered given value is less then the child's maximum 
        if(!maxlow.isNull && low(value, uS) < maxlow)
        {
            // calculate an offset to continue with by asking the child on predecessor of the lowered value
            auto offset = cluster[childIndex].successor(low(value, uS), lSR(uS)); 
            // the result is given by reconstruction of the answer
            retVal = index(uS, childIndex, offset);
        }
        else // otherwise we can not use the maximum of the child 
        {
            // ask the summary for the successor cluster. 
            auto succcluster = summary.successor(childIndex, hSR(uS)); 
            // if the successor cluster is null
            if(succcluster.isNull) return this.max; // return the current max, as this is the last remaining value 
            // if the successor cluster exists, the offset is given by its minimum
            // and the result by the reconstruction of the offset. 
            retVal = index(uS, succcluster, cluster[succcluster].min); 
        }
        return retVal; 
    }
}

///
unittest
{
    VEBnode vN = VEBnode(baseSize); 
    static assert(vN.sizeof < baseSize/2); 
    assert(vN.isNull); 
    assert(vN.sizeof == 2 * size_t.sizeof); 
    assert(vN.isLeaf); 
    assert(vN.isNull); 
    vN._val = 3; 
    assert(vN._min == 3);
    assert(1 in vN);
    assert(!(2 in vN));
    assert(vN.isLeaf);
    assert(vN.ptrArr == null); 
    vN.nullify; 
    assert(vN.isNull); 
    assert(vN._val == 0); 
}

/**
    This class represents the VEB tree itself. It saves the provided at the initialization step wished size. The
    generated tree has the capacity of the next higher power of 2. Beyond this, it stores the root element, through
    which all accesses to the tree are managed. The tree implements also the interface for being a bidirectional range.
*/
class VEBtree
{
    // the root element of the tree. 
    private VEBnode* root; 
    // this member is updated on every insertion and deletion to give the current element count on O(1)
    private size_t _elementCount; 
    /// this member stores the initialization size, as it would be lost forever after initialization, otherwise
    immutable size_t expectedSize; 
    /// this value tracks the total range of the tree to be able to move on it independent from its copies
    private auto _range = iota(0UL); 
    
    /// default constructor of a VEB tree is disabled. 
    @disable this(); 

    private this(VEBnode* root_, size_t expectedSize_, size_t elementCount_, typeof(iota(0UL)) range_) @nogc
    {
        root = root_; 
        expectedSize = expectedSize_; 
        _elementCount = elementCount_; 
        _range = range_; 
    }
    
    /**
        to construct a VEB tree the wished size has to be provided. However, the size should be greater then one and
        should not excess the maximum allowed size for the current architecture. 
    */
    nothrow this(size_t value)
    in
    {
        assert(value > 1); 
        assert(value < maxSizeBound);
    }
    body
    {
        // set the expected size to the passed value 
        expectedSize = value; 
        // delegate the creation of the nodes with the apropriate power of two of the needed universe size
        root = new VEBnode(nextPow2(expectedSize - 1)); 

        assert(this.empty);
    }
    ///
    unittest
    {
        auto currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vT, __ctor.       "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        auto uS = uniform(1U << size_t(1),testedSize, rndGenInUse);
        const VEBtree vT = new VEBtree(uS); 
        assert(vT.empty);
        if((uS & (uS - 1)) == 0)
            assert(vT.capacity == uS); 
        else
            assert(vT.capacity == (size_t(1) << (bsr(uS) + 1))); 
        
        assert(vT.expectedSize == uS); 
        
        const auto uS1 = uniform(1U << size_t(1),testedSize, rndGenInUse);
        const auto uSsmall = uniform(1U << size_t(1),baseSize, rndGenInUse);
        VEBtree vT1 = new VEBtree(uS1); 
        const VEBtree vTsmall = new VEBtree(uSsmall); 

        assert(vTsmall.root._val == 0);
        assert(vTsmall.root.ptrArr == null); 

        if(uS1 > CHAR_BIT * size_t.sizeof)
        {
            assert(vT1.root._val == 1);
            assert(vT1.root.ptrArr != null); 
            
            //check every child for consistency. 
            // the size of a node is higher square root & the summary node. 
            
            // capacity is tested elsewhere. 
            // hSR is also tested elsewhere
            const auto childsAmount_l1 = hSR(vT1.capacity) + 1; 
            const auto childsAmount_l2 = hSR(lSR(vT1.capacity)) > baseSize ? hSR(lSR(vT1.capacity)) + 1 : 0; 
            
            // the tree is just created, assert all children are nullified
            for(size_t i; i < childsAmount_l1; ++i)
            {
                assert(vT1.root.ptrArr[i].isNull);
                if(childsAmount_l1 > baseSize + 1)
                {
                    for(size_t j; j < childsAmount_l2; ++j)
                    {
                        assert(vT1.root.ptrArr[i].ptrArr[j].isNull);
                    }
                }
            }
        }
    }
    
    /// another possibility is to construct a VEB tree is by providing an array.
    nothrow this(R)(R range) if(isIterable!R)
    in
    {
        // check, whether the range is not too long. I. e. expressable with an uint. 
        assert(range.length < maxSizeBound);
    }
    body
    {
        import std.algorithm.comparison : max;
        // first, we have to determine the size of the tree. 
        // it is either derived from the length of the given tree or its greatest element
        size_t limit; 
        foreach(size_t i; range) limit = max(limit,i); 
        // assert no element has exceeded the allowed range of baseSize/2
        assert(limit < maxSizeBound);
        // if the array is longer, then the greatest element, but the length passes, substitute the limit
        limit = max(limit, range.length); 
        // call the constructor with the limit
        this(limit + 1);
        // put every element from the range into the tree
        foreach(size_t i; range) insert(i); 
    }
    
    /** 
        this method returns the capacity of the tree. It is equal to the next power of 2 regarding the size used at
        initialization. 
    */
    @nogc nothrow size_t capacity() const { return nextPow2(expectedSize - 1); }
    
    /**
        this method is used to add an element to the tree. duplicate values will be ignored. the class provides an
        intermediate layer between the caller and the contained root and enrichs the input by the stored size. 
    */
    auto insert(size_t value) @nogc nothrow 
    {
        if(value >= capacity) return false; 
        const bool retVal = root.insert(value, capacity); 
        if(retVal)
        {
            ++_elementCount; 

            if(length == 1) _range = iota(value, value + 1UL); 
            else
            {
                if(value < _range.front) _range = iota(value, _range.back + 1UL); 
                if(value > _range.back) _range = iota(_range.front, value + 1UL); 
            }
            
        } 
        return retVal; 
    }
    ///
    unittest
    {
        auto currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vT, insert.       "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
        VEBtree vT = new VEBtree(uS); 

        size_t n; 
        uint[allowedArraySize] insertedVals;  
        while(n < allowedArraySize)
        {
            auto valToInsert = uniform(0U, uS, rndGenInUse); 
            const bool inserted = vT.insert(valToInsert); 
            if(inserted)
            {
                insertedVals[n] = valToInsert; 
                n++;
            }
        }
        assert(vT._elementCount == insertedVals.length); 
        
        sort(insertedVals[]); 
        assert(uniq(insertedVals[]).array.length == insertedVals.length); 
    }

    /// this method overrides the insert method to directly use arrays
    @nogc nothrow void insert(R)(R arr) if(isIterable!R){ foreach(size_t i; arr) insert(i); }

    /// this method is used to remove elements from the tree. not existing values will be ignored. 
    bool remove(size_t value) @nogc nothrow 
    {
        const bool retVal = root.remove(value, capacity); 
        if(retVal)
        {
            --_elementCount;
            if(length == 0) _range = iota(0UL);
            else
            {
                assert(!_range.empty); 
                if(value == _range.front) popFront(); 
                if(value == _range.back) popBack(); 
            }
        } 
        return retVal; 
    }
    ///
    unittest
    {
        auto currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vT, remove.       "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
        VEBtree vT = new VEBtree(uS); 

        size_t n; 
        uint[allowedArraySize] insertedVals;  
        
        while(n < allowedArraySize)
        {
            auto valToInsert = uniform(0U, uS, rndGenInUse); 
            if(vT.insert(valToInsert))
            {
                insertedVals[n] = valToInsert; 
                n++; 
            }
        }
        
        assert(vT._elementCount == insertedVals.length); 
        
        foreach(size_t i; insertedVals) assert(vT.remove(i)); 
        assert(vT.length == 0); 
    }

    /// this method is used to determine, whether an element is currently present in the tree
    @nogc nothrow bool opIn_r(size_t value) const 
    {
        if(value >= capacity) return false;
        return root.member(value, capacity); 
    }
    ///
    unittest
    {
        auto currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vT, member.       "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator
         
        auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
        VEBtree vT = new VEBtree(uS); 

        size_t n; 
        uint[allowedArraySize] insertedVals;  
        while(n < allowedArraySize)
        {
            auto valToInsert = uniform(0U, uS, rndGenInUse); 
            if(vT.insert(valToInsert))
            {
                insertedVals[n] = valToInsert; 
                n++;
            }
        }
        
        sort(insertedVals[]); 
        auto sortedInserted = assumeSorted(insertedVals[]); 
        for(size_t i; i < testedSize; ++i)
        {
            if(sortedInserted.contains(i))
            {
                assert(i in vT);
            }
            else 
            {
                assert(!(i in vT), "i: " ~ to!string(i)); 
            }
        }
    }
        
    /// this method is used to determine the minimum of the tree
    @nogc nothrow @property Nullable!(size_t, maxSizeBound) min() const { return root.min; }

    /// this method is used to determine the maximum of the tree    
    @nogc nothrow @property Nullable!(size_t, maxSizeBound) max() const { return root.max; }

    /// this method retrieves the successor of the given input.
    Nullable!(size_t, maxSizeBound) successor(alias boundaries = "()")(size_t value) const
    {
        if(value >= capacity) return Nullable!(size_t, maxSizeBound)(); 

        // otherwise get the successor
        auto currentSuccessor = root.successor(value, capacity); 
        
        // in case of closed boundaries
        static if(boundaries[1] == ']') // if there is a successor (between the value and the upper bound)
        {
            if(!currentSuccessor.isNull) return currentSuccessor; // return the successor
            else return Nullable!(size_t, maxSizeBound)(capacity); // otherwise return the bound (capacity)
        }
        else return currentSuccessor; // in case of open boundaries return the successor (null or a value)
    }
    unittest
    {
        auto currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vT, successor.    "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator
         
        auto uS = uniform(allowedArraySize, testedSize, rndGenInUse);
        VEBtree vT = new VEBtree(uS); 

        // testing the boundaries now: 
        auto randomElement = uniform(allowedArraySize, uS); 
        assert(vT.successor(randomElement).isNull);
        assert(vT.successor!"[]"(randomElement) == vT.capacity);

        size_t n; 
        uint[allowedArraySize] insertedVals;  
        while(n < allowedArraySize)
        {
            auto valToInsert = uniform(0U, uS, rndGenInUse); 
            if(vT.insert(valToInsert))
            {
                insertedVals[n] = valToInsert; 
                n++;
            }
        }
        
        auto sortedInserted = assumeSorted(sort(insertedVals[])); 

        assert(vT.max == sortedInserted.back); 
        assert(vT.min == sortedInserted.front); 
        size_t j; 

        for(size_t i; i <= testedSize; ++i)
        {
            const auto el = vT.successor(i); 
            
            if(el.isNull)
            {
                assert(i == vT.max); 
                assert(sortedInserted.contains(i));
                break; // quit the loop;
            }
            else
            {
                if(sortedInserted.contains(i)) ++j; 
                assert(el == sortedInserted[j]); 
            }
        }   
    }

    /// this method retrieves the predecessor of the given input. 
    @nogc nothrow Nullable!(size_t, maxSizeBound) predecessor(alias boundaries = "()")(size_t value) const
    {
        auto currentPredecessor = root.predecessor(value, capacity); 
        static if(boundaries[0] == '[')
        {
            if(!currentPredecessor.isNull)
                return currentPredecessor; 
            else 
                return Nullable!(size_t, maxSizeBound)(0); 
        }
        else return currentPredecessor; 
    }
    ///
    unittest
    {
        auto currentSeed = unpredictableSeed();
        static if(vdebug){write("UT: vT, predecessor.  "); writeln("seed: ", currentSeed);} 
        rndGenInUse.seed(currentSeed); //initialize the random generator
         
        auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
        VEBtree vT = new VEBtree(uS); 

        // testing the boundaries now: 
        auto randomElement = uniform(allowedArraySize, uS); 
        assert(vT.predecessor(randomElement).isNull);
        assert(vT.predecessor!"[]"(randomElement) == 0);

        size_t n; 
        uint[allowedArraySize] insertedVals;  
        while(n < allowedArraySize)
        {
            auto valToInsert = uniform(0U, uS, rndGenInUse); 
            if(vT.insert(valToInsert))
            {
                insertedVals[n] = valToInsert; 
                n++;
            }
        }
        
        auto sortedInserted = assumeSorted(sort(insertedVals[])); 

        assert(vT.max == sortedInserted.back); 
        assert(vT.min == sortedInserted.front); 
        size_t j = allowedArraySize - 1; 

        size_t i = testedSize + 1; 
        do
        {
              --i;
            const auto el = vT.predecessor(i); 
            if(el.isNull)
            {
                assert(i == vT.min); 
                assert(sortedInserted.contains(i));
                break; // quit the loop;

            }
            else
            {
                if(sortedInserted.contains(i)) --j; 
                assert(el == sortedInserted[j]); 
            }
             
        }while(i > 0);
    }

    /// this method is used to determine, whether the tree is currently containing an element. 
    @nogc nothrow @property bool empty() const { return _range.empty; }

    /// this method returns the minimium. 
    @nogc nothrow @property size_t front() { return _range.front; }

    /// this method removes the minimum element
    void popFront() @nogc nothrow
    {
        auto s = successor(_range.front); 
        if(s.isNull) _range = iota(maxSizeBound, 0UL); 
        else _range = iota(s.get, _range.back + 1UL); 
    }

    /// bidirectional range also needs
    @nogc nothrow @property size_t back() { return _range.back; }
    
    /// this method removes the maximum element 
    @nogc nothrow void popBack()
    {
        if(!empty)
        {
            assert(!_range.empty); 
            auto p = predecessor(_range.back);
            if(p.isNull) _range = iota(maxSizeBound, 0UL); 
            else _range = iota(_range.front, p.get + 1UL); 
        }
    }
    
    /// Returns whether the element is in the tree 
    auto opIndex(size_t index) const @nogc nothrow
    {
        if(index in this) return index; 
        else return maxSizeBound; 
    }

    /// This method returns the amount of elements currently present in the tree.
    @nogc nothrow @property size_t length() const { return _elementCount; }
    
    /**
        forward range also needs save. This is a draft version of the save function, it uses the opslice of the struct
        to construct a new one via an array
    */
    @property VEBtree save() { return new VEBtree(root, expectedSize, _elementCount, _range.save); }

    /// dollar operator overload. 
    @nogc nothrow @property size_t opDollar() 
    {
        auto cMax = this.max; 
        if(cMax.isNull) return capacity; 
        else return cMax + 1; 
    }

    /**
        The single slice operation (slice-all) which is supported by the tree. Returns all elements in a new array.
        A convinience method. Uses exportTree with the boundaries set to the default ("()")
    */ 
    size_t[] opSlice() const { return exportTree(); }

    /// Makes a deep copy of the current object. 
    VEBtree dup() const
    {
        auto retVal = new VEBtree(expectedSize); 
     
        if(this.length == 0) return retVal; 
     
        auto curr = this.min; 
        do
        {
            retVal.insert(curr.get);
            curr = successor(curr.get); 
        }while(!curr.isNull);
     
        return retVal;
    }

    /**
        this method serves as export of the tree to an array. () and [] is possible as template parameter to export the
        boundaries, even if they are not present.
    */
    auto exportTree(alias boundaries = "()")() const
    {
        size_t[] retArray;
        auto exportLength = this.length; 

        static if(boundaries[0] == '[') 
            if(!(0 in this)) // if zero is not in the tree and we want to include the left boundary, the export grows
                ++exportLength; 
        static if(boundaries[1] == ']')
            ++exportLength; // we want to include the capacity as value, so the export grows 
        
        if(exportLength == 0) return retArray; 
        else retArray.length = exportLength;

        static if(boundaries[0] == '[') retArray[0] = 0; 
        else if(!this.empty) retArray[0] = this.min;
        
        static if(boundaries[1] == ']') retArray[$-1] = capacity; 
        else if(!this.empty) retArray[$-1] = this.max;

        for(size_t i = 1; i < retArray.length; ++i)
        {
            const auto succ = successor!boundaries(retArray[i-1]); 
            if(succ.isNull || succ == capacity) break; 
            retArray[i] = succ; 
        }

        return retArray; 
    }
    // (optional) todo: implement some kind of cool output as a graphViz pic, similiar to the graphs in Cormen. 
}

///
unittest
{
    VEBtree vT = new VEBtree(100); 
    assert(vT.empty);
    const auto result = vT.insert(2); 
    assert(result); 
    assert(!vT.empty); 
    assert(2 in vT);     
    
    VEBtree vT2 = vT.save(); 
    auto const vT3 = vT.dup(); 
    assert(2 in vT2); 
    const result2 = vT2.insert(3); 
    assert(result2); 
    assert(3 in vT2); 
    assert(3 in vT);
    assert(!(3 in vT3));
    assert(vT2.length == 2);
    
}

///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: vT, exportTree.   "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator

    const auto M = uniform(2U,testedSize, rndGenInUse); //set universe size to some integer. 
    VEBtree vT = new VEBtree(M); //create the tree
    vT.fill(1000, rndGenInUse); 

    //assert(vT.exportTree == vT[]);
    assert(vT.exportTree!"[)".front == 0); 
    assert(vT.exportTree!"(]".back == vT.capacity); 
}
///
unittest
{
    assert(!__traits(compiles,  VEBtree())); 
    VEBtree vT = new VEBtree(1000); 
    assert(vT.capacity == 1024); 
    assert(vT.min.isNull); 
    assert(vT.insert(2)); 
    vT.insert(5);
    assert(!(8 in vT)); 
    assert(vT.insert(88));
    assert(88 in vT); 
    assert(vT.predecessor(4) == 2);
    assert(!(8 in vT)); 
    assert(vT.insert(8)); 
    assert(8 in vT); 
    assert(vT.predecessor(75) == 8); 
    assert(vT.predecessor(90) == 88); 
    assert(vT.predecessor(7) == 5); 
    assert(vT.predecessor(4) == 2); 
    assert(vT.predecessor(2).isNull); 
    assert(vT.predecessor!"[]"(2) == 0); 
    assert(vT.successor(6) == 8); 
    assert(vT.successor(5) == 8); 
    assert(vT.successor(4) == 5); 
    assert(vT.successor(1) == 2); 
    assert(vT.successor(75) == 88); 
    assert(vT.successor(90).isNull); 
    assert(vT.successor!"[]"(90) == vT.capacity);
    assert(!(1029 in vT)); 
    assert(vT.successor(1025).isNull);
    assert(vT.successor!"[]"(1025).isNull);
    
    auto vT2 = new VEBtree(500); 
    assert(vT2.empty); 
    vT2.insert(50); 
    vT2.insert(500); 
    assert(vT2.max == 500); 
    assert(vT2.min == 50); 
    assert(vT2.successor(40) == 50);
    assert(vT2.successor(50) == 500); 
    
    vT2 = new VEBtree(500); 
    assert(vT2.empty); 
    vT2.insert(50); 
    vT2.insert(500); 
    assert(vT2.max == 500); 
    assert(vT2.min == 50); 
    assert(vT2.successor(40) == 50);
    assert(vT2.successor(50) == 500); 

    /* about 20 seconds in debug mode. 
    auto vT3 = new VEBtree(uint.max);
    assert(vT3.insert(5)); 
    assert(vT3.member(5));
    assert(vT3.capacity == cast(ulong)uint.max + 1);
    //*/
    
    assert(!(1029 in vT)); 
    assert(!(865 in vT)); 
    assert(vT.insert(865)); 
    assert(865 in vT); 
    assert(!vT.insert(865)); 
    assert(865 in vT); 
    assert(!(866 in vT)); 
    assert(!vT.remove(866)); 
    assert(865 in vT); 
    assert(vT.remove(865)); 
    assert(!(865 in vT)); 
}

///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: rand, succ.       "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator

    const auto M = uniform(2U,testedSize, rndGenInUse); //set universe size to some integer. 
    VEBtree vT = new VEBtree(M); //create the tree
    assert(vT.capacity == nextPow2(M-1)); 
    const auto m = vT.fill(40, rndGenInUse); //(try to) fill the tree with thousend values 
    size_t n; 
    Nullable!(size_t, maxSizeBound) i = vT.max; 

    // discover the thousend (or little less) values with the predecessor method
    while(!i.isNull)
    {
        ++n;
        i = vT.predecessor(i); 
        if(n > m) break; 
    }
    
    size_t o;
    i = vT.min; 
    while(!i.isNull)
    {
        ++o; 
        i = vT.successor(i.get);
        if(o - 1 > m) break; 
    }
    
    // assert, that all members are discovered, iff when no predecessors are left
    assert(n == m); 
    assert(o == m); 
}

///
unittest
{
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, pred        "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 
    vT.fill(1000, rndGenInUse); //fill the tree with some values 
    Nullable!(size_t, maxSizeBound) i = vT.max; 

    // remove all members beginning from the maximum
    bool result; 
    while(!i.isNull)
    {
        result = vT.remove(i); 
        assert(result); 
        const auto j = vT.predecessor(i); 
        if(!j.isNull)
            assert(j != i); 
        i = j; 
    }
    
    // assert, that all members are removed, iff when no predecessors are left. 
    assert(vT.empty); 
}

///
unittest
{
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, remove      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 
    vT.fill(1000, rndGenInUse); //fill the tree with some values 
    Nullable!(size_t, maxSizeBound) i = vT.min;
    
    // remove all members beginning from the minimum
    bool result; 
    while(!i.isNull)
    {        
        result = vT.remove(i); 
        assert(result); 
        const auto j = vT.successor(i); 
        if(!j.isNull)
            assert(j != i); 
        i = j; 
    } 

    // assert, that all members are removed, iff when no successors are left.
    assert(vT.empty); 
}

///
unittest
{
    const uint M = testedSize; 
    VEBtree vT = new VEBtree(M); 
    vT.insert(0x000f); 
    assert(vT.predecessor(0x000f).isNull);
    vT.insert(0x00f0);
    assert(vT.predecessor(0x00f0) == 0x000f); 
    vT.insert(0x0f00); 
    assert(vT.predecessor(0x0f00) == 0x00f0); 
    vT.insert(0xf000); 
    assert(vT.predecessor(0xf000) == 0x0f00);
    
    auto result = vT.remove(0xf000); 
    assert(result); 
    assert(vT.predecessor(0xf000) == 0x0f00);
    result = vT.remove(0x0f00); 
    assert(result); 
    assert(vT.predecessor(0x0f00) == 0x00f0); 
    result = vT.remove(0x00f0); 
    assert(result); 
    assert(vT.predecessor(0x00f0) == 0x000f); 
    result = vT.remove(0x000f); 
    assert(result); 
    assert(vT.predecessor(0x000f).isNull);
}

///
unittest
{
    const uint M = testedSize; 
    VEBtree vT = new VEBtree(M); 
    vT.insert(0xf000); 
    assert(0xf000 in vT); 
    vT.insert(0x0f00); 
    assert(0x0f00 in vT); 
    vT.insert(0x00f0);
    assert(0x00f0 in vT);
    vT.insert(0x000f); 
    assert(0x000f in vT); 
    
    auto result = vT.remove(0xf000); 
    assert(result); 
    assert(!(0xf000 in vT)); 
    result = vT.remove(0x0f00); 
    assert(result); 
    assert(!(0x0f00 in vT)); 
    result = vT.remove(0x00f0); 
    assert(result); 
    assert(!(0x00f0 in vT)); 
    result = vT.remove(0x000f); 
    assert(result); 
    assert(!(0x000f in vT)); 
}

/// 
unittest
{
    //stress test
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, stress      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    // last test says: see below. 
    const auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 
    size_t[] arr; 
    const auto howMuchFilled = vT.fill(arr, rndGenInUse); 

    assert(arr.length == howMuchFilled); 
    
    VEBtree vT2 = new VEBtree(M); 
    
    assert(vT2.capacity == vT.capacity); 
    
    auto rbt = redBlackTree!size_t(0); 
    rbt.clear; 
    
    void fill1()
    {
        foreach(size_t i; arr)
        {
            vT2.insert(i); 
        }
        
        foreach(size_t i; arr)
        {
            vT2.remove(i); 
        }
        assert(vT2.empty);
        
    }
    
    void fill2()
    {
        foreach(size_t i; arr)
        {
            rbt.insert(i); 
        }
    }
    
    /*
        this part is for speed test
    */
    /*
        compiled with ldc2 vebtree.d -O -main -unittest
        results of stress tests: 
            size of tree: 16777216
            howMuchFilled: 16252928
            VEB: 2 secs, 382 ms, 588 μs, and 8 hnsecs
    */
    /*
    import std.stdio; 

    writeln("size of tree: ", vT2.capacity); 
    writeln("howMuchFilled: ", howMuchFilled);
    //auto r = benchmark!(fill1, fill2)(1); 
    auto r = benchmark!(fill1)(1); 
    
    auto f0Result = to!Duration(r[0]); 
    //auto f1Result = to!Duration(r[1]); 
    writeln("VEB: ", f0Result); //10ms
    //writeln("rbt: ", f1Result); //40sec
    //assert(f0Result < f1Result); 
    //*/
}

///
unittest
{
    const uint currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, member      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const uint M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer.
    uint[] sourceArr; 
    sourceArr.length = M; 
    // generate a random array as the source for the tree
    for(uint i; i < M; i++) sourceArr[i] = uniform(0U, M, rndGenInUse); 
    // constructor to test
    VEBtree vT = new VEBtree(sourceArr); 
    // make the array values unique. 
    auto uniqueArr = sort(sourceArr).uniq;
    // check, that all values are filled 
    bool result; 
    foreach(uint i; uniqueArr)
    {
        assert(i in vT); 
        result = vT.remove(i); 
        assert(result); 
    }
    // check, that no other elements are present. 
    assert(vT.empty); 
}

///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: rand, opSlice     "); writeln("seed: ", currentSeed);}  
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    const auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 

    size_t[] arr; 
    vT.fill(arr, rndGenInUse, 16); 
    //assert(setSymmetricDifference(vT[], sort(arr)).empty); 
}

///
unittest
{
    assert(isBidirectionalRange!VEBtree); 
    assert(isRandomAccessRange!VEBtree); 
}

///
unittest
{
    VEBtree vT = new VEBtree(14);
    auto result = vT.insert(2); 
    assert(result); 
    result = vT.insert(5); 
    assert(result);
    result = vT.insert(10); 
    assert(result);
    //assert(vT[] == [2, 5, 10]); 
}

///
unittest
{
    /*
    //another stress test
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: stress test 2  "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    
    void fill16(){ VEBtree vT = new VEBtree(1 << 16); }
    void fill17(){ VEBtree vT = new VEBtree(1 << 17); }
    void fill18(){ VEBtree vT = new VEBtree(1 << 18); }
    void fill19(){ VEBtree vT = new VEBtree(1 << 19); }    
    void fill20(){ VEBtree vT = new VEBtree(1 << 20); }
    void fill21(){ VEBtree vT = new VEBtree(1 << 21); }
    void fill22(){ VEBtree vT = new VEBtree(1 << 22); }
    void fill23(){ VEBtree vT = new VEBtree(1 << 23); }
    void fill24(){ VEBtree vT = new VEBtree(1 << 24); }
    void fill25(){ VEBtree vT = new VEBtree(1 << 25); }
    void fill26(){ VEBtree vT = new VEBtree(1 << 26); }
    void fill27(){ VEBtree vT = new VEBtree(1 << 27); }
    void fill28(){ VEBtree vT = new VEBtree(1 << 28); }
    void fill29(){ VEBtree vT = new VEBtree(1 << 29); }
    void fill30(){ VEBtree vT = new VEBtree(1 << 30); }
    
    import std.stdio; 
    auto r = benchmark!(fill16, fill17, fill18, fill19, fill20, fill21, fill22, fill23, fill24, fill25, fill26, fill27,
        fill28, fill29, fill30)(1);
    //auto r = benchmark!(fill1)(1); 
    auto f16Result = to!Duration(r[0]); 
    auto f17Result = to!Duration(r[1]); 
    auto f18Result = to!Duration(r[2]); 
    auto f19Result = to!Duration(r[3]); 
    auto f20Result = to!Duration(r[4]);
    auto f21Result = to!Duration(r[5]);
    auto f22Result = to!Duration(r[6]);
    auto f23Result = to!Duration(r[7]);
    auto f24Result = to!Duration(r[8]);
    auto f25Result = to!Duration(r[9]);
    auto f26Result = to!Duration(r[10]);
    auto f27Result = to!Duration(r[11]);
    auto f28Result = to!Duration(r[12]);
    auto f29Result = to!Duration(r[13]);
    auto f30Result = to!Duration(r[14]);
    
    writeln("VEB with M of ", 1 << 16, ": ", f16Result); 
    writeln("VEB with M of ", 1 << 17, ": ", f17Result);
    writeln("VEB with M of ", 1 << 18, ": ", f18Result);
    writeln("VEB with M of ", 1 << 19, ": ", f19Result);
    writeln("VEB with M of ", 1 << 20, ": ", f20Result);
    writeln("VEB with M of ", 1 << 21, ": ", f21Result);
    writeln("VEB with M of ", 1 << 22, ": ", f22Result);
    writeln("VEB with M of ", 1 << 23, ": ", f23Result);
    writeln("VEB with M of ", 1 << 24, ": ", f24Result);
    writeln("VEB with M of ", 1 << 25, ": ", f25Result); 
    writeln("VEB with M of ", 1 << 26, ": ", f26Result); 
    writeln("VEB with M of ", 1 << 27, ": ", f27Result); 
    writeln("VEB with M of ", 1 << 28, ": ", f28Result); 
    writeln("VEB with M of ", 1 << 29, ": ", f29Result); 
    writeln("VEB with M of ", 1 << 30, ": ", f30Result); 
    //*/
    
}

/// 
unittest
{
    // This unittest is for check of adding of big numbers
    /* in debug mode about 1 min. 
    const uint[] arr = [1, 2, 8, 2_147_483_647]; 
    new VEBtree(arr); 
    //*/
}

///
unittest
{
    import std.algorithm : sort, uniq; 
    //stress test
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, ranges      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    // last test says: see below. 
    const auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    auto const vT = new VEBtree(M); 
    /*testing the range methods*/
    assert(vT.empty); 
    
    uint[] sourceArr; 
    sourceArr.length = uniform(2U, M, rndGenInUse); 
    for(uint i; i < sourceArr.length; i++)
        sourceArr[i] = uniform(0U, M, rndGenInUse); 

    sort(sourceArr); 
    const auto uniqueArr = sourceArr.uniq.array; 

    // constructor to test

    auto vTnew = new VEBtree(sourceArr); 
    assert(!vTnew.empty); 
    assert(vTnew.length == uniqueArr.length); 
    const auto vT2 = vTnew.save; 
    assert(vTnew.array == uniqueArr); 
    assert(!vTnew.empty);
    assert(!vT2.empty);
    assert(vT2[] == uniqueArr); 

    /* Works. Duration in debug mode: about 35 seconds. 
    auto vTT = new VEBtree(maxSizeBound - 1); 
    assert(vTT.insert(42)); 
    //*/
}
