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
import std.traits; 

version(unittest)
{ 
    import std.stdio; 
    import std.range; 
    import std.algorithm; // iteration, setops, sorting and searching is used in unittest
    import std.random; 
    import std.datetime; 
    import std.conv : to;
    import std.container; // red black tree may be used in unittests for comparison.
    size_t[] powersOfTwo = iota(0, 8 * size_t.sizeof).map!(a => size_t(1) << a).array; 
    Random rndGenInUse; 


    void bin(ulong n)
    {
        import std.stdio : writeln; 
        /* step 1 */
        if (n > 1) bin(n/2);
        /* step 2 */
        write(n % 2);
    }
    enum testedSize = 1 << 3 * size_t.sizeof;
    enum allowedArraySize = 1 << (2 * size_t.sizeof + size_t.sizeof/2); // choosed arbitrary, to avoid seg. faults

    //
    auto elementCount(VEBtree vT){ return vT[].length; }

    auto fill(VEBtree vT, size_t m, Random rndGenInUse)
    {
        size_t n; 
        for(size_t i = 0; i < m; ++i)
        {
            auto x = uniform(0, vT.expectedSize, rndGenInUse);
            // the check for membership is done to add only on inserting to the counter, not just 
            // because visiting the the loop
            if(!vT.member(x))
            {
                vT.insert(x); 
                ++n; 
            }
        }
        return n; 
    }
        
    auto fill(VEBtree vT, ref size_t[] arr, Random rndGenInUse, size_t fillPercentage = 31)
    {
        size_t n; 
        while(n != fillPercentage * vT.capacity/32)
        {
            auto x = uniform(0, vT.capacity - 1, rndGenInUse);
            // the check for membership is done to add only on inserting to the counter, not just 
            // because visiting the the loop
            if(!vT.member(x))
            {
                vT.insert(x); 
                arr ~= x; 
                ++n; 
            }
        
        }
        assert(n == fillPercentage*vT.capacity/32); 
        return n; 
    }

    VEBtree fill(size_t M, Random rndGenInUse)
    {
        VEBtree vT = new VEBtree(M); 
        for(auto i = 0; i < 1000; i++)
        {
            auto x = uniform(0U, vT.expectedSize, rndGenInUse); 
            auto result = vT.insert(x); 
        }
        return vT; 
    }
}

/**
    the baseSize defines the cutoff limit, where the node goes into the bit array mode. It is parametrized on the size
    of size_t and changes dynamically with the architecture used. 
*/
enum baseSize = 8 * size_t.sizeof; 
/**
    the maxSize defines the maximum the tree can be constructed with. It is parametrized on the size of size_t and
    changes dynamically with the architecture used. 
*/
enum maxSize = size_t(1) << baseSize/2; 

/// Convinience function to return the ceiling to the next power of two of the given input. 
@nogc size_t nPof2(size_t value)
in
{
    assert(value != 0); 
    assert(bsr(value) < baseSize - 1); 
}
body { return size_t(1) << (bsr(value) + 1); }
///
unittest
{
    const size_t currentSeed = unpredictableSeed();
    write("UT: nPof2.            "); writeln("seed: ", currentSeed); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    
    const auto pOfM = nPof2(M); 
    assert((pOfM & (pOfM-1)) == 0); 
    const auto check = powersOfTwo.until(nPof2(M), OpenRight.no).array; 
    assert(M < check[$-1]); 
    assert(M > check[$-2]);
}

/**
    This function returns the upper square root of the given input as integer. It is needed in the initialization step 
    of the VEB tree to calculate the number of children of a given layer. The upper square root is defined by 2^{\lceil
    (\lg u)/2\rceil}
*/
size_t hSR(size_t value) 
{
    auto msb = bsr(value); 
    /*
    writeln("value: ", value);
    writeln("msb: ", msb);
    writeln("msb/2: ", msb/2);
    writeln("msb & 1: ", msb & 1); 
    writeln("value != 0: ", value != 0); 
    writeln("value & (value - 1): ", value & (value - 1)); 
    writeln("(msb/2 + ((msb & 1) || ((value != 0) && (value & (value - 1))))): ", (msb/2 + ((msb & 1) || ((value != 0) && (value & (value - 1))))));
    writeln(size_t(1) << (msb/2 + ((msb & 1) || ((value != 0) && (value & (value - 1))))));
    */
    return size_t(1) << (msb/2 + ((msb & 1) || ((value != 0) && (value & (value - 1))))); 
    //return 1 << (msb/2 + (value > (1 << msb) || (msb & 1)));
}

///
unittest
{
    const size_t currentSeed = unpredictableSeed();
    write("UT: hSR.              "); writeln("seed: ", currentSeed); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    auto hSR = hSR(M); 

    assert((hSR & (hSR - 1)) == 0); 
    if(hSR < uint.max)
    {
        import std.math; 
        import std.conv; 
        /*
        writeln("M: ", M); 
        writeln("hSR: ", hSR);
        writeln("hSR²: ", hSR * hSR); 
        writeln("sqrt M: ", sqrt(to!float(M)));
        */
        assert(hSR >= sqrt(to!float(M)));
    } 
    const auto check = powersOfTwo.until(hSR).array; 
    assert((check[$-1]) * (check[$-1]) < M); 
}

/**
    This function returns the lower square root of the given input as integer. It is needed by the indexing functions
    high(x), low(x) and index(x,y) of elements in the tree. The lower square root is defined by 2^{\lfloor(\lg
    u)/2\rfloor}
*/
@nogc size_t lSR(size_t value) { return size_t(1) << (bsr(value)/2); }

///
unittest
{
    const size_t currentSeed = unpredictableSeed();
    write("UT: lSR.              "); writeln("seed: ", currentSeed); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    auto lSR = lSR(M); 
    //writeln(powersOfTwo);
    //writeln("lSR: ", lSR); 
    assert((lSR & (lSR - 1)) == 0); 
    assert(lSR * lSR < M);
    const auto check = powersOfTwo.find(lSR).array; 
    //writeln("check[1]: ", check[1]); 
    //writeln("lSR: ", lSR); 
    //writeln("check[1]: ", check[1]);
    //writeln("M: ", M);
    import std.math; 
    import std.conv; 
    if(lSR < size_t.max/2) assert((check[1]) > sqrt(to!float(M))); 
}

/*
This is an index function defined as \lfloor x/lSR(u)\rfloor. It is needed to find the appropriate cluster
of a element in the tree. 
*/
private @nogc size_t high(size_t value, size_t uS) { return value >> (bsr(uS) / 2); }

//
unittest
{
    const size_t currentSeed = unpredictableSeed();
    write("UT: high.             "); writeln("seed: ", currentSeed); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    const size_t U = nPof2(M); 
    const size_t x = uniform(0U, U, rndGenInUse); 

    assert(high(x,U) == x / lSR(U)); 
}

/*
This is an index function defined as fmod(value, lSR(uS)). It is needed to find the appropriate
value inside a cluster. 
*/
private @nogc size_t low(size_t value, size_t uS) { return value & ((size_t(1) << (bsr(uS) / 2)) - 1); }

//
unittest
{
    const size_t currentSeed = unpredictableSeed();
    write("UT: low.              "); writeln("seed: ", currentSeed); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    const size_t U = nPof2(M); 
    const size_t x = uniform(0U, U, rndGenInUse); 

    assert(low(x, U) == (x & (lSR(U) - 1)));
}

/*
This is an index function to retain the searched value. It is defined as x * lSR(u) + y. Beyond this, the
relation holds: x = index(high(x), low(x))
*/
private @nogc size_t index(size_t uS, size_t x, size_t y){ return (x * lSR(uS) + y); }

//
unittest
{
    const size_t currentSeed = unpredictableSeed();
    write("UT: index.            "); writeln("seed: ", currentSeed); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    const size_t M = uniform(0U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    //writeln("M: ", M);
    const size_t U = nPof2(M); 
    const size_t x = uniform(0U, U, rndGenInUse); 
    
    assert(index(U, high(x, U), low(x, U)) == x); 
}

/**
This is the struct to represent a VEB tree node. As memebers it contains the uS, the min and the max value as
well as a link to a summary node and a cluster, which is a range of VEB tree nodes of size hSR(u). Each
child node has a universe size of lSR(u)
*/
private struct VEBnode
{
    /*
        This pointer acts as an array to nodes like this one. As the universe size is not provided, the length of the
        array can not be used to calculate the most of operations, so no explicit array is needed. The only remaining
        property is whether the pointer is set at all. From this property the node can decide, whether it is a leaf or
        an intermediate node. 
    */
    VEBnode* ptrArr; // the first member behaves different, as the others, as it is the summary node. 
    @property ref VEBnode summary()
    in { assert(!isLeaf); }
    body { return ptrArr[0]; }
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        write("UT: vN, summary.      "); writeln("seed: ", currentSeed); 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        auto value = uniform!"[]"(0U,testedSize, rndGenInUse);
        VEBnode vN = VEBnode(512); 
        assert(!vN.isLeaf); 
        vN.ptrArr[0]._val = 73; 
        assert(vN.summary._val == 73);
    }
    
    @property VEBnode* cluster()
    in { assert(!isLeaf); }
    body { return (ptrArr + 1); }
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        write("UT: vN, cluster.      "); writeln("seed: ", currentSeed); 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        const auto value = uniform!"[]"(0U, testedSize, rndGenInUse);
        const auto place = uniform(0U,baseSize, rndGenInUse);
        /*
        writeln("value: ", value); 
        writeln("place: ", place); 
        */
        VEBnode vN = VEBnode(4096); 
        vN.ptrArr[place]._val = value; 
        assert(vN.ptrArr[place]._val == value); 
        assert(vN.cluster[place - 1]._val == value); // the right place: it is the (place - 1) location of clusters
        vN.cluster[place]._val = 73; 
    }
    
    /*
        This is an unnamed union. It defines the essential behavior of the node. It is either a real node with a min and
        a max, or it is a ulong which is handled as a bit array. 
    */ 
    union 
    {
        size_t _val;  // ulong is known to be 64-bit. 
        mixin(bitfields!(
            size_t, "_min", baseSize/2, // the default value of the min is greater then the max. 
            size_t, "_max", baseSize/2
        ));
    }

    @disable this(); 
    this(size_t uS)
    {
        if(uS > baseSize)
        {
            VEBnode[] tmp; 
            tmp.reserve(hSR(uS) + 1);
            tmp ~= VEBnode(hSR(uS)); 
            for(size_t i = 1; i <= hSR(uS); ++i)
                tmp ~= VEBnode(lSR(uS)); 
            ptrArr = tmp.ptr; 
            nullify;
        }
    }
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        write("UT: vN, __ctor.       "); writeln("seed: ", currentSeed); 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        const auto uS = uniform!"[]"(0U, testedSize, rndGenInUse);
        const auto place = uniform(0U,baseSize, rndGenInUse);
        /*
        writeln("value: ", value); 
        writeln("place: ", place); 
        */
        VEBnode vN = VEBnode(uS);
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

    @nogc @property bool isLeaf() { return ptrArr == null; }
    
    @nogc @property bool isNull() { return isLeaf ? (_val == 0) : (_min > _max); }

    @nogc @property void nullify() { _val = isLeaf ? 0 : 1; }  

    @property Nullable!(size_t, maxSize) min()
    {
        // define the result as a nullable 
        Nullable!(size_t, maxSize) retVal; 
        /*
            we have only a chance to get a value, if a value is present.
            if it is a leaf, handle the val as a bit array and find the first bit set from the right. 
            if it is not a leaf, get the minimum. 
        */ 
        if(!isNull) retVal = isLeaf ? bsf(_val) : _min; 
        // return the result, even if it was not set to a value. 
        return retVal;  
    }

    @property void min(size_t value)
    {
        if(isLeaf)
        {
            assert(min > value);
            insert(value); 
        }
        else
        {
            // the passed value should not exceed the allowed size of a size/2
            assert(value < maxSize); 
            _min = value; 
        }
    }

    @property Nullable!(size_t, maxSize) max()
    {
        // define the result as a nullable
        Nullable!(size_t, maxSize) retVal; 
        /*
            we have only a chance to get a value, if a value is present. 
            if it is a leaf, handle the val as a bit array and find the first bit set from the left. 
            if it is not a leaf, get the max. 
        */
        if(!isNull) retVal = isLeaf ? bsr(_val) : _max; 
        // return the result, even if it was not set to a value. 
        return retVal;  
    }

    @property void max(size_t value)
    {
        if(isLeaf) 
        {
            assert(max < value); 
            insert(value); 
        }
        else
        {
            // the passed value should not exceed the allowed size of a size/2
            assert(value < maxSize); 
            _max = value; 
        }
    }

    bool member(size_t bitnum)
    in
    {
        // method inside the node defined on leafs only. 
        assert(isLeaf); 
        // when a bitnum is passed to the leaf, then, it is an index to the bitarray and has to be in proper range
        assert(bitnum < baseSize);
    }
    body { return bt(&_val, bitnum) != 0; }
    
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        write("UT: vN, member.       "); writeln("seed: ", currentSeed); 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        const auto value = uniform(0U,size_t.max, rndGenInUse);
        const auto bitNum = uniform(0U,baseSize, rndGenInUse);
        VEBnode vN = VEBnode(baseSize); 
        vN._val = value; 
        /*
        writeln(value); 
        bin(value); 
        writeln(); 
        writeln(size_t(1) << bitNum); 
        writeln("hu? : ", vN.member(bitNum) ); 
        writeln("hu2: ", vN._val & size_t(1) << bitNum);
        */
        if((vN._val & size_t(1) << bitNum) != 0 ) assert(vN.member(bitNum)); 
        if((vN._val & size_t(1) << bitNum) == 0 ) assert(!vN.member(bitNum)); 
    }
    
    bool insert(size_t bitnum)
    in
    {
        // method inside the node defined on leafs only. 
        assert(isLeaf); 
        // when a bitnum is passed to the leaf, then, it is an index to the bitarray and has to be in proper range
        assert(bitnum < baseSize);
    }
    body { return bts(&_val, bitnum) == 0; }

    bool remove(size_t bitnum)
    in
    {
        assert(isLeaf); 
        assert(bitnum < baseSize); 
    }
    body { return btr(&_val, bitnum) != 0; }

    Nullable!(size_t, maxSize) predecessor(size_t bitNum)
    in
    {
        assert(isLeaf); 
        assert(bitNum < baseSize); 
    }
    body
    {
        Nullable!(size_t, maxSize) retVal; 
        
        if(!isNull && (bitNum != 0))
        {
            auto maskedVal = _val & ((size_t(1) << bitNum) - 1); 
            if(maskedVal != 0)
                retVal = bsr(maskedVal);
        }
        return retVal; 
    }
    
    unittest
    {
        const size_t currentSeed = unpredictableSeed(); //2471218309
        write("UT: vN, predecessor.  "); writeln("seed: ", currentSeed); 
        rndGenInUse.seed(currentSeed); //initialize the random generator
        const size_t v = uniform(0U, size_t.max, rndGenInUse); //set universe size to some integer. 
        const size_t x = uniform(0U, baseSize, rndGenInUse);
        VEBnode vN = VEBnode(baseSize); 
        vN._val = v; 
        /*
        writeln("v: ", v); 
        writeln("x: ", x); 
        write("bin(v): ");  bin(v); writeln();
        */
        bool found; 

        //writeln("vN.predecessor(x): ", x, " --> ", vN.predecessor(x)); 
        for (size_t index = x - 1; index >= 0; --index)
        {
            //writeln(index); 
            if (v & (size_t(1) << index)) 
            {
                /*
                writeln("v & (1 << index): ", v & (size_t(1) << index)); 
                writeln("1 << index: ", size_t(1) << index);
                writeln("index: ", index); 
                */
                found = true; 
                assert(!vN.isNull);
                assert(vN.predecessor(x) == index); 
                break; 
            }
        }

        if(!found) assert(vN.predecessor(x).isNull); 
    }
    

    Nullable!(size_t, maxSize) successor(size_t bitNum)
    in
    {
        assert(isLeaf); 
        assert(bitNum < baseSize); 
    }
    body
    {
        Nullable!(size_t, maxSize) retVal; 
        
        if(!isNull && (bitNum + 1 < baseSize)) 
        {
            auto maskedVal = _val & ~((size_t(1) << (bitNum + 1)) - 1); 
            if(maskedVal != 0)
                retVal = bsf(maskedVal);
        }
        return retVal; 
    }
    
    unittest
    {
        const size_t currentSeed = unpredictableSeed();
        write("UT: vN, successor.    "); writeln("seed: ", currentSeed); 
        rndGenInUse.seed(currentSeed); //initialize the random generator
        const size_t v = uniform(0U, size_t.max, rndGenInUse); //set universe size to some integer. 
        const size_t x = uniform(0U, baseSize, rndGenInUse);
        VEBnode vN = VEBnode(baseSize); 
        vN._val = v; 
        /*
        writeln("v: ", v); 
        writeln("x: ", x); 
        write("bin(v): ");  bin(v); writeln();
        */
        bool found; 

        //writeln("vN.successor(x): ", x, " --> ", vN.successor(x)); 
        //writeln("1 << bsr(x): ", size_t(1) << bsr(x));
        for (size_t index = x + 1; index < baseSize; ++index)
        {
            //writeln(index); 
            if (v & (size_t(1) << index)) 
            {
                /*
                writeln("v & (1 << index): ", v & (size_t(1) << index)); 
                writeln("1 << index: ", size_t(1) << index);
                writeln("index: ", index); 
                */
                found = true; 
                assert(vN.successor(x) == index); 
                break; 
            }
        }
        //writeln(vN.successor(x));
        if(!found) assert(vN.successor(x).isNull);
    }
    
}

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
    assert(vN.member(1));
    assert(!vN.member(2));
    //writeln("val: ", vN._val);
    assert(vN.isLeaf);
    assert(vN.ptrArr == null); 
    vN.nullify; 
    //writeln("val: ", vN._val);
    assert(vN.isNull); 
    assert(vN._val == 0); 
}

/**
This struct represents the VEB tree itself. For the sake of convinience it saves the provided at the initialization step
wished maximum element. However at the point of development it is only used for testing. Beyond this, it stores only
the reference to the root element, as the theory tells. The tree implements not only the documented interface of a 
van VEB tree, but is also a bidirectional range. It supports two slice operations and a non-trivial opIndex operator. 
*/
class VEBtree
{
    // the root element of the tree. 
    private VEBnode root; 
    // this member is updated on every insertion and deletion to give the current element count on O(1)
    private size_t _elementCount; 
    /// this member stores the initialization size, as it would be lost forever after initialization, otherwise
    immutable size_t expectedSize; 
    
    /// default constructor of a VEB tree is disabled. 
    @disable this(); 
    
    /// to construct a VEB tree one should provide the maximum element one wish to be able to store. 
    this(size_t value)
    in
    {
        assert(value > 1); 
        // the passed value should be at most one over uint max1
        assert(value <= maxSize);
    }
    body
    {
        //writeln("val: ", value); 
        // set the expected size to the passed value 
        expectedSize = value; 
        //writeln("expectedSize: ", expectedSize); 
        // delegate the creation of the nodes with the apropriate power of two of the needed universe size
        root = VEBnode(nPof2(expectedSize - 1)); 
        assert(root.isNull);
        //writeln("nPof2(expectedSize - 1): ", nPof2(expectedSize - 1));
    }
    
    unittest
    {
        auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
        write("UT: vT, __ctor.       "); writeln("seed: ", currentSeed); 
        rndGenInUse.seed(currentSeed); //initialize the random generator

        auto uS = uniform(1U << size_t(1),testedSize, rndGenInUse);
        VEBtree vT = new VEBtree(uS); 
        assert(vT.root.isNull);
        if((uS & (uS - 1)) == 0)
            assert(vT.capacity == uS); 
        else
            assert(vT.capacity == (size_t(1) << (bsr(uS) + 1))); 
        
        assert(vT.expectedSize == uS); 
        //writeln("uS: ", uS); 
        //writeln("vT.expectedSize: ", vT.expectedSize); 
        const auto uS1 = uniform(1U << size_t(1),testedSize, rndGenInUse);
        const auto uSsmall = uniform(1U << size_t(1),baseSize, rndGenInUse);
        VEBtree vT1 = new VEBtree(uS1); 
        const VEBtree vTsmall = new VEBtree(uSsmall); 

        assert(vTsmall.root._val == 0);
        assert(vTsmall.root.ptrArr == null); 

        if(uS1 > 8 * size_t.sizeof)
        {
            assert(vT1.root._val == 1);
            assert(vT1.root.ptrArr != null); 
            //writeln("vT1.root._val: ", vT1.root._val);
            //check every child for consistency. 
            // the size of a node is higher square root & the summary node. 
            
            // capacity is tested elsewhere. 
            // hSR is also tested elsewhere
            const auto childsAmount_l1 = hSR(vT1.capacity) + 1; 
            const auto childsAmount_l2 = hSR(lSR(vT1.capacity)) > baseSize ? hSR(lSR(vT1.capacity)) + 1 : 0; 
            
            // the tree is just created, assert all children are nullified
            for(size_t i; i < childsAmount_l1; ++i)
            {
                //writeln("i: ", i); 
                assert(vT1.root.ptrArr[i].isNull);
                //writeln("ii: ", i); 
                if(childsAmount_l1 > baseSize + 1)
                {
                    //writeln("iii: ", i); 
                    /*
                    writeln("hey!"); 
                    writeln("childsAmount_l1: ", childsAmount_l1); 
                    writeln("i: ", i); 

                    writeln(); 
                    */
                    for(size_t j; j < childsAmount_l2; ++j)
                    {
                        //writeln("iiii: ", i); 
                        //writeln("j: ", j); 
                        assert(vT1.root.ptrArr[i].ptrArr[j].isNull);
                    }
                }
            }
        }

    }
    
    /// another possibility is to construct a VEB tree by providing an array.
    this(R)(R range) if(isIterable!R)
    in
    {
        // check, whether the range is not too long. I. e. expressable with an uint. 
        assert(range.length < maxSize);
    }
    body
    {
        import std.algorithm.comparison : max;
        //writeln("got array: ", range); 
        
        // first, we have to determine the size of the tree. 
        // it is either derived from the length of the given tree or its greatest element
        size_t limit; 
        foreach(size_t i; range) limit = max(limit,i); 
        // assert no element has exceeded the allowed range of baseSize/2
        assert(limit < maxSize);
        // if the array is longer, then the greatest element, but the length passes, substitute the limit
        limit = max(limit, range.length); 
        // call the constructor with the limit
        //writeln("limit: ", limit); 
        this(limit + 1);
        //writeln("capacity: ", capacity); 
        // put every element from the range into the tree
        foreach(size_t i; range) 
        {
            //writeln("i: ", i);
            insert(i); 
        }
    }
    
    public
    {
        /** 
            this method returns the capacity of the tree. It is equal to the next power of two with regard to the
            maximum element 
        */
        size_t capacity() { return nPof2(expectedSize - 1); }
    
    
        /// this method is used to add an element to the tree. duplicate values will be ignored. 
        bool insert(size_t value)
        {
            const bool retVal = insert(value, root, capacity); 
            if(retVal) ++_elementCount; 
            return retVal; 
        }

        private bool insert(size_t value, ref VEBnode vN, size_t uS)
        {
            if(value >= capacity) return false; 
            import std.algorithm.comparison : min, max;
            //writeln("inserting: ", value);
            if(uS <= baseSize) 
                {
                    //writeln("small insert: ", value); 
                    return vN.insert(value); 
                    //assert(!vN.isNull);
                    //return res; 
                }

            //writeln("stay by me"); 
            if(vN.isNull)
            {
                //writeln("i2: ", value); 
                vN.min = value; 
                vN.max = value; 
                assert(!vN.isNull); 
                return true; 
            }

            assert(!vN.isNull);
            assert(!vN.min.isNull); 
            assert(!vN.max.isNull); 

            if(value == vN.min || value == vN.max) return false; 

            if(vN.min == vN.max)
            {
                //writeln("i3: ", value);
                vN.min = min(vN.min, value); 
                vN.max = max(vN.max, value); 
                return true; 
            }

            //writeln("kk inserting: ", value);
            //writeln("kk min ", vN.min); 
            //writeln("kk max ", vN.max); 
            // a swap can not be used here, as min is itself a (property) method 
            if(value < vN.min) {const auto tmp = value; value = vN.min.get; vN.min = tmp; }
            // a swap can not be used here, as max is itself a (property) method 
            if(value > vN.max) {const auto tmp = value; value = vN.max.get; vN.max = tmp; }
            //writeln("kk min ", vN.min); 
            //writeln("kk max ", vN.max); 
            //writeln("ll inserting: ", value);
            
            auto nextTreeIndex = high(value, uS); 
            //writeln("nextTreeIndex: ", nextTreeIndex); 
            //writeln("vN.ptrArr[nextTreeIndex].isNull: ", vN.ptrArr[nextTreeIndex].isNull);
            if(vN.cluster[nextTreeIndex].isNull)
            {
                //writeln("inserting into summary");
                insert(high(value, uS), vN.summary, hSR(uS));
            } 
                   //writeln("inserting into C:nextTreeIndex, low: ", nextTreeIndex, " ", low(value, uS));
                   //writeln("vN.ptrArr[nextTreeIndex].val: ", vN.ptrArr[nextTreeIndex]._val);
            auto res = insert(low(value, uS), vN.cluster[nextTreeIndex], lSR(uS));
                    //writeln("vN.ptrArr[nextTreeIndex].val: ", vN.ptrArr[nextTreeIndex]._val);
            return res;
        }
        unittest
        {
            auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
            write("UT: vT, insert.       "); writeln("seed: ", currentSeed); 
            rndGenInUse.seed(currentSeed); //initialize the random generator

            auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
            VEBtree vT = new VEBtree(uS); 

            size_t n; 
            uint[allowedArraySize] insertedVals;  
            while(n < allowedArraySize)
            {
                auto valToInsert = uniform(0U, uS, rndGenInUse); 
                bool inserted = vT.insert(valToInsert); 
                if(inserted)
                {
                    insertedVals[n] = valToInsert; 
                    n++;
                }
            }
            assert(vT._elementCount == insertedVals.length); 
            
            sort(insertedVals[]); 
            assert(uniq(insertedVals[]).array.length == insertedVals.length); 
            //writeln(insertedVals); 
            //writeln(insertedVals.count); 
        }
        /// this method overrides the insert method to directly use arrays
        void insert(R)(R arr) if(isIterable!R){ foreach(size_t i; arr) insert(i); }

        /// this method is used to remove elements from the tree. not existing values will be ignored. 
        bool remove(size_t value)
        {
            const bool retVal = remove(value, root, capacity); 
            if(retVal) --_elementCount; 
            return retVal; 
        }

        private bool remove(size_t value, ref VEBnode vN, size_t uS)
        {
            //writeln("remove function begins"); 
            //writeln("uS: ", uS); 

            if(uS <= baseSize) return vN.remove(value);
            if(vN.isNull) return false; 
            if(vN.min == vN.max)
            {
                if(vN.min != value) return false; 
                vN.nullify; 
                return true; 
            }
            if(value == vN.min)
            {
                auto treeOffset = vN.summary.min;
                if(treeOffset.isNull)
                {
                    vN.min = vN.max; 
                    return true; 
                }
                auto min = vN.cluster[treeOffset].min; 
                remove(min, vN.cluster[treeOffset], lSR(uS)); 

                if(vN.cluster[treeOffset].isNull)
                    remove(treeOffset, vN.summary, hSR(uS));

                vN.min = index(uS, treeOffset, min); 
                return true; 
            }
            if(value == vN.max)
            {
                auto treeOffset = vN.summary.max; 
                if(treeOffset.isNull)
                {
                    vN.max = vN.min; 
                    return true; 
                }

                auto max = vN.cluster[treeOffset].max; 
                remove(max, vN.cluster[treeOffset], lSR(uS)); 

                if(vN.cluster[treeOffset].isNull)
                    remove(treeOffset, vN.summary, hSR(uS)); 

                vN.max = index(uS, treeOffset, max); 
                return true; 
            }

            auto treeOffset = high(value, uS); 
            const bool retVal = remove(low(value, uS), vN.cluster[treeOffset], lSR(uS));
            if(vN.cluster[treeOffset].isNull)
                remove(treeOffset, vN.summary, hSR(uS)); 

            return retVal; 
        }
        unittest
        {
            auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
            write("UT: vT, remove.       "); writeln("seed: ", currentSeed); 
            rndGenInUse.seed(currentSeed); //initialize the random generator

            auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
            VEBtree vT = new VEBtree(uS); 

            size_t n; 
            uint[allowedArraySize] insertedVals;  
            
            while(n < allowedArraySize)
            {
                auto valToInsert = uniform(0U, uS, rndGenInUse); 
                bool inserted = vT.insert(valToInsert); 
                if(inserted)
                {
                    insertedVals[n] = valToInsert; 
                    n++; 
                }
            }
            
            assert(vT._elementCount == insertedVals.length); 
            /*
            writeln("n: ", insertedVals.length);
            writeln("uS: ", uS); 
            writeln("capacity: ", vT.capacity); 
            writeln("inserted: ", insertedVals); 
            writeln("vT.root._val: ", vT.root._val); 
            */
            foreach(size_t i; insertedVals)
            {
                //writeln("removing: ", i); 
                bool removed = vT.remove(i); 
                //writeln("removed: ", removed); 
                //writeln("vT.root._val: ", vT.root._val); 
            }
            assert(vT.length == 0); 
        }

        /// this method is used to determine, whether an element is currently present in the tree
        bool member(size_t value) { return member(value, root, capacity); }

        private bool member(size_t value, ref VEBnode vN, size_t uS)
        {
            //writeln("member call, value: ", value); 
            //writeln("member call, uS: ", uS); 
            if(value >= capacity) return false; 
            if(uS <= baseSize) 
                {
                    assert(vN.ptrArr == null);
                    return vN.member(value); 
                }

            if(vN.isNull) return false; 
            if(value == vN.min || value == vN.max) return true; 

            return member(low(value, uS), vN.cluster[high(value, uS)], 
                lSR(uS)); 
        }
        
        unittest
        {
            auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
            write("UT: vT, member.       "); writeln("seed: ", currentSeed); 
            rndGenInUse.seed(currentSeed); //initialize the random generator
             
            auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
            VEBtree vT = new VEBtree(uS); 

            size_t n; 
            uint[allowedArraySize] insertedVals;  
            while(n < allowedArraySize)
            {
                auto valToInsert = uniform(0U, uS, rndGenInUse); 
                bool inserted = vT.insert(valToInsert); 
                if(inserted)
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
                        assert(vT.member(i));
                    }
                else 
                    {
                        assert(!vT.member(i), "i: " ~ to!string(i)); //10481664, 8908800
                    }
            }
        }
        
        /// this method is used to determine the minimum of the tree
        @property Nullable!(size_t, maxSize) min(){ return root.min; }

        /// this method is used to determine the maximum of the tree    
        @property Nullable!(size_t, maxSize) max(){ return root.max; }

        /// this method retrieves the successor of the given input.
        Nullable!(size_t, maxSize) successor(size_t value) { return successor(value, root, capacity); }

        private Nullable!(size_t, maxSize) successor(size_t value, ref VEBnode vN, size_t uS)
        {
            /*
            writeln("got value: ", value); 
            writeln("got uS: ", uS); 
            writeln("baseSize is: ", baseSize); 
            */
            /*
            size_t[] suspiciousValues = [20511]; 
            if(canFind(suspiciousValues, value)) 
                {
                    writeln("got value: ", value); 
                    writeln("uS: ", uS); 
                    write("bin(vN._val) "); bin(vN._val);
                    writeln(); 
                    writeln("vN.min: ", vN.min); 
                    writeln("vN.max: ", vN.max); 
                    writeln("vN.isNull: ", vN.isNull); 
                }
                */
            Nullable!(size_t, maxSize) retVal; 
            if(uS <= baseSize) 
                {
                    /*
                    if(canFind(suspiciousValues, value))
                    {
                        writeln("we got: ", value); 
                        writeln("vN.successor(value): ", vN.successor(value)); 
                    }
                    */
                    assert(value < baseSize); 
                    return vN.successor(value); 
                }
            if(vN.isNull) return retVal; 
            if(value < vN.min) return vN.min; 
            if(value >= vN.max) return retVal; 
            //writeln("got past simple cases"); 

//            const auto subTreeIndex = high(value, uS) + 1; 
//            const auto subTreeMax = vN.ptrArr[subTreeIndex].max; 
            /*
            writeln("hhhhhhhhh: ", vN.ptrArr[subTreeIndex].max.isNull);
            writeln("val: ", value); 
            writeln("subTreeIndex: ", subTreeIndex);
            writeln("subTreeMax: ", subTreeMax.isNull);
            writeln("low(value, uS): ", low(value, uS));
            */
//            if(subTreeMax.isNull || low(value, uS) >= subTreeMax)
//            {
                //writeln("we got here");
//                auto nextTree = successor(high(value, uS), vN.ptrArr[0], hSR(uS));
                /*
                writeln("nextTree.isNull: ", nextTree.isNull);
                writeln(vN.ptrArr[nextTree + 1].isNull);
                */
//                if(nextTree.isNull || vN.ptrArr[nextTree + 1].isNull) return vN.max;
                //if(vN.ptrArr[nextTree + 1].isNull) return vN.max; 

//                retVal = index(uS, nextTree, vN.ptrArr[nextTree + 1].min); 
//                return retVal; 
//            }
            //writeln("skipped the if");
//            retVal = index(uS, high(value, uS), successor(low(value,
//                uS), vN.ptrArr[subTreeIndex], hSR(uS)));
/*
            if(canFind(suspiciousValues, value)) 
                {
                    writeln("simple cases passed"); 
                }
*/
            const auto maxlow = vN.cluster[high(value, uS)].max;
            /*
            if(canFind(suspiciousValues, value)) 
                {
                    writeln("maxlow: ", maxlow); 
                    writeln("low(value, uS): ", low(value, uS)); 
                    writeln("high(value, uS): ", high(value, uS)); 
                }
                */
                if(maxlow.isNull || low(value, uS) >= maxlow)
                {
                    /*
                    if(canFind(suspiciousValues, value)) 
                    {
                        writeln("if 1"); 
                        writeln("maxlow: ", maxlow); 
                        writeln("low(value, uS): ", low(value, uS)); 
                        writeln("high(value, uS): ", high(value, uS)); 
                        write("vN.summary._val: "); bin(vN.summary._val); 
                        writeln(); 
                    }*/
                    auto nextTree = successor(high(value, uS), vN.summary, hSR(uS)); 
                    if(nextTree.isNull) return vN.max; 
                    retVal = index(uS, nextTree, vN.cluster[nextTree].min); 
                }
                else
                {
                    /*
                    if(canFind(suspiciousValues, value)) 
                    {
                        writeln("if 2"); 
                        writeln("maxlow: ", maxlow); 
                        writeln("low(value, uS): ", low(value, uS)); 
                        writeln("high(value, uS): ", high(value, uS)); 
                    }
                    */
                    auto nextTree = successor(low(value, uS), vN.cluster[high(value, uS)], lSR(uS)); 
                    retVal = index(uS, high(value, uS), nextTree);
                }
                

                /*
                if(!maxlow.isNull && low(value, uS) < maxlow)
                {
                    auto succcluster = successor(low(value, uS), vN.cluster[high(value, uS)], lSR(uS)); 
                    retVal = index(uS, high(value, uS), succcluster); 
                }
                else
                {
                    auto offset = successor(high(value, uS), vN.summary, hSR(uS)); 
                    if(offset.isNull) retVal =  vN.max; 
                    else retVal = index(lSR(uS), offset, vN.cluster[offset].min); 
                }
                */
                /*
            if(!maxlow.isNull && low(value, uS) < maxlow)
                    { //predecessor(low(value, uS), vN.cluster[high(value, uS)], lSR(uS));
                        if(canFind(suspiciousValues, value))
                        {
                            writeln("if 1"); 
                            writeln("low(value, uS): ", low(value, uS)); 
                            writeln("high(value, uS): ", high(value, uS)); 
                            writeln("lSR(uS): ", lSR(uS)); 
                            writeln("sending value from inside (low(value, uS)): ", low(value, uS)); 
                        }
                        auto offset = successor(low(value, uS), vN.cluster[high(value, uS)], lSR(uS));
                        //vN.cluster[high(value, uS)].successor(low(value, uS));
                        if(canFind(suspiciousValues, value)) 
                            {
                                writeln("offset: ", offset); 
                            }
                        
                        retVal = index(uS, high(value, uS), offset); 
                    }
                    else
                    {
                        if(canFind(suspiciousValues, value))
                        {
                            writeln("else 1");
                            writeln("low(value, uS): ", low(value, uS)); 
                            writeln("high(value, uS): ", high(value, uS)); 
                            writeln("lSR(uS): ", lSR(uS)); 
                            writeln("hSR(uS): ", hSR(uS));
                            writeln("sending value from inside (high(value, uS)): ", high(value, uS)); 
                            write("bin of vN.summary val: "); bin(vN.summary._val); 
                            writeln(); 
                            writeln("val of vN.summary: ", vN.summary._val); 
                        }
                        auto succcluster = successor(high(value, uS), vN.summary, hSR(uS)); 
                        if(!succcluster.isNull)
                        {
                            auto offset = vN.cluster[succcluster].min; 
                            retVal = index(uS, succcluster, offset); 
                        }
                    }      
                    */    
            return retVal; 
        }
        unittest
        {
            auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
            write("UT: vT, successor.    "); writeln("seed: ", currentSeed); 
            rndGenInUse.seed(currentSeed); //initialize the random generator
             
            auto uS = uniform(allowedArraySize, testedSize, rndGenInUse);
            VEBtree vT = new VEBtree(uS); 

            size_t n; 
            uint[allowedArraySize] insertedVals;  
            while(n < allowedArraySize)
            {
                auto valToInsert = uniform(0U, uS, rndGenInUse); 
                bool inserted = vT.insert(valToInsert); 
                if(inserted)
                {
                    insertedVals[n] = valToInsert; 
                    n++;
                }
            }
            
            //writeln("size: ", vT.length); 
            auto sortedInserted = assumeSorted(sort(insertedVals[])); 
            //writeln("max: ", vT.max); 
            //writeln("min: ", vT.min); 
            //writeln("back: ", sortedInserted.back); 
            //writeln("front: ", sortedInserted.front); 

            assert(vT.max == sortedInserted.back); 
            assert(vT.min == sortedInserted.front); 
            size_t j; 

            for(size_t i = 0; i <= testedSize; ++i)
            {
                /*
                    if(i == 12292095 || i == 13525034)
                    {
                        writeln("i: ", i); 
                        write("bin i + 1: ", i + 1, " "); bin(i + 1); 
                        writeln(); 
                        write("bin i: ", i, " "); bin(i); 
                        writeln(); 
                        writeln("expected result: ", sortedInserted.lowerBound(i)[$-1]);
                    }
                  */
                   //writeln("sending value: ", i); 
                const auto el = vT.successor(i); 
                //if(i == 32) writeln("el: ", el); 
                    //if(i == 12292095 || i == 13525034) 
                        //writeln("ii: ", i); 
                        /*
                    if(i == 12292095 || i == 13525034)
                    {
                        writeln("elel: ", el); 
                        assert(sortedInserted.contains(el.get)); 
                        writeln(sortedInserted.contains(el.get)); 
                    }
                        */
                
                if(el.isNull)
                {
                    assert(i == vT.max); 
                    assert(sortedInserted.contains(i));
                    break; // quit the loop;
                }
                else
                {
                    //writeln("i: ", i); 
                    //writeln("el: ", el); 
                    if(sortedInserted.contains(i)) ++j; 
                    //if(i == 32) writeln("sortedInserted[j]: ", sortedInserted[j]); 
                    assert(el == sortedInserted[j]); 
                }
            }
            
        }

        /// this method retrieves the predecessor of the given input. 
        Nullable!(size_t, maxSize) predecessor(size_t value) { return predecessor(value, root, capacity); }

        private Nullable!(size_t, maxSize) predecessor(size_t value, ref VEBnode vN, size_t uS)
        {
            /*
            size_t[] suspiciousValues = [13525034, 12292095, 3000, 46, 42]; 
            if(canFind(suspiciousValues, value)) 
                {
                    writeln("got value: ", value); 
                    writeln("uS: ", uS); 
                    write("bin(vN._val) "); bin(vN._val);
                    writeln(); 
                    writeln("vN.min: ", vN.min); 
                    writeln("vN.max: ", vN.max); 
                }
            */
            Nullable!(size_t, maxSize) retVal; 
            //writeln("value: ", value);
            //writeln("uS: ", uS);
            if(uS <= baseSize) 
                {
                    //if(canFind(suspiciousValues, value)) writeln("sending value: ", value); 
                    return vN.predecessor(value); 
                }

            //writeln("vN.isNull: ", vN.isNull);
            if(vN.isNull) return retVal; 
            //writeln("vN.max: ", vN.max);
            if(value > vN.max) return vN.max; 
            //writeln("vN.min: ", vN.min);
            if(value <= vN.min) return retVal; 

            // const auto subTreeIndex = high(value, uS); 
            // const auto subTreeMin = vN.cluster[subTreeIndex].min; 
            /*
            writeln("subTreeIndex: ", subTreeIndex);
            writeln("subTreeMin: ", vN.ptrArr[subTreeIndex].min);
            writeln("low(value, uS): ", low(value, uS));
            */

              // if(subTreeMin.isNull || low(value, uS) <= subTreeMin)
              //{
                /*
                writeln("high(value, uS): ", high(value, uS));
                writeln("vN.ptrArr[0].isNull: ", vN.ptrArr[0].isNull);
                writeln("vN.ptrArr[0].min: ", vN.ptrArr[0].min);
                writeln("vN.ptrArr[0].max: ", vN.ptrArr[0].max);
                writeln("vN.ptrArr[0].ptrArr: ", vN.ptrArr[0].ptrArr);
                writeln("vN.ptrArr[0].isLeaf: ", vN.ptrArr[0].isLeaf);
                writeln("vN.ptrArr[0]._min: ", vN.ptrArr[0]._min);
                writeln("vN.ptrArr[0]._max: ", vN.ptrArr[0]._max);
                writeln("vN.ptrArr[0]._val: ", vN.ptrArr[0]._val);
                writeln("hSR(uS): ", hSR(uS));
                */
                // auto nextTree = predecessor(subTreeIndex, vN.summary, hSR(uS));
                //writeln("nextTree: ", nextTree);
                //if(nextTree.isNull || vN.ptrArr[nextTree + 1].isNull) return vN.max;
                // if(nextTree.isNull || vN.cluster[nextTree].isNull) return vN.min; 
                //if(!vN.ptrArr[nextTree + 1].isNull)
                //{
                //return index(uS, nextTree, vN.ptrArr[nextTree + 1].max);
                // retVal = index(uS, nextTree, vN.cluster[nextTree].max);
                    //writeln("kuku: ", value);
                    // return retVal; 
                //}   
                // }

                // retVal = index(uS, high(value, uS), predecessor(low(value, uS), vN.ptrArr[subTreeIndex], hSR(uS)));
                // return retVal; 
                //if(canFind(suspiciousValues, value)) writeln("easy steps done"); 
                const auto minlow = vN.cluster[high(value, uS)].min; 
                if(!minlow.isNull && low(value, uS) > minlow)
                {
                    /*
                    if(canFind(suspiciousValues, value))
                        {
                            writeln("if 1"); 
                            writeln("high(value, uS): ", high(value, uS)); 
                            writeln("low(value, uS): ", low(value, uS)); 
                            writeln("sending value (low(value, uS)): ", low(value, uS)); 
                        }
                    */
                    auto offset = predecessor(low(value, uS), vN.cluster[high(value, uS)], lSR(uS));
                    /*
                    if(canFind(suspiciousValues, value))
                    {
                        writeln("got offset: ", offset); 
                        writeln("low: ", low(value, uS)); 
                        writeln("high: ", high(value, uS)); 
                        writeln("lSR: ", lSR(uS)); 
                        writeln("hSR: ", hSR(uS));
                        writeln("uS: ", uS);
                        write("bin: "); bin(value); 
                        writeln(); 
                    } 
                    */
                    retVal = index(uS, high(value, uS), offset); 
                    //if(canFind(suspiciousValues, value)) writeln("retVal: ", retVal); 
                }
                else
                {
                    /*
                    if(canFind(suspiciousValues, value)) 
                    {
                        writeln("else 1"); 
                        writeln("low: ", low(value, uS)); 
                        writeln("high: ", high(value, uS)); 
                        writeln("lSR: ", lSR(uS)); 
                        writeln("hSR: ", hSR(uS));
                        writeln("uS: ", uS); 
                        write("bin: "); bin(value); 
                        writeln(); 
                        writeln("sending value (high(value, uS)): ", (high(value, uS))); 
                    }
                    */ 
                    auto predcluster = predecessor(high(value, uS), vN.summary, hSR(uS));
                    //if(canFind(suspiciousValues, value)) writeln("predcluster: ", predcluster); 
                    if(predcluster.isNull)
                    {
                        /*
                        if(canFind(suspiciousValues, value))
                        {
                            writeln("if 2"); 
                            writeln("predcluster.isNull: ", predcluster.isNull); 
                            writeln("vN.min: ", vN.min); 
                            writeln("value: ", value); 
                        }
                        */
                        if(!vN.min.isNull && value > vN.min)
                            return vN.min; 
                    }
                    else
                    {
                        /*
                        if(canFind(suspiciousValues, value))
                        {
                            writeln("else 2");
                            writeln("predcluster.isNull: ", predcluster.isNull); 
                        }
                        */
                        auto offset = vN.cluster[predcluster].max; 
                        retVal = index(uS, predcluster, offset); 
                    }
                }
                return retVal; 
        }
        unittest
        {
            auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
            write("UT: vT, predecessor.  "); writeln("seed: ", currentSeed); 
            rndGenInUse.seed(currentSeed); //initialize the random generator
             
            auto uS = uniform(allowedArraySize,testedSize, rndGenInUse);
            VEBtree vT = new VEBtree(uS); 

            size_t n; 
            uint[allowedArraySize] insertedVals;  
            while(n < allowedArraySize)
            {
                auto valToInsert = uniform(0U, uS, rndGenInUse); 
                bool inserted = vT.insert(valToInsert); 
                if(inserted)
                {
                    insertedVals[n] = valToInsert; 
                    n++;
                }
            }
            
            //writeln("size: ", vT.length); 
            auto sortedInserted = assumeSorted(sort(insertedVals[])); 
            //writeln("max: ", vT.max); 
            //writeln("min: ", vT.min); 
            //writeln("back: ", sortedInserted.back); 
            //writeln("front: ", sortedInserted.front); 

            assert(vT.max == sortedInserted.back); 
            assert(vT.min == sortedInserted.front); 
            size_t j = allowedArraySize - 1; 

            size_t i = testedSize + 1; 
            do
            {
                /*
                    if(i == 12292095 || i == 13525034)
                    {
                        writeln("i: ", i); 
                        write("bin i + 1: ", i + 1, " "); bin(i + 1); 
                        writeln(); 
                        write("bin i: ", i, " "); bin(i); 
                        writeln(); 
                        writeln("expected result: ", sortedInserted.lowerBound(i)[$-1]);
                    }
                  */
                  //writeln("i: ", i);  
                  --i;
                const auto el = vT.predecessor(i); 
                    //if(i == 12292095 || i == 13525034) 
                        //writeln("ii: ", i); 
                        /*
                    if(i == 12292095 || i == 13525034)
                    {
                        writeln("elel: ", el); 
                        assert(sortedInserted.contains(el.get)); 
                        writeln(sortedInserted.contains(el.get)); 
                    }
                        */
                
                if(el.isNull)
                {
                    assert(i == vT.min); 
                    assert(sortedInserted.contains(i));
                    break; // quit the loop;

                }
                else
                {
                    //writeln("i: ", i); 
                    //writeln("el: ", el); 
                    if(sortedInserted.contains(i)) --j; 
                    assert(el == sortedInserted[j]); 
                }
                 
            }while(i > 0);
        }

        // this method is used to determine, whether the tree is currently containing an element. 
        @property bool empty() { return root.isNull; }

        // this method returns the minimium. 
        @property size_t front()
        in { assert(!root.isNull); }
        body { return this.min; }

        // this method removes the minimum element
        void popFront(){ if(!empty) remove(min); }

        // bidirectional range also needs
        @property size_t back()
        in { assert(!root.isNull); }
        body { return this.max; }
    
        // this method removes the maximum element 
        void popBack() { if(!empty) remove(max); }
    
        /**
            This method returns the amount of elements currently present in the tree.
            This is a draft version, as it uses the slice operator of the class. So getting this number has a complexity
            proportional to n. As this functionaly is not seen as crucial, it is enough for the first time. 
        */
        @property size_t length(){ return _elementCount; }
    }
    
    // forward range also needs save. This is a draft version of the save function, it uses the opslice of the struct
    // to construct a new one via an array
    @property VEBtree save() { return new VEBtree(this[]); }
    
    /**
    opSlice operator to get the underlying array. 
    This is a draft version, as it uses the successor method of the class. So getting the underlying array is 
    proportional to n. As this functionaly is not seen as crucial, it is enough for the first time. 
    */
    //TODO: opSlice operator should be implemented as generator, to avoid memory reallocations.
    private size_t[] opSlice()
    {
        size_t[] retArray; 
        if(!min.isNull)
        {
            retArray ~= min;
            if(min != max)
            {
                retArray.reserve(max - min + 1);
                while(retArray[$-1] != max)
                    retArray ~= successor(retArray[$-1]); 
            }
        }
        //writeln(retArray); 
        return retArray; 
    }
    
    // (optional) todo: implement some kind of cool output as a graphViz pic, similiar to the graphs in Cormen. 
}

///
unittest
{

    VEBtree vT = new VEBtree(100); 
    assert(vT.root.isNull);
    auto result = vT.insert(2); 
    assert(result); 
    assert(!vT.root.isNull); 
    assert(vT.member(2));     
    VEBtree vT2 = vT.save(); 
    assert(vT2.member(2)); 
    result = vT2.insert(3); 
    assert(result); 
    assert(vT2.member(3)); 
    assert(!vT.member(3));
}

///
unittest
{
    assert(!__traits(compiles, new VEBtree())); 
    VEBtree vT = new VEBtree(1000); 
    assert(vT.capacity == 1024); 
    assert(vT.min.isNull); 
    assert(vT.insert(2)); 
    vT.insert(5);
    assert(!vT.member(8)); 
    assert(vT.insert(88));
    assert(vT.member(88)); 
    assert(vT.predecessor(4) == 2);
    assert(!vT.member(8)); 
    assert(vT.insert(8)); 
    assert(vT.member(8)); 
    assert(vT.predecessor(75) == 8); 
    assert(vT.predecessor(90) == 88); 
    assert(vT.predecessor(7) == 5); 
    assert(vT.predecessor(4) == 2); 
    assert(vT.predecessor(2).isNull); 
    assert(vT.successor(6) == 8); 
    assert(vT.successor(5) == 8); 
    assert(vT.successor(4) == 5); 
    assert(vT.successor(1) == 2); 
    assert(vT.successor(75) == 88); 
    assert(vT.successor(90).isNull); 
    assert(!vT.member(1029)); 
    assert(!vT.member(1029)); 
    assert(vT.successor(1025).isNull);
    
    auto vT2 = new VEBtree(500); 
    assert(vT2.empty); 
    vT2.insert(50); 
    vT2.insert(500); 
    assert(vT2.max == 500); 
    assert(vT2.min == 50); 
    assert(vT2.successor(40) == 50);
    assert(vT2.successor(50) == 500); 
    
    /* about 30 seconds
    auto vT3 = new VEBtree(uint.max);
    assert(vT3.insert(5)); 
    assert(vT3.member(5));
    assert(vT3.capacity == cast(ulong)uint.max + 1);
    //*/
    
    assert(!vT.member(1029)); 
    assert(!vT.member(865)); 
    assert(vT.insert(865)); 
    assert(vT.member(865)); 
    assert(!vT.insert(865)); 
    assert(vT.member(865)); 
    assert(!vT.member(866)); 
    assert(!vT.remove(866)); 
    assert(vT.member(865)); 
    assert(vT.remove(865)); 
    assert(!vT.member(865)); 

}

///

unittest
{
    auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
    //writeln("currSeed: ", currentSeed); 
    rndGenInUse.seed(currentSeed); //initialize the random generator

    auto M = uniform(0U,testedSize, rndGenInUse); //set universe size to some integer. 
    //M = 30_000_000; 
    VEBtree vT = new VEBtree(M); //create the tree
    assert(vT.capacity == nPof2(M)); 
    auto m = vT.fill(40, rndGenInUse); //(try to) fill the tree with thousend values 
    /*
    writeln("vT.length: ", vT.length);
    writeln("vT.max: ", vT.max); 
    writeln("vT.min: ", vT.min); 
    writeln("vT.capacity: ", vT.capacity); 
    */
    size_t n; 
    Nullable!(size_t, maxSize) i = vT.max; 

    // discover the thousend (or little less) values with the predecessor method
    while(!i.isNull)
    {
        ++n;
        //writeln("i: ", i); 
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
    /*
    writeln("------"); 
    writeln("n: ", n); 
    writeln("m: ", m);
    writeln("o: ", o);
    */
}

///
unittest
{
    auto currentSeed = unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = fill(M, rndGenInUse); //fill the tree with some values 
    Nullable!(size_t, maxSize) i = vT.max; 
    
    // remove all members beginning from the maximum
    bool result; 
    while(!i.isNull)
    {
        result = vT.remove(i); 
        assert(result); 
        auto j = vT.predecessor(i); 
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
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = fill(M, rndGenInUse); //fill the tree with some values 
    Nullable!(size_t, maxSize) i = vT.min;
    
    // remove all members beginning from the minimum
    bool result; 
    while(!i.isNull)
    {
        import std.conv; 
        
        result = vT.remove(i); 
        assert(result); 
        auto j = vT.successor(i); 
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
    uint M = 1 << 16; 
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
    uint M = 1 << 16; 
    VEBtree vT = new VEBtree(M); 
    vT.insert(0xf000); 
    assert(vT.member(0xf000)); 
    vT.insert(0x0f00); 
    assert(vT.member(0x0f00)); 
    vT.insert(0x00f0);
    assert(vT.member(0x00f0)); 
    vT.insert(0x000f); 
    assert(vT.member(0x000f)); 
    
    auto result = vT.remove(0xf000); 
    assert(result); 
    assert(!vT.member(0xf000)); 
    result = vT.remove(0x0f00); 
    assert(result); 
    assert(!vT.member(0x0f00)); 
    result = vT.remove(0x00f0); 
    assert(result); 
    assert(!vT.member(0x00f0)); 
    result = vT.remove(0x000f); 
    assert(result); 
    assert(!vT.member(0x000f)); 
}

/// 
unittest
{
    //stress test
    auto currentSeed = unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    // last test says: see below. 
    auto M = uniform(1U, testedSize, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 
    size_t[] arr; 
    auto howMuchFilled = vT.fill(arr, rndGenInUse); 

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
    //auto r = benchmark!(fill1)(1); 
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
    uint currentSeed = unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer.
    uint[] sourceArr; 
    sourceArr.length = M; 
    // generate a random array as the source for the tree
    for(uint i = 0; i < M; i++) sourceArr[i] = uniform(0U, M, rndGenInUse); 
    // constructor to test
    VEBtree vT = new VEBtree(sourceArr); 
    // make the array values unique. 
    auto uniqueArr = sort(sourceArr).uniq;
    // check, that all values are filled 
    bool result; 
    foreach(uint i; uniqueArr)
    {
        assert(vT.member(i)); 
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
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    auto M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 
    size_t[] arr; 
    vT.fill(arr, rndGenInUse, 16); 
    
    assert(setSymmetricDifference(vT[], sort(arr)).empty); 
}

///
unittest
{
    uint currentSeed = unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    auto M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 
    size_t[] arr; 
    vT.fill(arr, rndGenInUse, 16); 
    auto begin = 5; 
    auto end = 100; 
    auto filterRes = sort(arr).filter!(a => a >= begin && a < end);
    /* test commented out due to disabling opSlice operation */
    //assert(setSymmetricDifference(filterRes, vT[begin..end]).empty); 
}

///
unittest
{
    auto currentSeed = unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    auto M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    VEBtree vT = new VEBtree(M); 
    size_t[] arr; 
    vT.fill(arr, rndGenInUse, 16); 
    assert(vT.length == vT.elementCount); 
}

///
/*
unittest
{
    assert(isBidirectionalRange!VEBtree);
}
*/

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
    assert(vT[] == [2, 5, 10]); 
}

///


unittest
{
    /+
    //another stress test
    auto currentSeed = unpredictableSeed(); 
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
    
    /*
        This part is for speed test. 
    */
    /*
    import std.stdio; 
    auto r = benchmark!(fill16, fill17, fill18, fill19, fill20, fill21, fill22, fill23, fill24, fill25)(1); 
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
    //*/
    +/
}


///
/*
    This unittest is for check of adding of big numbers
*/
unittest
{

    /* 
    uint[] arr = [1, 2, 8, 2147483647]; 
    auto vT = new VEBtree(arr)); 
    */
}