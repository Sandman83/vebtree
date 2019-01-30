module vebtree.vebroot; 
import vebtree; 
import std.bitmanip : taggedPointer; 
public import core.bitop;
import std.traits;
public import std.range; 
public import std.math : nextPow2; 
public import core.stdc.limits : CHAR_BIT; 
import std.algorithm.iteration : each, map, uniq, sum, filter;
public import std.algorithm.searching : until, find, canFind, maxIndex, count, minElement, maxElement; 
public import std.algorithm.sorting : sort, isSorted; 
import std.algorithm.setops : setSymmetricDifference; 
import std.algorithm.mutation : remove; 

debug 
{
    //version = bug; 
    version(bug)
    {
        import std.experimental.logger; 
    }
    else
    {
        version(DigitalMars)
        {
            import std.experimental.logger; 
        }
        version(LDC)
        {
            import std.stdio; 
            alias trace = writeln; 
        }
    }
}

version(unittest)
{
    import std.random; 
    import std.format; 
    import std.conv : to;
    import std.container; // red black tree may be used in unittests for comparison.
    import std.math : sqrt; 
    public import std.random; 
    
    //size_t[] debugNumbers;
    //string debugFunction; 
    //bool print; 

    // helping function for output a given value in binary representation
    void bin(size_t n)
    {
        /* step 1 */
        if (n > 1) bin(n/2);
        /* step 2 */
        import core.stdc.stdio : printf; 
        printf("%d", n % 2);
    }
    
    /// precalculated powers of two table for unit testing
    enum powersOfTwo = (CHAR_BIT * size_t.sizeof).iota.map!(a => size_t(1) << a); 
    enum testMultiplier = 1; //16
    
    ///
    static assert(!isInputRange!(ReturnType!(vebRoot!(CHAR_BIT * size_t.sizeof)))); 
    static assert(isIterable!(ReturnType!(vebRoot!(CHAR_BIT * size_t.sizeof))));
    static assert(isBidirectionalRange!(ReturnType!(vebRoot!(CHAR_BIT * size_t.sizeof))[]));
    static assert(!is(typeof(vebRoot(4)[2])));

    auto generateVEBtree(string identifier1, size_t baseSize)
        (size_t identifier2, uint currentSeed, size_t min, size_t max, ref size_t M)
    {
        static assert(baseSize > 1); 
        static assert((baseSize & (baseSize - 1)) == 0);  
        assert(min >= 2); 
        rndGen.seed(currentSeed); //initialize the random generator
        M = uniform(min, max + 1); // parameter for construction
        return vebRoot!baseSize(M);
    }
}

version(unittest)
{
    string generateDebugString(string identifier1, size_t identifier2, size_t baseSize, uint currentSeed, size_t M)
    {
        return format!"%s: %d baseSize: %d; seed: %d M: %d"(identifier1, identifier2, baseSize, currentSeed, M); 
    }
}

/**
the baseSize defines the cutoff limit, where the node goes into the bit array mode. It is parametrized on the size
of size_t and changes dynamically with the architecture used. 
*/

/// bit mask representing uint.max. 
enum size_t lowerMask = size_t.max >> (size_t.sizeof * CHAR_BIT / 2);
/// bit mask representing size_t.max without uint.max. 
enum size_t higherMask = size_t.max ^ lowerMask; 

/**
This function returns the higher square root of the given input. It is needed in the initialization step 
of the VEB tree to calculate the number of children of a given layer. And this is the universe size of the
summary of a node. The upper square root is defined by 2^{\lceil(\lg u)/2\rceil}
*/
package size_t hSR(size_t val) @nogc  
{
    return size_t(1) << (bsr(val)/2 + ((val.bsr & 1) || ((val != 0) && (val & (val - 1))))); 
}
//
unittest
{
    
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: hSR. seed: %d"(currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL,uint.max); //set universe size to some integer. 
    auto hSR = hSR(M); 
    assert((hSR & (hSR - 1)) == 0, errorString); 
    
    auto check = powersOfTwo.until(hSR).array; 
    assert((check[$-1]) * (check[$-1]) < M, errorString); 
}

/**
This function returns the lower square root of the given input. It is needed by the indexing functions
high(x), low(x) and index(x,y) of elements in the tree. Also, this is the universe size of a child of a node. The
lower square root is defined by 2^{\lfloor(\lgu)/2\rfloor}
*/
package size_t lSR(size_t val) @nogc  
{
    return size_t(1) << (bsr(val)/2);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: lSR               seed: %d"(currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL,uint.max); //set universe size to some integer. 
    auto lSR = M.lSR; 
    
    assert((lSR & (lSR - 1)) == 0, errorString); 
    assert(lSR * lSR < M, errorString);
    auto check = powersOfTwo.find(lSR); 
}

/*
This is an index function defined as \lfloor x/lSR(u)\rfloor. It is needed to find the appropriate cluster
of a element in the tree. It is a part of the ideal indexing function.
*/
private size_t high(size_t universe, size_t val) @nogc  
out(result)
{
    assert(result == val / universe.lSR); // bithacks = keithschwarz
}
do
{
    return val >> (bsr(universe) / 2); 
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: high              seed: %d"(currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator
    const M = uniform(1UL,uint.max); //set universe size to some integer. 
    assert(M, errorString); 
    size_t U = M.nextPow2; 
    assert(U, errorString); 
    auto x = uniform(0UL, U); 
    assert(high(U, x) == x / U.lSR, errorString); 
}

/*
This is an index function defined as fmod(value, lSR(universe)). It is needed to find the appropriate
value inside a cluster. It is part of the ideal indexing function
*/
private size_t low(size_t universe, size_t val) @nogc 
out(retVal)
{
    assert(retVal == (val & ((size_t(1) << (bsr(universe) / 2)) - 1)));
}
do
{
    return val % universe.lSR; 
}

//
unittest
{
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: low               seed: %d"(currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL,uint.max); //set universe size to some integer. 
    size_t U = nextPow2(M); 
    auto x = uniform(0UL, U); 
    assert(low(U, x) == (x & (U.lSR - 1)), errorString);
}

/*
This is an index function to retain the searched value. It is defined as x * lSR(u) + y. Beyond this, the
relation holds: x = index(high(x), x.low). This is the ideal indexing function of the tree. 
*/
private size_t index(size_t universe, size_t x, size_t y) @nogc 
{
    return (x * universe.lSR + y);
}
//
unittest
{
    auto currentSeed = unpredictableSeed(); 
    const errorString = format!"UT: index             seed: %d"(currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator
    const M = uniform(0UL,uint.max); //set universe size to some integer. 
    size_t U = M.nextPow2; 
    auto x = uniform(0UL, U); 
    assert(index(U, U.high(x), U.low(x)) == x, errorString); 
}

private auto vebTree(Flag!"inclusive" inclusive, alias root)()
{
    auto retVal = VEBtree!(inclusive, root)();

    retVal.length = root.length_; 

    static if(inclusive)
    {
        debug
        {
        }

        assert(retVal.frontKey == 0); 

        if(vebtree.empty(root))
        {
            retVal.backKey = root.universe;
            assert(!retVal.length); 
            retVal.length += 2; 
        }
        else
        {
            if(root.max <= root.universe)
            {
                retVal.backKey = root.universe;
                if(root.max < root.universe)
                {
                    retVal.length += 1; 
                }
            }
            else
            {
                assert(root.max < root.capacity); 
                retVal.backKey = root.capacity; 
                retVal.length += 1; 
            }

            if(root.min) // i. e. front != 0
            {
                retVal.length += 1; 
            }
        }
    }
    else
    {
        retVal.frontKey = root.min; 
        retVal.backKey = root.max; 
    }

    return retVal;
}
static foreach(_; 1 .. size_t.sizeof - 1)
{
    unittest
    {
        import std.parallelism : parallel; 
        enum baseSize = 1 << _; 
        foreach(b; (CHAR_BIT * size_t.sizeof * testMultiplier).iota.parallel)
        {
            auto currentSeed = unpredictableSeed();
            size_t M; 
            auto vT = generateVEBtree!("UT: white box test: ", 1 << _)(b, currentSeed, 2UL, baseSize, M);

            assert(vT.value_ == 0);
            if(vT.isLeaf)
            {
                assert(vT.ptr_ is null);
                assert(vT.capacity == baseSize);
            }
            else
            {
                assert(!(vT.ptr_ is null));
                assert(vT.capacity == (vT.universe - 1).nextPow2);
            }
            
            assert(vT.empty == true);
            assert(vT.min == NIL); 
            assert(vT.max == NIL); 
            assert(vT[].front == 0); 
            assert(vT[].back == vT.universe); 
            assert(vT().front == NIL);
            assert(vT().back == NIL); 
            assert(vT.length == 0);
            assert(vT.universe == M);
            
            size_t N = uniform(0UL, 2 * M); // independent parameter for testing
            // make an array of length N
            size_t[] testArray, cacheArray;
            testArray = new size_t[N]; 
            cacheArray.reserve(N);
            // fill the array with all possible values 
            foreach(ref el; testArray)
            {
                el = (2 * M).iota.choice;
            }

            foreach(testNumber; testArray)
            {
                assert(vT.universe == M);

                const insertResult = vT.insert(testNumber);
                
                if(insertResult)
                {
                    assert(!vT.empty);
                    cacheArray ~= testNumber;
                }
            }

            cacheArray.sort;
            
            if(cacheArray.empty)
            {
                assert(vT.empty);
            }
            else
            {
                assert(!vT.empty);
            }
            
            foreach(el; cacheArray)
            {
                assert(bt(&vT.value_, el));
            }
            assert(vT.length == cacheArray.uniq.count);
            assert(vT.universe == M);
            if(cacheArray.length)
            {
                assert(vT.min == cacheArray.front); 
                assert(vT.max == cacheArray.back); 
            }
            else
            {
                assert(vT.min == NIL);
                assert(vT.max == NIL);
            }
            
            auto currElement = vT.min; 
            foreach(el; cacheArray.uniq)
            {
                assert(currElement == el); 
                currElement = vT.next(currElement); 
            }
            currElement = vT.max;
            foreach(el; cacheArray.uniq.array.retro)
            {
                assert(currElement == el); 
                currElement = vT.prev(currElement); 
            }

            foreach(key; 0 .. vT.universe)
            {
                if(cacheArray.uniq.array.canFind(key))
                {
                    assert(key in vT); 
                }
                else
                {
                    assert(!(key in vT));
                }
            }
            auto deepCopy = vT.dup; 

            assert(deepCopy.value_ == vT.value_);
            assert(vT == cacheArray.uniq);
            assert(vT.prev(vT.min) == NIL);
            assert(vT.next(vT.max) == NIL);
            assert(vT == deepCopy);
            assert(vT == deepCopy());
            
            if(cacheArray.length)
            {
                auto valToRemove = cacheArray.uniq.array.randomCover.front; 
                vT.removeImpl(valToRemove);
                assert((deepCopy.value_ ^ vT.value_) == (size_t(1) << valToRemove)); 
                cacheArray
                    .count(valToRemove)
                    .iota
                    .each!(i => cacheArray = 
                                cacheArray
                                    .remove(cacheArray.length - cacheArray.find(valToRemove).length));
            }
            else
            {
                assert((deepCopy.value_ ^ vT.value_) == 0); 
            }
            
            foreach(key; 0 .. vT.capacity)
            {
                if(cacheArray.uniq.array.canFind(key))
                {
                    assert(vT.removeImpl(key)); 
                }
                else
                {
                    assert(!(vT.removeImpl(key)));
                }
            }
            assert(vT.value_ == 0); 
            assert(vT.empty);
        }   
    }
}

/**
define the absence of a key to be -1. 
*/
enum NIL = ptrdiff_t(-1); 

/**
This is the struct to represent a VEB tree node. Its members are
- a pointer to the stats: universe and current inserted element amount 
- a pointer to the min and max values. These pointee is used as a bit array in the leaf nodes. 
- a poitner (or array) to the child nodes, in case the node is not a leaf node
- a pointer (an array) to the data pointers, in case the tree is used with data. 
Dependent from the universe size passed in a method the stored value will be interpretated in two different ways: 
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

package struct VEBroot(size_t baseSize)
{
    /**
    the maxSizeBound defines the maximum the tree can be constructed with. It is parametrized on the size of size_t and
    changes dynamically with the architecture used. 
    */
    enum maxSizeBound = size_t(1) << (CHAR_BIT * size_t.sizeof/2); // == uint.max + 1 on a 64-bit system

    size_t toHash() const nothrow
    {
        assert(0); 
    }

    /**
    yields a deep copy of the node. I. e. copies all data in children and allocates another tree 
    */
    typeof(this) dup() 
    {
        auto retVal = typeof(this)(universe_); 
        foreach(el; opCall())
        {
            retVal.insert(el); 
        }
        return retVal; 
    }

    bool opEquals(T)(auto ref T input) const if(isIterable!T)
    {
        static if(hasLength!T)
        {
            if(length != input.length)
            {
                return false; 
            }
        }
        
        size_t currentElem = this.min; 

        debug
        {
            static if(hasLength!T)
            {
            }
            
        }
        foreach(el; input)
        {
            debug
            {
            }
            if(el != currentElem)
            {
                return false; 
            }
            currentElem = this.next(currentElem); 
        }
        
        return true; 
    }

    invariant
    {
        if(!(ptr_ is null))
        {
            assert(universe_ >= 2);
        }
        if(universe_ <= baseSize)
        {
            assert(this.capacity == baseSize); 
            assert(ptr_ is null); 
        }
    }

    /**
    member method for the case universe size < base size. Overloads by passing only one parameter, which is
    the bit number of interest. Returns whether the appropriate bit inside the bitvector is set.
    */
    bool opBinaryRight(string op)(size_t key) @nogc if(op == "in")
    in
    {
        if(!(ptr_ is null))
        {
            assert(universe_ >= 2); 
        }
    }
    do
    {
        debug
        {
        }
        if(key >= this.capacity)
        {
            debug
            {
            }
            return false; 
        }

        if(this.empty)
        {
            debug
            {
            }
            // if an empty intermediate node is found, nothing is stored below it. 
            return false; 
        } 

        debug
        {
        }
        if(this.isLeaf)
        {
            debug
            {
            }
            assert(key < baseSize);

            debug
            {
            }
            return bt(&value_, key) != 0;
        }
        else
        {
            debug
            {
            }
            // case of a single valued range. 
            if(key == this.min || key == this.max)
            {
                debug
                {
                }
                return true; 
            }
            
            /*
                else we have to descend, using the recursive indexing: 
                1. take the high(value, uS)-th child and 
                2. ask it about the reduced low(value, uS) value
                3. use the lSR(uS) universe size of the childe node. 
            */
            debug
            {
                if(!(ptr_[high(key)].ptr_ is null))
                {
                    assert(ptr_[high(key)].universe_ >= 2); 
                }
            }
            return low(key) in ptr_[high(key)]; 
        }
    }
    /**
    yields the next power of two, based un universe size
    */
    size_t capacityImpl() const @nogc
    {
        return baseSize;
    }

    /**
    the opApply method grants the correct foreach behavior, nogc version
    */
    int opApply(scope int delegate(ref size_t) @nogc operations) @nogc
    {
        return opApplyImpl(operations);
    }

    /**
    the opApply method grants the correct foreach behavior
    */
    int opApply(scope int delegate(ref size_t) operations)
    {
        return opApplyImpl(operations);
    }

    // with the trick of https://forum.dlang.org/thread/erznqknpyxzxqivawnix@forum.dlang.org
    private int opApplyImpl(O)(O operations)
    {
        int result; 

        debug
        {
        }
        size_t leading = this.min; 

        //for(size_t leading = min; leading < max; leading = this.next(leading)) 
        
        for(size_t i = 0; i < length; ++i)
        {
            debug
            {
            }

            result = operations(leading);
            
            if(result)
            {
                break; 
            }

            leading = this.next(leading);
        }
        
        return result;
    }

    /**
    []-slicing. Yields a "random access range" with the content of the tree, always containing zero and universe as keys
    */
    auto opIndex()
    {
        return vebTree!(Yes.inclusive, this)();
    }

    /**
    ()-slicing. Yields a "random access range" with the content of the tree. Keys can be NIL. 
    */
    auto opCall()
    {
        return vebTree!(No.inclusive, this)();
    }    

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
    this(size_t val)  
    in
    {
        assert(val >= 2); 
    }
    do
    {
        universe_ = val;
        this.setEmpty; 
        debug{}
        
        assert(!length_ == this.empty);
        
        debug{}
        
        if(!isLeaf)
        {
            debug{}

            assert(this.capacity == (universe_ - 1).nextPow2);
            const arrSize = this.capacity.hSR + 1; 

            debug{}

            debug
            {
                assert(ptr_ is null);
            }
            
            // reserve enough place for the summary and the children cluster
            ptr_ = (new typeof(this)[arrSize]).ptr;
            
            debug
            {
                assert(!(ptr_ is null));
                foreach(i; 0 .. arrSize)
                {
                    assert(ptr_[i].universe_ == 0);
                }

                version(unittest)
                {
                    /*
                    if(debugNumbers.canFind(val) || print)
                    {
                        trace("universe_.hSR: ", universe_.hSR);
                        trace("universe_.lSR: ", universe_.lSR);
                        trace("this.capacity: ", this.capacity); 
                        trace("this.universe_: ", this.universe_);
                        print = true;   
                    }
                    */
                }
            }
            
            debug{}

            // add higher square root children with lower square root universe each.
            foreach(i, ref el; ptr_[0 .. this.capacity.hSR])
            {
                debug{}
                
                el = typeof(this)(this.capacity.lSR); 
            }

            // add the summary with its universe of higher squaure root of the current universe
            ptr_[this.capacity.hSR] = typeof(this)(this.capacity.hSR); 
            
            debug
            {
                if(!(ptr_ is null))
                {
                    foreach(ref el; ptr_[0 .. arrSize])
                    {
                        assert(el.universe_ >= 2); 
                    }
                }
            }
        }
        assert(!length_ == this.empty);
    }

    /**
    This tree has a length notion: it is the current number of inserted elements. 
    */
    size_t length() const @nogc
    {
        return length_; 
    }

    package:
    /**
    remove method. this method is called from class with a universe size given. It performs recursion calls untill
    the universe size is reduced to the base size. Then the overloaded remove method is called. 
    */
    bool removeImpl(size_t key) @nogc
    {
        return length = length - (btr(&value_, key) != 0); 
    }
    /**
    successor method. this method is called from class with a universe size given. It performs recursion calls until
    the universe size is reduced to the base size. Then the overloaded successor method is called. 
    */
    size_t nextImpl(size_t val) const @nogc 
    {
        debug{}

        // if this node is empty, no successor can be found here or deeper in the tree
        if(emptyImpl) return NIL; 

        debug{}

        if(val + 1 >= baseSize) return NIL;

        debug{}

        // create a mask, which hides all lower bits of the stored value up to the given bit number, then apply
        // bit search from the lowest bit. 
        auto maskedVal = value_ & ~((size_t(1) << (val + 1)) - 1); 

        debug{}

        if(maskedVal != 0) return maskedVal.bsf;

        debug{}

        return NIL; 
    }
    size_t prevImpl(size_t val) @nogc 
    {  
        debug{}
            
        if(!this.empty && (val != 0))
        {
            debug{}
            
            /*
            create a mask, which hides all higher bits of the stored value down to the given bit number, then apply
            bit search from the highest bit. 
            */
            auto maskedVal = value_ & ((size_t(1) << val) - 1); 

            debug{}

            if(maskedVal != 0)
            {
                debug{}

                return typeof(return)(maskedVal.bsr);
            }
        }
        return NIL;
    }
    bool insertImpl(size_t key) @nogc
    {
        debug{}

        return length = length + (bts(&value_, key) == 0);
    }

    bool minImpl(size_t key) @nogc
    {
        // the passed value should not exceed the allowed size of a size/2
        return insertImpl(key);
    }

    bool maxImpl(size_t key) @nogc
    {
        return insertImpl(key);
    }
    
    size_t maxImpl() const @nogc
    {
        if(value_ == 0) return NIL; 
        return bsr(value_); 
    }

    size_t minImpl() const @nogc
    {
        if(value_ == 0) return NIL; 
        return bsf(value_);
    }

    bool length(size_t input) @nogc
    in
    {
        debug{}
        
        assert(input <= this.capacity);
        
        if(input != length)
        {
            input > length ? assert(input - length == 1) : assert(length - input == 1);
        }
    }
    do
    {
        const retVal = length != input; 
        
        length_ = input;

        if(!length_)
        {
            this.setEmpty;
        }
        
        return retVal; 
    }

    bool setEmptyImpl() @nogc
    {
        const retVal = value_ == 0 ? false : true;
        value_ = 0; 
        return retVal; 
    }

    bool emptyImpl() const @nogc 
    {
        return value_ == 0; 
    }
    
    size_t index(size_t x, size_t y) const @nogc
    {
        return .index(this.capacity, x, y); //universe_
    }

    size_t low(size_t val) const @nogc
    {
        return .low(this.capacity, val); //universe_
    }

    size_t high(size_t val) const @nogc
    {
        return .high(this.capacity, val); //universe_
    }
    bool isLeaf() const @nogc 
    {
        return universe_ <= baseSize; 
    }

    size_t value_;
    size_t universe_;
    size_t length_; 
    typeof(this)* ptr_;
}

private struct VEBtree(Flag!"inclusive" inclusive, alias root)
{
    auto opBinaryRight(string op)(size_t key) @nogc  
        if(op == "in") 
    {
        return key in root; 
    }

    static if(inclusive)
    {
        size_t frontKey; 
        size_t backKey; 
    }
    else
    {
        ptrdiff_t frontKey; 
        ptrdiff_t backKey; 
    }

    size_t length; 

    typeof(frontKey) front() @nogc
    {        
        return frontKey; 
    }

    void popFront() @nogc
    in
    {
        assert(!empty); 
    }
    do
    {
        debug
        {
        }

        frontKey = next(frontKey);
        --length; 
    }
    
    typeof(backKey) back() @nogc
    {
        return backKey; 
    }

    void popBack()
    in
    {
        assert(length); 
    }
    do
    {
        backKey = prev(backKey); 
        --length;
    }

    auto prev(size_t key) @nogc
    {
        const pred = root.prev(key);
        static if(inclusive)
        {
            return pred == NIL ? 0 : pred; 
        }
        else
        {
            return pred; 
        }
    }

    auto next(size_t key) @nogc
    {
        const succ = root.next(key);
        static if(inclusive)
        {
            if(succ == NIL)
            {
                if(key <= root.universe)
                {
                    return root.universe; 
                }
                else if(key <= root.capacity)
                {
                    return root.capacity; 
                }
                else
                {
                    assert(0, "key exceeds tree capacity");
                }
            }
            else
            {
                return succ; 
            }
        }
        else
        {
            return succ; 
        }
    }
    
    bool empty() @nogc
    {
        return !length; 
    }

    auto save()
    {
        return this; 
    }

    size_t toHash() const nothrow
    {
        assert(0);
    }

    /**
    for comparison with an iterable, the iterable will be iterated, as the current object.
    */
    bool opEquals(T)(auto ref T input) const if(isIterable!T)
    {
        static if(is(T == typeof(this)))
        {
            return root == input.root; 
        }

        static if(hasLength!T)
        {
            if(length != input.length)
            {
                return false; 
            }
        }

        auto copy = this.save;

        foreach(el; input)
        {
            if(el != copy.front)
            {
                return false; 
            }
            popFront(copy); 
        }
        
        return true; 
    }
}