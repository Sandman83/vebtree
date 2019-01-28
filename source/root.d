module vebtree.root; 
import vebtree; 
import std.bitmanip : taggedPointer; 
import core.bitop;
import std.traits;
public import std.range; 
public import std.math : nextPow2; 
import core.stdc.limits : CHAR_BIT; 
import std.algorithm.iteration : each, map, uniq, sum, filter;
import std.algorithm.searching : until, find, canFind, maxIndex, count, minElement, maxElement; 
import std.algorithm.sorting : sort, isSorted; 
import std.algorithm.setops : setSymmetricDifference; 
import std.algorithm.mutation : remove; 
debug import std.experimental.logger; 

version(unittest)
{
    import std.random; 
    import std.datetime.stopwatch; 
    import std.conv : to;
    import std.container; // red black tree may be used in unittests for comparison.
    import std.math : sqrt; 
    public import std.parallelism : parallel; 

    // helping function for output a given value in binary representation
    void bin(size_t n)
    {
        /* step 1 */
        if (n > 1) bin(n/2);
        /* step 2 */
        logf("%d", n % 2);
    }

    enum bitness = CHAR_BIT * size_t.sizeof; 
    /// precalculated powers of two table for unit testing
    enum powersOfTwo = (bitness).iota.map!(a => size_t(1) << a); 
    enum defaultBaseSize = CHAR_BIT * size_t.sizeof; 
    enum testMultiplier = 1; //16
    ///

    /*
    static assert(!isInputRange!(VEBroot)); 
    static assert(isIterable!(VEBroot));
    static assert(isBidirectionalRange!(typeof(VEBroot[])));
    static assert(!is(typeof(vebRoot(4)[2])));
    */

    auto generateVEBtree(string identifier1, size_t baseSize)
        (size_t identifier2, uint currentSeed, size_t min, size_t max, ref size_t M)
    {
        static assert(baseSize > 1); 
        static assert((baseSize & (baseSize - 1)) == 0); 
        assert(max > min); 
        rndGen.seed(currentSeed); //initialize the random generator
        M = uniform(min, max); // parameter for construction
        trace(identifier1,": ", identifier2, " baseSize: ", baseSize, "; seed: ", currentSeed, " M: ", M); 
        return vebRoot!baseSize(M);
    }
}

/**
the baseSize defines the cutoff limit, where the node goes into the bit array mode. It is parametrized on the size
of size_t and changes dynamically with the architecture used. 
*/
//enum baseSize = CHAR_BIT * size_t.sizeof; 

/// calculating the type, based on native type of the underlying system
static if(size_t.sizeof == 16) // future
{
	alias halfSizeT = ulong; 
}
else static if(size_t.sizeof == 8) // 64-bit case
{
	alias halfSizeT = uint; 
}
else static if(size_t.sizeof == 4) // 32-bit case 
{
	alias halfSizeT = ushort; 
}
else static if(size_t.sizeof == 2) // 16-bit case
{
	alias halfSizeT = ubyte; 
}
else 
{
	static assert(0);
}

/// bit mask representing uint.max. 
enum size_t lowerMask = halfSizeT.max; 
/// bit mask representing size_t.max without uint.max. 
enum size_t higherMask = (size_t.max ^ lowerMask); 

/**
This function returns the higher square root of the given input. It is needed in the initialization step 
of the VEB tree to calculate the number of children of a given layer. And this is the universe size of the
summary of a node. The upper square root is defined by 2^{\lceil(\lg u)/2\rceil}
*/
package size_t hSR(size_t value) @nogc //nothrow 
{
    return size_t(1) << (bsr(value)/2 + ((value.bsr & 1) || ((value != 0) && (value & (value - 1))))); 
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: hSR               ", "seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL,halfSizeT.max); //set universe size to some integer. 
    auto hSR = hSR(M); 

    assert((hSR & (hSR - 1)) == 0); 
    if(hSR < halfSizeT.max) assert(hSR >= sqrt(to!float(M)));
    
    auto check = powersOfTwo.until(hSR).array; 
    assert((check[$-1]) * (check[$-1]) < M); 
}

/**
This function returns the lower square root of the given input. It is needed by the indexing functions
high(x), low(x) and index(x,y) of elements in the tree. Also, this is the universe size of a child of a node. The
lower square root is defined by 2^{\lfloor(\lgu)/2\rfloor}
*/
package size_t lSR(size_t value) @nogc //nothrow 
{
    return size_t(1) << (bsr(value)/2);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: lSR               ", "seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL,halfSizeT.max); //set universe size to some integer. 
    auto lSR = M.lSR; 
    
    assert((lSR & (lSR - 1)) == 0); 
    assert(lSR * lSR < M);
    auto check = powersOfTwo.find(lSR); 
    if(lSR < halfSizeT.max) 
    {
        assert((check.drop(1).front) > sqrt(to!float(M))); 
    }
}

/*
This is an index function defined as \lfloor x/lSR(u)\rfloor. It is needed to find the appropriate cluster
of a element in the tree. It is a part of the ideal indexing function.
*/
private size_t high(size_t universe, size_t value) @nogc nothrow 
in
{
    assert((universe & (universe - 1)) == 0); 
}
do
{
    return value >> (bsr(universe) / 2);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: high              ", "seed: ", currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator
    const M = uniform(1UL,halfSizeT.max); //set universe size to some integer. 
    assert(M); 
    size_t U = M.nextPow2; 
    log("M: ", M); 
    log("M.nextPow2: ", M.nextPow2);
    assert(U); 
    auto x = uniform(0UL, U); 

    assert(high(U, x) == x / U.lSR); 
}

/*
This is an index function defined as fmod(value, lSR(universe)). It is needed to find the appropriate
value inside a cluster. It is part of the ideal indexing function
*/
private size_t low(size_t universe, size_t value) @nogc nothrow
in
{
    assert((universe & (universe - 1)) == 0); 
}
do
{
    return value & ((size_t(1) << (bsr(universe) / 2)) - 1);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: low               ", "seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL,halfSizeT.max); //set universe size to some integer. 
    size_t U = nextPow2(M); 
    auto x = uniform(0UL, U); 

    assert(low(U, x) == (x & (U.lSR - 1)));
}

/*
This is an index function to retain the searched value. It is defined as x * lSR(u) + y. Beyond this, the
relation holds: x = index(high(x), x.low). This is the ideal indexing function of the tree. 
*/
private size_t index(size_t universe, size_t x, size_t y) @nogc //nothrow
{
    return (x * lSR(universe) + y);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: index             ", "seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    const M = uniform(0UL,halfSizeT.max); //set universe size to some integer. 
    
    size_t U = M.nextPow2; 
    auto x = uniform(0UL, U); 
    
    assert(index(U, U.high(x), U.low(x)) == x); 
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
        if(root.empty)
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
        enum baseSize = 1 << _; 
        foreach(b; bitness.iota)
        {
            auto currentSeed = unpredictableSeed();
            size_t M; 
            auto vT = generateVEBtree!("UT: white box test #1: ", 1 << _)(b, currentSeed, 1, baseSize, M);

            assert(vT.value_ == 0);
            assert(vT.ptr is null);
            assert(vT.empty == true);
            assert(vT.min == NIL); 
            assert(vT.max == NIL); 
            assert(vT[].front == 0); 
            assert(vT[].back == vT.universe); 
            assert(vT().front == NIL);
            assert(vT().back == NIL); 
            assert(vT.length == 0);
            assert(vT.universe == M);
            assert(vT.capacity == baseSize);
            size_t N = uniform(0UL, baseSize); // independent parameter for testing
            auto testArray = (2 * M).iota.randomCover.array; 
            auto cacheArray = new size_t[N];
            
            size_t counter; 

            foreach(testNumber; testArray)
            {
                assert(vT.universe == M);
                if(counter == N) break; 

                const insertResult = vT.insert(testNumber);
                
                if(insertResult)
                {
                    assert(!vT.empty);
                    cacheArray[counter] = testNumber;
                    ++counter;
                }
            }
            
            //const originalCacheArray = cacheArray.dup; 
            cacheArray.sort;
            
            assert(vT.ptr is null);
            assert(vT.empty == !N);
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
auto vebRoot(size_t baseSize = defaultBaseSize)(size_t universe)
{
    return VEBroot!baseSize(universe); 
}
package struct VEBroot(size_t baseSize)
{
    /**
    the maxSizeBound defines the maximum the tree can be constructed with. It is parametrized on the size of size_t and
    changes dynamically with the architecture used. 
    */
    enum maxSizeBound = size_t(1) << baseSize/2; // == uint.max + 1 on a 64-bit system

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
        assert(universe_); 
    }

    /**
    member method for the case universe size < base size. Overloads by passing only one parameter, which is
    the bit number of interest. Returns whether the appropriate bit inside the bitvector is set.
    */
    bool opBinaryRight(string op)(size_t key) @nogc if(op == "in")
    {
        debug
        {
        }
        if(key >= this.capacity)
        {
            return false; 
        }

        if(this.empty)
        {
            // if an empty intermediate node is found, nothing is stored below it. 
            return false; 
        } 

        if(this.isLeaf)
        {
            assert(key < baseSize);
            return bt(&value_, key) != 0;
            //return (*static_cast<long*>(root) & (1 << value)) != 0;
        }
        else
        {
            
            // case of a single valued range. 
            if(key == this.min || key == this.max)
            {
                return true; 
            }
            
            /*
                else we have to descend, using the recursive indexing: 
                1. take the high(value, uS)-th child and 
                2. ask it about the reduced low(value, uS) value
                3. use the lSR(uS) universe size of the childe node. 
            */
            return low(key) in cluster[high(key)]; 
        }
    }
    /**
    yields the next power of two, based un universe size
    */
    size_t capacityImpl() @nogc
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
    this(size_t val) // nothrow 
    in
    {
        assert(val); 
    }
    do
    {
        universe_ = val;
        debug
        {
            //log(1);
        }
        assert(!length_ == this.empty);
        debug
        {
            //log(2);
        }
        if(!isLeaf)
        {
            debug
            {
                //log(3);
            }
            
            const arrSize = (universe_ - 1).nextPow2.hSR + 1; 

            debug
            {
                //log(4);
            }

            debug
            {
                assert(ptr_ is null);
                //log(5); 
            }
            
            // reserve enough place for the summary and the children cluster
            ptr_ = (new typeof(this)[arrSize]).ptr;
            
            debug
            {
                //log(6); 
                assert(!(ptr_ is null));
                //log(7); 
                foreach(i; 0 .. arrSize)
                {
                    //log(8); 
                    assert(arr[i].universe == 0);
                    //log(9); 
                }
                //log(10); 
            }
            
            // add the summary with its universe of higher squaure root of the current universe
            summary = typeof(this)((universe_ - 1).nextPow2.hSR); 
            
            debug
            {
                //log(11); 
            }
            // add higher square root children with lower square root universe each.
            foreach(i, ref el; cluster)
            {
                debug
                {
                    //log(12); 
                }
                el = typeof(this)((universe_ - 1).nextPow2.lSR); 
            }
            debug
            {
                //log(13); 
            }
        }

        assert(!length_ == this.empty);
        debug
        {
            debug
            {
                //log(14); 
            }
        }
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
        debug
        {
        }

        // if this node is empty, no successor can be found here or deeper in the tree
        if(this.empty) return NIL; 

        debug
        {
        }

        if(val + 1 >= baseSize) { return NIL; }

        debug
        {
        }
        //if(empty && (val + 1 < baseSize)) return NIL; 
        // create a mask, which hides all lower bits of the stored value up to the given bit number, then apply
        // bit search from the lowest bit. 
        auto maskedVal = value_ & ~((size_t(1) << (val + 1)) - 1); 

        debug
        {
        }

        if(maskedVal != 0) { return maskedVal.bsf; }

        debug
        {
        }

        return NIL; 
    }
    size_t prevImpl(size_t val) @nogc 
    {  
        debug
        {
        }
            
        if(!this.empty && (val != 0))
        {
            debug
            {
            }
            
            /*
            create a mask, which hides all higher bits of the stored value down to the given bit number, then apply
            bit search from the highest bit. 
            */
            auto maskedVal = value_ & ((size_t(1) << val) - 1); 
            debug
            {
            }
            if(maskedVal != 0)
            {
                debug
                {
                }
                return typeof(return)(maskedVal.bsr);
            }
        }
        return NIL;
    }
    bool insertImpl(size_t key) @nogc
    {
        debug
        {
        }
        return length = length + (bts(&value_, key) == 0);
    }

    bool nullifyImpl() @nogc
    {
        value_ = 0; 
        return true; 
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
    in
    {
        assert(value_);
    }
    do
    {
        return bsr(value_); 
    }
    size_t minImpl() const @nogc
    in
    {
        assert(value_);
    }
    do
    {
        return bsf(value_);
    }
    bool length(size_t input) @nogc
    in
    {
        debug
        {
        }
        assert(input < maxSizeBound);
        if(input != length)
        {
            input > length ? assert(input - length == 1) : assert(length - input == 1);
        }
    }
    do
    {
        const retVal = length != input; 
        
        length_ = input;

        if(length_)
        {
            filled_ = true; 
        }
        else
        {
            filled_ = false; 
        }

        return retVal; 
    }

    bool empty() const @nogc
    {
        if(isLeaf) return value_ == 0; 
        return !filled_;
    }

    bool emptyImpl() @nogc 
    {
        return value_ == 0; 
    }
    ref summary() inout
    in
    {
        assert(!isLeaf);
    }
    do
    {
        return arr[0];
    }
    auto cluster() inout
    in
    {
        assert(!isLeaf);
    }
    do
    {
        return arr[1 .. $]; 
    }
    size_t index(size_t x, size_t y) const @nogc
    {
        return .index(universe_, x, y); 
    }
    size_t low(size_t val) const @nogc
    {
        return .low(universe_, val); 
    }
    size_t high(size_t val) const @nogc
    {
        return .high(universe_, val); 
    }
    bool isLeaf() const @nogc 
    {
        return universe_ <= baseSize; 
    }

    size_t value_;
    size_t universe_;
    size_t length_;
    union
    {
        struct 
        {
            mixin(taggedPointer!(
                size_t*, "_",
                bool, "filled_", 1
            ));
        }
        struct 
        {
            typeof(this)* ptr_; 
        }
    }

    package: 
    auto arr() inout
    {
        return ptr_[0 .. (universe_-1).nextPow2.hSR + 1];
    }
    
    auto ref ptr() 
    {
        return cast(typeof(this)*)(cast(size_t)_ & ~size_t(1));
    }
}

private struct VEBtree(Flag!"inclusive" inclusive, alias root)
{
    auto opBinaryRight(string op)(size_t key) @nogc //nothrow 
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

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///
/+ TODO:
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: 1. use case       ", "seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(2UL, baseSize); //set universe size to some integer (small). 
    size_t N = uniform(1UL, M); //set universe size to some integer (small). 
    auto vT = vebRoot(M); 
    assert(vT.empty); 

    size_t[] testArray = M.iota.randomCover.take(N).array; 
    auto cacheArray = new size_t[N]; 
    
    size_t count; 
    
    foreach(i, el; testArray)
    {
        assert(vT.length == count); 
        if(vT.insert(el))
        {
            assert(el in vT); 
            ++count;
            cacheArray[count - 1] = el; 
            assert(vT.min == cacheArray[0 .. count].minElement); 
            assert(vT.max == cacheArray[0 .. count].maxElement); 
        }
    }
    testArray.sort;
    assert(vT().front == testArray.front);  
    assert(vT().back == testArray.back); 
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe);
    assert(vT.length == testArray.length); 
    
    assert(vT() == testArray); 
    assert(vT.capacity == baseSize); 
    assert(vT.universe == M); 
    assert(!vT.empty); 
    foreach(el; testArray)
    {
        assert(el in vT); 
    }
    size_t counter; 
    for(auto el = vT.min; el != vT.max; el = vT.next(el))
    {
        assert(el == testArray[counter]); 
        ++counter; 
    }
    
    for(auto el = vT.max; el != vT.min; el = vT.prev(el))
    {
        
        assert(el == testArray[counter]); 
        --counter; 
    }
    auto secondElementQ = vT.next(testArray[0]); 
    if(secondElementQ != NIL)
    {
        assert(testArray.sort.lowerBound(secondElementQ).length == 1); 
    }
    auto randomElement = testArray[uniform(0UL, testArray.length)]; 
    assert(!vT.insert(randomElement)); 

    auto vTdeepCopy = vT.dup; 
    foreach(el; testArray)
    {
        vT.remove(el); 
    }
    assert(vT.empty); 
    assert(!vT.length);

    assert(vTdeepCopy.length == testArray.length); 
    auto vTdeepCopy2 = vTdeepCopy.dup; 

    vTdeepCopy2.remove(testArray[0]); 
    assert(vTdeepCopy2.length + 1 == testArray.length); 
    auto inclusiveSlice = vTdeepCopy[]; 
    if(0 in vTdeepCopy)
    {
        assert(inclusiveSlice.length == testArray.length + 1); 
    }
    else
    {
        assert(inclusiveSlice.length == testArray.length + 2); 
    }
    auto exclusiveSlice = vTdeepCopy(); 
    assert(exclusiveSlice.length == vTdeepCopy.length); 
    foreach(el; vTdeepCopy)
    {
        trace(el);
        assert(el in vTdeepCopy);
        assert(el in exclusiveSlice);
    }
    foreach(el; exclusiveSlice)
    {
        assert(el in vTdeepCopy); 
    }
    auto shallowCopyFromRoot = vTdeepCopy; 
    assert(!vTdeepCopy.empty); 
    assert(vTdeepCopy.length == vTdeepCopy().length); 
    assert(shallowCopyFromRoot == vTdeepCopy().save); 
    inclusiveSlice = vTdeepCopy[]; 
    auto shallowCopyFromSlice = inclusiveSlice.save;
    assert(inclusiveSlice.front == shallowCopyFromSlice.front);
    inclusiveSlice.popFront; 
    assert(inclusiveSlice.front != shallowCopyFromSlice.front);
    
    if(0 in vTdeepCopy)
    {
        assert(inclusiveSlice.front == vTdeepCopy.next(0));
    }
    else
    {
        assert(inclusiveSlice.front == vTdeepCopy.min); 
    }
    assert(vTdeepCopy() == testArray);
    auto vTdeepCopy3 = vT.dup; 
    assert(vTdeepCopy3 == vT); 
    auto vTshallowCopy = vT; 
    assert(shallowCopyFromRoot.min == vTdeepCopy.min); 
    vTdeepCopy.remove(vTdeepCopy.min); 
    //TODO: assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
    assert(vTshallowCopy == vT);
    assert(vTdeepCopy3 == vT); 
    assert(vT() == vT); 
    assert(vT == vT());
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: 2. use case       ", "seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    
    size_t M = uniform(size_t(baseSize + 1), testedSize); //set universe size to some integer (small). 
    size_t N = uniform(1UL, M < allowedArraySize ? M : allowedArraySize); //set universe size to some integer (small). 
    
    auto vT = vebRoot(M); 
    assert(vT.empty); 
    size_t[] testArray = new size_t[N]; 
    M.iota.randomCover.take(N)
            .enumerate
            .tee!(el => testArray[el.index] = el.value)
            .each!(el => vT.insert(el.value));
    assert(vT.min == testArray.sort.front); 
    assert(vT.max == testArray.sort.back); 
    assert(vT().front == testArray.sort.front);  
    assert(vT().back == testArray.sort.back); 
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe);
    assert(vT.length == testArray.length); 
    foreach(i, el; vT().enumerate)
    {
        assert(el == testArray.sort[i]);
    }
    assert(vT() == testArray);
    assert(vT.capacity == M.nextPow2); 
    assert(vT.universe == M); 
    assert(!vT.empty); 
    testArray.each!(el => assert(el in vT)); 
    size_t counter; 
    for(auto el = vT.min; el != vT.max; el = vT.next(el))
    {
        assert(el == testArray.sort[counter]); 
        ++counter; 
    }
    for(auto el = vT.max; el != vT.min; el = vT.prev(el))
    {
        assert(el == testArray.sort[counter]); 
        --counter; 
    }

    auto secondElementQ = vT.next(testArray.sort[0]); 
    if(secondElementQ != NIL)
    {
        assert(testArray.sort.lowerBound(secondElementQ).length == 1); 
    }

    auto randomElement = testArray[uniform(0UL, testArray.length)]; 
    assert(!vT.insert(randomElement)); 

    auto vTdeepCopy = vT.dup; 
    foreach(el; testArray)
    {
        vT.remove(el); 
    }
    assert(vT.empty); 
    assert(!vT.length);
    assert(vTdeepCopy.length == testArray.length); 

    auto vTdeepCopy2 = vTdeepCopy.dup; 

    vTdeepCopy2.remove(testArray[0]); 
    assert(vTdeepCopy2.length + 1 == testArray.length); 

    auto inclusiveSlice = vTdeepCopy[]; 
    if(0 in vTdeepCopy)
    {
        assert(inclusiveSlice.length == testArray.length + 1); 
    }
    else
    {
        assert(inclusiveSlice.length == testArray.length + 2); 
    }

    auto exclusiveSlice = vTdeepCopy(); 
    assert(exclusiveSlice.length == vTdeepCopy.length); 
    foreach(el; vTdeepCopy)
    {
        assert(el in exclusiveSlice);
    }
    foreach(el; exclusiveSlice)
    {
        assert(el in vTdeepCopy); 
    }
    auto shallowCopyFromRoot = vTdeepCopy; 
    assert(shallowCopyFromRoot == vTdeepCopy().save); 
    inclusiveSlice = vTdeepCopy[]; 
    auto shallowCopyFromSlice = inclusiveSlice.save;
    assert(inclusiveSlice.front == shallowCopyFromSlice.front);
    inclusiveSlice.popFront; 
    assert(inclusiveSlice.front != shallowCopyFromSlice.front);
    
    if(0 in vTdeepCopy)
    {
        assert(inclusiveSlice.front == vTdeepCopy.next(0));
    }
    else
    {
        assert(inclusiveSlice.front == vTdeepCopy.min); 
    }
    
    assert(vTdeepCopy() == testArray);
    auto vTdeepCopy3 = vT.dup; 
    auto vTshallowCopy = vT; 
    assert(shallowCopyFromRoot.min == vTdeepCopy.min); 
    vTdeepCopy.remove(vTdeepCopy.min); 
    assert(shallowCopyFromRoot.min == vTdeepCopy.min); 
 
    assert(vTshallowCopy == vT);
    assert(vTdeepCopy3 == vT); 

    assert(vT() == vT); 
    assert(vT == vT());
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
    trace("UT: vN, opBinaryIn    ", "seed: ", currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator

    auto value = uniform(0UL, size_t.max);
    auto bitNum = uniform(0UL, baseSize);
    auto vN = vebRoot(baseSize); 
    vN.value_ = value; 
    
    if((vN.value_ & size_t(1) << bitNum) != 0 ) 
    {
        assert(bitNum in vN); 
    }

    if((vN.value_ & size_t(1) << bitNum) == 0 )
    {
        assert(!(bitNum in vN)); 
    }
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: vN, predecessor   ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    auto v = uniform(2UL, testedSize); //set universe size to some integer. 
    auto x = uniform(1UL, baseSize);
    auto vN = vebRoot(baseSize); 
    vN.value_ = v; 

    bool found; 

    for(size_t index = x - 1; index >= 0; --index)
    {
        if (v & (size_t(1) << index)) 
        {
            found = true; 
            assert(!vN.empty);
            assert(vN.prev(x) == index); 
            break; 
        }
        if(!index) break; 
    }

    if(!found) assert(vN.prev(x) == NIL); 
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: vN, successor     ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    auto v = uniform(0UL, size_t.max); //set universe size to some integer. 
    auto x = uniform(0UL, baseSize);
    auto vN = vebRoot(baseSize); 
    vN.value_ = v; 
    bool found; 

    for (size_t index = x + 1; index < baseSize; ++index)
    {
        if (v & (size_t(1) << index)) 
        {
            found = true; 
            assert(vN.next(x) == index); 
            break; 
        }
    }
    if(!found) assert(vN.next(x) == NIL);
}
+/
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///
/+ TODO: 
unittest
{
    auto vN = vebRoot(baseSize); 
    assert(vN.empty); 
    assert(vN.isLeaf); 
    assert(vN.empty); 
    vN.value_ = 3; 
    assert(vN.min == 0);
    assert(1 in vN);
    assert(!(2 in vN));
    assert(vN.isLeaf);
    assert(vN.empty); 
    assert(vN.value_ == 0); 
}
+/

///
/+ TODO: 
unittest
{
    
    auto vT = vebRoot(100); 
    assert(vT.empty);
    auto result = vT.insert(2); 
    
    assert(result); 
    assert(!vT.empty); 
    assert(2 in vT);
    assert(vT.length == 1);      
    
    auto vT2 = vT;
    auto vT3 = vT.dup; 
    assert(2 in vT2);
    assert(vT2.length == 1); 
    auto result2 = vT2.insert(3);
    assert(vT2.length == 2);
    assert(result2); 
    assert(3 in vT2); 
    assert(3 in vT);
    assert(!(3 in vT3));
    assert(vT2.length == 2);
    
}
+/

///
/+ TODO: 
unittest
{
    
    auto currentSeed = unpredictableSeed();
    trace("UT: vT, [], ()        ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator

    size_t M = uniform(2UL,testedSize); //set universe size to some integer. 
    auto vT = vebRoot(M); //create the tree
    assert(M.iota.map!(i => vT.insert(uniform(0UL, vT.universe))).sum == vT.length); 
    
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe); 
    
}
+/

///
/+ TODO: 
unittest
{
    auto p = vebRoot(100); 
    assert(p.empty); 
    p.insert(5); 
    p.insert(100); 
    assert(!p.empty); 
    assert(p.next(0) == 5); 
    assert(p.next(4) == 5); 
    assert(p.next(5) == 100); 
    auto s = p[]; 
    assert(s.front == 0); 
    assert(p.min == 5); 
    s.popFront; 
    assert(!s.empty); 
    assert(s.front == 5); 
    s.popFront; 
    assert(s.front == 100); 
    s.popFront; 
    assert(s.empty); 

    auto pp = vebRoot(100);
    assert(pp.empty); 
    pp.insert(5); 
    assert(!pp.empty); 
    assert(pp.next(0) == 5); 
    assert(pp.next(4) == 5); 
    assert(pp.next(5) == NIL);
    assert(pp[].next(5) == 100); 
    auto ss = pp(); 
    assert(ss.front == 5); 
    ss.popFront; 
    assert(ss.empty); 
    assert(ss.front == NIL); 
}
+/

///
/+ TODO: 
unittest
{
    
    auto vT = vebRoot(1000); 
    assert(vT.capacity == 1024); 
    assert(vT.min == NIL); 
    assert(vT.insert(2)); 
    assert(vT.insert(5));
    assert(!(8 in vT)); 
    assert(vT.insert(88));
    assert(88 in vT); 
    assert(vT.prev(4) == 2);
    assert(!(8 in vT)); 
    assert(vT.insert(8)); 
    assert(8 in vT); 
    assert(vT.prev(75) == 8); 
    
    assert(vT.prev(90) == 88); 
    
    assert(vT.prev(7) == 5); 
    assert(vT.prev(4) == 2); 
    assert(vT.prev(2) == NIL); 
    
    //TODO: reactivate this by slicing assert(vT[].prev(2) == 0); 
    
    assert(vT.prev(2) == NIL); 
    
    assert(vT.next(6) == 8); 
    assert(vT.next(5) == 8); 
    
    assert(vT.next(4) == 5); 
    assert(vT.next(1) == 2); 
    assert(vT.next(75) == 88); 
    assert(vT.next(90) == NIL); 
    //TODO: reactivate this by slicing assert(vT[].next(90) == vT.universe);
    
    assert(!(1029 in vT)); 
    
    assert(vT.next(1025) == NIL);
    assert(vT.next(1025) == NIL);
    
    auto vT2 = vebRoot(500); 
    assert(vT2.empty); 
    vT2.insert(50); 
    vT2.insert(500); 
    assert(vT2.max == 500); 
    assert(vT2.min == 50); 
    assert(vT2.next(40) == 50);
    assert(vT2.next(50) == 500); 
    
    vT2 = vebRoot(500); 
    assert(vT2.empty); 
    vT2.insert(50); 
    vT2.insert(500); 
    assert(vT2.max == 500); 
    assert(vT2.min == 50); 
    assert(vT2.next(40) == 50);
    assert(vT2.next(50) == 500); 

    /* about 20 seconds in debug mode. 
    auto vT3 = vebRoot(halfSizeT.max);
    assert(vT3.insert(5)); 
    assert(vT3.member(5));
    assert(vT3.capacity == cast(ulong)halfSizeT.max + 1UL);
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
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: rand, succ        ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator

    size_t M = uniform(2UL,testedSize); //set universe size to some integer. 
    auto vT = vebRoot(M); //create the tree
    assert(vT.capacity == (M-1).nextPow2); 

    auto filled = M.iota.map!(i => vT.insert(uniform(0UL, vT.universe))).sum; 
    assert(filled == vT.length); 

    size_t n; 
    auto i = vT.max; 

    // discover the thousend (or little less) values with the predecessor method
    while(i != NIL)
    {
        ++n;
        i = vT.prev(i); 
        if(n > filled) break; 
    }
    
    size_t o;
    i = vT.min; 
    while(i != NIL)
    {
        ++o; 
        i = vT.next(i);
        if(o - 1 > filled) break; 
    }
    
    // assert, that all members are discovered, iff when no predecessors are left
    assert(n == filled); 
    assert(o == filled); 
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed(); 
    trace("UT: rand, pred        ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(2UL, testedSize); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    assert(M.iota.map!(i => vT.insert(uniform(0UL, vT.universe))).sum == vT.length); 
    auto i = vT.max; 

    // remove all members beginning from the maximum
    bool result; 
    while(i != NIL)
    {
        result = vT.remove(i); 
        assert(result); 
        auto j = vT.prev(i); 
        if(j != NIL)
            assert(j != i); 
        i = j; 
    }
    
    // assert, that all members are removed, iff when no predecessors are left. 
    assert(vT.empty); 
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed(); 
    trace("UT: rand, remove      ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(2UL, testedSize); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    assert(M.iota.map!(i => vT.insert(uniform(0UL, vT.universe))).sum == vT.length); 
    auto i = vT.min;
    
    // remove all members beginning from the minimum
    bool result; 
    while(i != NIL)
    {        
        result = vT.remove(i); 
        assert(result); 
        auto j = vT.next(i); 
        if(j != NIL)
            assert(j != i); 
        i = j; 
    } 

    // assert, that all members are removed, iff when no successors are left.
    assert(vT.empty); 
}
+/

///
/+ TODO: 
unittest
{
    size_t M = testedSize; 
    auto vT = vebRoot(M); 
    vT.insert(0x000f); 
    assert(vT.prev(0x000f) == NIL);
    vT.insert(0x00f0);
    assert(vT.prev(0x00f0) == 0x000f); 
    vT.insert(0x0f00); 
    assert(vT.prev(0x0f00) == 0x00f0); 
    vT.insert(0xf000); 
    assert(vT.prev(0xf000) == 0x0f00);
    
    auto result = vT.remove(0xf000); 
    assert(result); 
    assert(vT.prev(0xf000) == 0x0f00);
    result = vT.remove(0x0f00); 
    assert(result); 
    assert(vT.prev(0x0f00) == 0x00f0); 
    result = vT.remove(0x00f0); 
    assert(result); 
    assert(vT.prev(0x00f0) == 0x000f); 
    result = vT.remove(0x000f); 
    assert(result); 
    assert(vT.prev(0x000f) == NIL);
}
+/

///
/+ TODO: 
unittest
{
    size_t M = testedSize; 
    auto vT = vebRoot(M); 
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
+/

/// 
/+ TODO: 
unittest
{
    //stress test
    auto currentSeed = unpredictableSeed(); 
    trace("UT: rand, stress      ","seed: ", currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    // last test says: see below. 
    size_t M = uniform(2UL, allowedArraySize); // set universe size to some integer. 
    auto vT = vebRoot(M); 

    size_t[] arr; 
    arr.length = 31 * vT.capacity/typeof(vT).sizeof; 
    (vT.capacity - 1).iota.randomCover.take(arr.length)
            .enumerate
            .tee!(el => arr[el.index] = el.value)
            .each!(el => vT.insert(el.value));
    
    auto vT2 = vebRoot(M); 
    
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
        TODO: this part is for speed test
    */
    /*
        compiled with ldc2 vebtree.d -O -main -unittest
        results of stress tests: 
            size of tree: 16777216
            howMuchFilled: 16252928
            VEB: 2 secs, 382 ms, 588 μs, and 8 hnsecs
    */
    /*

    //auto r = benchmark!(fill1, fill2)(1); 
    auto r = benchmark!(fill1)(1); 
    
    auto f0Result = to!Duration(r[0]); 
    //auto f1Result = to!Duration(r[1]); 
    //assert(f0Result < f1Result); 
    //*/
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed(); 
    trace("UT: rand, member      ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(2UL, testedSize); // set universe size to some integer.
    size_t[] sourceArr; 
    sourceArr.length = M; 
    // generate a random array as the source for the tree
    M.iota.each!(i => sourceArr[i] = uniform(0UL, M));
    // make the array values unique. 
    auto uniqueArr = sourceArr.sort.uniq;
    // constructor to test
    auto vT = vebRoot(sourceArr.length); 
    uniqueArr.each!(el => vT.insert(el)); 
    // check, that all values are filled 
    bool result;
    foreach(i; uniqueArr)
    {
        assert(i in vT); 
        result = vT.remove(i); 
        assert(result); 
    }
    // check, that no other elements are present. 
    assert(vT.empty); 
}
+/

///
/+ TODO: 
unittest
{
    auto currentSeed = unpredictableSeed();
    trace("UT: rand, opSlice     ","seed: ", currentSeed); 
    rndGen.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 16", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    size_t M = uniform(2UL, allowedArraySize); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    size_t[] arr; 
    arr.length = 16 * vT.capacity/typeof(vT).sizeof; 
    (vT.capacity - 1).iota.randomCover.take(arr.length)
            .enumerate
            .tee!(el => arr[el.index] = el.value)
            .each!(el => vT.insert(el.value));

    assert(setSymmetricDifference(vT(), arr.sort).empty); 
}
+/

///
/+ TODO: 
unittest
{
    auto vT = vebRoot(14);
    auto result = vT.insert(2); 
    assert(result); 
    result = vT.insert(5); 
    assert(result);
    result = vT.insert(10); 
    assert(result);
    assert(vT[] == [0, 2, 5, 10, 14]); 
    assert(vT() == [2, 5, 10]); 
}
+/

///
/+
unittest
{
    /*
    //another stress test
    auto currentSeed = unpredictableSeed(); 
    trace("UT: stress test 2  ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    
    void fill16(){ auto vT = vebRoot(1 << 16); }
    void fill17(){ auto vT = vebRoot(1 << 17); }
    void fill18(){ auto vT = vebRoot(1 << 18); }
    void fill19(){ auto vT = vebRoot(1 << 19); }    
    void fill20(){ auto vT = vebRoot(1 << 20); }
    void fill21(){ auto vT = vebRoot(1 << 21); }
    void fill22(){ auto vT = vebRoot(1 << 22); }
    void fill23(){ auto vT = vebRoot(1 << 23); }
    void fill24(){ auto vT = vebRoot(1 << 24); }
    void fill25(){ auto vT = vebRoot(1 << 25); }
    void fill26(){ auto vT = vebRoot(1 << 26); }
    void fill27(){ auto vT = vebRoot(1 << 27); }
    void fill28(){ auto vT = vebRoot(1 << 28); }
    void fill29(){ auto vT = vebRoot(1 << 29); }
    void fill30(){ auto vT = vebRoot(1 << 30); }
    
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
    
    trace("VEB with M of ", 1 << 16, ": ", f16Result); 
    trace("VEB with M of ", 1 << 17, ": ", f17Result);
    trace("VEB with M of ", 1 << 18, ": ", f18Result);
    trace("VEB with M of ", 1 << 19, ": ", f19Result);
    trace("VEB with M of ", 1 << 20, ": ", f20Result);
    trace("VEB with M of ", 1 << 21, ": ", f21Result);
    trace("VEB with M of ", 1 << 22, ": ", f22Result);
    trace("VEB with M of ", 1 << 23, ": ", f23Result);
    trace("VEB with M of ", 1 << 24, ": ", f24Result);
    trace("VEB with M of ", 1 << 25, ": ", f25Result); 
    trace("VEB with M of ", 1 << 26, ": ", f26Result); 
    trace("VEB with M of ", 1 << 27, ": ", f27Result); 
    trace("VEB with M of ", 1 << 28, ": ", f28Result); 
    trace("VEB with M of ", 1 << 29, ": ", f29Result); 
    trace("VEB with M of ", 1 << 30, ": ", f30Result); 
    //*/
}
+/

///
/+ TODO: 
unittest
{
    //stress test
    auto currentSeed = unpredictableSeed(); 
    trace("UT: rand, ranges      ","seed: ", currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    // last test says: see below. 
    size_t M = uniform(2UL, testedSize); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    /*testing the range methods*/
    assert(vT.empty); 
    
    size_t[] sourceArr; 
    sourceArr.length = uniform(2UL, M); 
    sourceArr.length.iota.each!(i => sourceArr[i] = uniform(0UL, sourceArr.length));
    
    auto uniqueArr = sourceArr.sort.uniq; 

    // constructor to test

    auto vTnew = vebRoot(sourceArr.length); 
    uniqueArr.each!(el => vTnew.insert(el)); 

    assert(!vTnew.empty); 
    assert(vTnew.length == uniqueArr.walkLength); 
    auto vT2 = vTnew; 
    auto slice = vTnew(); 
    assert(slice.front == uniqueArr.front); 
    assert(vTnew() == uniqueArr); 
    assert(!vTnew.empty);
    assert(!vT2.empty);

    size_t N = 100; 
    auto vT3 = vebRoot(N); 
    assert(vT3.empty); 
    auto unique3 = N.iota.map!(i => uniform(0UL, N)).array.sort.uniq.array;
    unique3.each!(u => vT3.insert(u));
    unique3.each!(u => assert(u in vT3));
    assert(vT3.length == unique3.length); 
    auto sl3 = vT3[]; 
    
    if(unique3.front == 0 && unique3.back == vT3.universe)
    {
        assert(sl3.length == unique3.length);
    }
    else if(unique3.front == 0 || unique3.back == vT3.universe)
    {
        assert(sl3.length == unique3.length + 1);
    }
    else
    {
        assert(sl3.length == unique3.length + 2);
    }
    assert(sl3.length); 
    assert(!sl3.empty); 

    unique3.each!(u => vT3.remove(u));
    assert(vT3.empty); 
    
    //* Works. Duration in debug mode: about 35 seconds. 
    //auto vTT = vebRoot((size_t(1) << 27) - 1); 
    //assert(vTT.insert(42)); 
    //assert(42 in vTT);
    //*/
}
+/