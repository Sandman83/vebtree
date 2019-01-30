module vebtree.vebroot;
import vebtree;
import core.bitop;
import std.traits : ReturnType, isIterable, arity;
import std.typecons : Flag, Yes, No;
public import std.math : nextPow2;
public import core.stdc.limits : CHAR_BIT;

debug public import std.format : format;

version (unittest)
{
    import std.range;
    //import std.random;
    import std.format;
    import std.conv : to;
    import std.container; // red black tree may be used in unittests for comparison.
    import std.math : sqrt;
    public import std.random;

    // helping function for output a given value in binary representation
    void bin(size_t n)
    {
        /* step 1 */
        if (n > 1)
            bin(n / 2);
        /* step 2 */
        import core.stdc.stdio : printf;

        printf("%d", n % 2);
    }

    /// precalculated powers of two table for unit testing
    import std.range : iota;
    import std.algorithm.iteration : map;

    enum powersOfTwo = (CHAR_BIT * size_t.sizeof).iota.map!(a => size_t(1) << a);
    enum testMultiplier = 1; //16

    ///
    /*
    static assert(!isInputRange!(ReturnType!(vebRoot!(CHAR_BIT * size_t.sizeof))));
    static assert(isIterable!(ReturnType!(vebRoot!(CHAR_BIT * size_t.sizeof))));
    static assert(isInputRange!(ReturnType!(vebRoot!(CHAR_BIT * size_t.sizeof))[]));
    static assert(isBidirectionalRange!(ReturnType!(vebRoot!(CHAR_BIT * size_t.sizeof))[]));
    static assert(!is(typeof(vebRoot(4)[2])));
    */

    auto generateVEBtree(size_t baseSize)(uint currentSeed, size_t min, size_t max, ref size_t M)
    {
        static assert(baseSize > 1);
        static assert((baseSize & (baseSize - 1)) == 0);
        assert(min >= 2);
        rndGen.seed(currentSeed); //initialize the random generator
        M = uniform(min, max + 1); // parameter for construction
        return vebRoot!baseSize(M);
    }
    string generateDebugString(string identifier1, size_t identifier2, size_t baseSize, uint currentSeed, size_t M)
    {
        return format!"%s: %d baseSize: %d; seed: %d M: %d"(identifier1, identifier2, baseSize, currentSeed, M);
    }
}

package:
// bit mask representing uint.max. 
enum size_t lowerMask = size_t.max >> (size_t.sizeof * CHAR_BIT / 2);
// bit mask representing size_t.max without uint.max. 
enum size_t higherMask = size_t.max ^ lowerMask;

/*
This function returns the higher square root of the given input. It is needed in the initialization step 
of the VEB tree to calculate the number of children of a given layer. And this is the universe size of the
summary of a node. The upper square root is defined by 2^{\lceil(\lg u)/2\rceil}
*/
size_t hSR(size_t val) @nogc
{
    return size_t(1) << (bsr(val) / 2 + ((val.bsr & 1) || ((val != 0) && (val & (val - 1)))));
}
//
unittest
{

    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: hSR. seed: %d"(currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL, uint.max); //set universe size to some integer. 
    auto hSR = hSR(M);
    assert((hSR & (hSR - 1)) == 0, errorString);
    import std.range : array;
    import std.algorithm.searching : until;

    auto check = powersOfTwo.until(hSR).array;
    assert((check[$ - 1]) * (check[$ - 1]) < M, errorString);
}

/*
This function returns the lower square root of the given input. It is needed by the indexing functions
high(x), low(x) and index(x,y) of elements in the tree. Also, this is the universe size of a child of a node. The
lower square root is defined by 2^{\lfloor(\lgu)/2\rfloor}
*/
size_t lSR(size_t val) @nogc
{
    return size_t(1) << (bsr(val) / 2);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: lSR               seed: %d"(currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    const M = uniform(1UL, uint.max); //set universe size to some integer. 
    auto lSR = M.lSR;

    assert((lSR & (lSR - 1)) == 0, errorString);
    assert(lSR * lSR < M, errorString);
    import std.algorithm.searching : find;

    assert(!powersOfTwo.find(lSR).empty);
}

/*
This is an index function defined as \lfloor x/lSR(u)\rfloor. It is needed to find the appropriate cluster
of a element in the tree. It is a part of the ideal indexing function.
*/
size_t high(size_t universe, size_t val) @nogc
out (result; result == val / universe.lSR) // bithacks = keithschwarz
{
    return val >> (bsr(universe) / 2);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: high              seed: %d"(currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    const M = uniform(1UL, uint.max); //set universe size to some integer. 
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
size_t low(size_t universe, size_t val) @nogc
out (retVal; retVal == (val & ((size_t(1) << (bsr(universe) / 2)) - 1)))
{
    return val % universe.lSR;
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: low               seed: %d"(currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    size_t M = uniform(1UL, uint.max); //set universe size to some integer. 
    size_t U = nextPow2(M);
    auto x = uniform(0UL, U);
    assert(low(U, x) == (x & (U.lSR - 1)), errorString);
}

/*
This is an index function to retain the searched value. It is defined as x * lSR(u) + y. Beyond this, the
relation holds: x = index(high(x), x.low). This is the ideal indexing function of the tree. 
*/
size_t index(size_t universe, size_t x, size_t y) @nogc
{
    return (x * universe.lSR + y);
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    const errorString = format!"UT: index             seed: %d"(currentSeed);
    rndGen.seed(currentSeed); //initialize the random generator
    const M = uniform(0UL, uint.max); //set universe size to some integer. 
    size_t U = M.nextPow2;
    auto x = uniform(0UL, U);
    assert(index(U, U.high(x), U.low(x)) == x, errorString);
}

auto vebTree(Flag!"inclusive" inclusive, alias root, Args...)(Args args)
{
    static if(Args.length)
    {
        auto retVal = VEBtree!(inclusive, root)(args[0], args[1], args[2]);
    }
    else
    {
        auto retVal = VEBtree!(inclusive, root)(root.min, root.max, root.length);
    }

    return retVal;
}

static foreach (_; 1 .. size_t.sizeof - 1)
{
    unittest
    {
        import std.parallelism : parallel;

        enum baseSize = 1 << _;
        foreach (b; (CHAR_BIT * size_t.sizeof * testMultiplier).iota.parallel)
        {
            auto currentSeed = unpredictableSeed();
            size_t M;

            auto vT = generateVEBtree!(1 << _)(currentSeed, 2UL, baseSize, M);
            assert(vT.universe == M);  
            const errorString = generateDebugString("UT: white box test: ", b, baseSize, currentSeed, M);

            assert(vT.value_ == 0, errorString);
            if (vT.isLeaf)
            {
                assert(vT.ptr_ is null, errorString);
                assert(vT.capacity == baseSize, errorString);
            }
            else
            {
                assert(!(vT.ptr_ is null), errorString);
                assert(vT.capacity == (vT.universe - 1).nextPow2, errorString);
            }

            assert(vT.empty == true, errorString);
            assert(vT.min == NIL, errorString);
            assert(vT.max == NIL, errorString);
            assert(vT[].front == 0, errorString);
            assert(vT[].back == vT.universe, errorString);
            assert(vT().front == NIL, errorString);
            assert(vT().back == NIL, errorString);
            assert(vT.length == 0, errorString);
            assert(vT.universe == M, errorString);

            size_t N = uniform(0UL, 2 * M); // independent parameter for testing
            // make an array of length N
            size_t[] testArray, cacheArray;
            testArray = new size_t[N];
            cacheArray.reserve(N);
            // fill the array with all possible values 
            foreach (ref el; testArray)
            {
                el = (2 * M).iota.choice;
            }

            foreach (testNumber; testArray)
            {
                assert(vT.universe == M, errorString);
                const insertResult = vT.insert(testNumber);

                if (insertResult)
                {
                    assert(!vT.empty, errorString);
                    cacheArray ~= testNumber;
                }
            }

            import std.algorithm.sorting : sort;

            cacheArray.sort;

            if (cacheArray.empty)
            {
                assert(vT.empty, errorString);
            }
            else
            {
                assert(!vT.empty, errorString);
            }

            foreach (el; cacheArray)
            {
                assert(bt(&vT.value_, el), errorString);
            }
            import std.algorithm.iteration : uniq;
            import std.algorithm.searching : count;

            assert(vT.length == cacheArray.uniq.count, errorString);
            assert(vT.universe == M, errorString);
            if (cacheArray.length)
            {
                assert(vT.min == cacheArray.front, errorString);
                assert(vT.max == cacheArray.back, errorString);
            }
            else
            {
                assert(vT.min == NIL, errorString);
                assert(vT.max == NIL, errorString);
            }

            auto currElement = vT.min;
            foreach (el; cacheArray.uniq)
            {
                assert(currElement == el, errorString);
                currElement = vT.next(currElement);
            }
            currElement = vT.max;
            foreach (el; cacheArray.uniq.array.retro)
            {
                assert(currElement == el, errorString);
                currElement = vT.prev(currElement);
            }

            foreach (key; 0 .. vT.universe)
            {
                import std.algorithm.searching : canFind;

                if (cacheArray.uniq.array.canFind(key))
                {
                    assert(key in vT, errorString);
                }
                else
                {
                    assert(!(key in vT), errorString);
                }
            }
            auto deepCopy = vT.dup;

            assert(deepCopy.value_ == vT.value_, errorString);
            assert(vT == cacheArray.uniq, errorString);
            assert(vT.prev(vT.min) == NIL, errorString);
            assert(vT.next(vT.max) == NIL, errorString);
            assert(vT == deepCopy, errorString);
            assert(vT == deepCopy(), errorString);

            if (cacheArray.length)
            {
                auto val = cacheArray.uniq.array.randomCover.front;
                vT.removeImpl(val);
                assert((deepCopy.value_ ^ vT.value_) == (size_t(1) << val), errorString);
                import std.algorithm.iteration : each;
                import std.algorithm.searching : count, find;
                import std.algorithm.mutation : remove;

                cacheArray.count(val).iota.each!(i => cacheArray = cacheArray.remove(
                        cacheArray.length - cacheArray.find(val).length));
            }
            else
            {
                assert((deepCopy.value_ ^ vT.value_) == 0, errorString);
            }

            foreach (key; 0 .. vT.capacity)
            {
                import std.algorithm.searching : canFind;

                if (cacheArray.uniq.array.canFind(key))
                {
                    assert(vT.removeImpl(key), errorString);
                }
                else
                {
                    assert(!(vT.removeImpl(key)), errorString);
                }
            }
            assert(vT.value_ == 0, errorString);
            assert(vT.empty, errorString);
        }
    }
}

/**
define the absence of a key to be -1. 
*/
enum NIL = ptrdiff_t(-1);

/**
A van Emde Boas node implementation
*/
struct VEBroot(size_t baseSize)
{
    invariant
    {
        if (!(ptr_ is null))
        {
            assert(universe_ >= 2);
        }
        if (universe_ <= baseSize)
        {
            assert(this.capacity == baseSize);
            assert(ptr_ is null);
        }
    }

    /**
    the maxSizeBound defines the maximum the tree can be constructed with. It is parametrized on the size of size_t and
    changes dynamically with the architecture used. 
    */
    enum maxSizeBound = size_t(1) << (CHAR_BIT * size_t.sizeof / 2); // == uint.max + 1 on a 64-bit system

    size_t toHash() const nothrow { assert(0); }

    /**
    yields a deep copy of the node. I. e. copies all data in children and allocates another tree 
    */
    typeof(this) dup()
    {
        auto retVal = typeof(this)(universe_);
        foreach (el; opCall())
            retVal.insert(el);
        return retVal;
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
    Equality operator checks for any iterable, whether in contains the same values, as the current tree. 
    */
    bool opEquals(T)(auto ref T input) const if (isIterable!T)
    {
        static if (hasLength!T)
        {
            if (length != input.length)
                return false;
        }

        size_t currentElem = this.min;

        foreach (el; input)
        {
            if (el != currentElem)
                return false;
            currentElem = this.next(currentElem);
        }

        return true;
    }

    /**
    member method for the case universe size < base size. Overloads by passing only one parameter, which is
    the bit number of interest. Returns whether the appropriate bit inside the bitvector is set.
    */
    bool opBinaryRight(string op)(size_t key) @nogc if (op == "in")
    in
    {
        if (!(ptr_ is null))
            assert(universe_ >= 2);
        if(isLeaf)
            assert(key < baseSize);
    }
    do
    {
        if (key >= this.capacity)
            return false;

        if (this.empty) // if an empty intermediate node is found, nothing is stored below it. 
            return false;

        if (this.isLeaf)
            return bt(&value_, key) != 0;
        else
        {
            // case of a single valued range. 
            if (key == this.min || key == this.max)
                return true;

            /*
                else we have to descend, using the recursive indexing: 
                1. take the high(value, uS)-th child and 
                2. ask it about the reduced low(value, uS) value
                3. use the lSR(uS) universe size of the childe node. 
            */
            return low(key) in ptr_[high(key)];
        }
    }

    /**
    the opApply method grants the correct foreach behavior, nogc version
    */
    int opApply(scope int delegate(ref size_t) @nogc operations) const @nogc
    {
        return opApplyImpl(operations);
    }
    
    /**
    ditto
    */
    int opApply(scope int delegate(ref size_t, ref size_t) @nogc operations) const @nogc
    {
        return opApplyImpl(operations);
    }

    /**
    ditto
    */
    int opApply(scope int delegate(ref size_t) operations) const 
    {
        return opApplyImpl(operations);
    }

    /**
    ditto
    */
    int opApply(scope int delegate(ref size_t, ref size_t) operations) const 
    {
        return opApplyImpl(operations);
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
    
    @disable this(this); 

    this(size_t val)
    in(val >= 2)
    {
        universe_ = val;
        setEmpty;
        
        assert(!length_ == this.empty);

        if (!isLeaf)
        {
            assert(this.capacity == (universe_ - 1).nextPow2);
            const arrSize = this.capacity.hSR + 1;
            
            // reserve enough place for the summary and the children cluster
            ptr_ = (new typeof(this)[arrSize]).ptr;

            // add higher square root children with lower square root universe each.
            foreach (i, ref el; ptr_[0 .. this.capacity.hSR])
                el = typeof(this)(this.capacity.lSR);

            // add the summary with its universe of higher squaure root of the current universe
            ptr_[this.capacity.hSR] = typeof(this)(this.capacity.hSR);
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

    /**
    This yields whether the node is a leaf node.
    */
    bool isLeaf() const @nogc
    {
        return universe_ <= baseSize;
    }

    package:
    /*
    yields the next power of two, based un universe size
    */
    size_t capacityImpl() const @nogc
    {
        return baseSize;
    }

    /*
    remove method. this method is called from class with a universe size given. It performs recursion calls untill
    the universe size is reduced to the base size. Then the overloaded remove method is called. 
    */
    bool removeImpl(size_t key) @nogc
    {
        return length = length - (btr(&value_, key) != 0);
    }
    
    /*
    successor method. this method is called from class with a universe size given. It performs recursion calls until
    the universe size is reduced to the base size. Then the overloaded successor method is called. 
    */
    size_t nextImpl(size_t val) const @nogc
    {
        // if this node is empty, no successor can be found here or deeper in the tree
        if (emptyImpl)
            return NIL;

        if (val + 1 >= baseSize)
            return NIL;

        // create a mask, which hides all lower bits of the stored value up to the given bit number, then apply
        // bit search from the lowest bit. 
        auto maskedVal = value_ & ~((size_t(1) << (val + 1)) - 1);
        
        if (maskedVal != 0)
            return maskedVal.bsf;

        return NIL;
    }

    size_t prevImpl(size_t val) @nogc
    {
        if (!this.empty && (val != 0))
        {
            /*
            create a mask, which hides all higher bits of the stored value down to the given bit number, then apply
            bit search from the highest bit. 
            */
            auto maskedVal = value_ & ((size_t(1) << val) - 1);

            if (maskedVal != 0)
                return typeof(return)(maskedVal.bsr);
        }
        return NIL;
    }

    bool insertImpl(size_t key) @nogc
    {
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
        if (value_ == 0)
            return NIL;
        return bsr(value_);
    }

    size_t minImpl() const @nogc
    {
        if (value_ == 0)
            return NIL;
        return bsf(value_);
    }

    bool length(size_t input) @nogc
    in
    {
        assert(input <= this.capacity);

        if (input != length)
        {
            input > length ? assert(input - length == 1) : assert(length - input == 1);
        }
    }
    do
    {
        const retVal = length != input;

        length_ = input;

        if (!length_)
            setEmpty;

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

    size_t value_;
    size_t universe_;
    size_t length_;
    typeof(this)* ptr_;

    private:
    // The empty setter of a node. This function is kept for consistency in this module. 
    pragma(inline, true) void setEmpty() @nogc
    {
        value_ = isLeaf ? 0 : -NIL;
    }

    // with the trick of https://forum.dlang.org/thread/erznqknpyxzxqivawnix@forum.dlang.org
    int opApplyImpl(O)(O operations) const
    {
        int result;
        size_t leading = this.min;

        //for(size_t leading = min; leading < max; leading = this.next(leading)) 

        for (size_t i = 0; i < length; ++i)
        {
            static if (arity!operations == 1)
                result = operations(leading);
            else static if (arity!operations == 2)
                result = operations(i, leading);
            else 
                assert(0); 

            if (result)
                break;

            leading = this.next(leading);
        }

        return result;
    }
}

private struct VEBtree(Flag!"inclusive" inclusive, alias root)
{
    @disable this(); 

    this(ptrdiff_t min, ptrdiff_t max, size_t length_)
    {
        length = length_; 

        static if (inclusive)
        {
            if(!length)
            {
                backKey = root.universe; 
                length = 2; 
            }
            else
            {
                if(min > 0)
                {
                    ++length;  
                }

                if(max <= root.universe)
                {
                    backKey = root.universe; 
                    ++length; 
                }
                else if(max <= root.capacity)
                {
                    backKey = root.capacity; 
                    ++length; 
                }
                else
                {
                    debug
                    {
                        assert(max == root.universe || max == -1, format!"max: %d\n"(max));
                    }
                    else
                    {
                        assert(0); 
                    }
                }
            }
        }
        else
        {
            frontKey = min;
            backKey = max;
        }
    }
    auto opBinaryRight(string op)(size_t key) @nogc if (op == "in")
    {
        return key in root;
    }

    static if (inclusive)
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
    in(!empty)
    {
        --length;
        frontKey = next(frontKey);
    }

    typeof(backKey) back() @nogc
    {
        return backKey;
    }

    void popBack()
    in(length)
    {
        --length;
        backKey = prev(backKey);
    }

    auto prev(size_t key) @nogc
    {
        const pred = root.prev(key);
        static if (inclusive)
            return pred == NIL ? 0 : pred;
        else
            return pred;
    }

    auto next(size_t key) @nogc
    {
        const succ = root.next(key);
        
        static if(inclusive)
            debug
                if (succ == NIL)
                    assert(length <= 1, format!"key: %d, length: %d\n"(key, length)); 
        
        static if (inclusive)
            if (succ == NIL)    
               return backKey;
            else
                return succ;
        else
            return succ;
    }

    bool empty() @nogc
    {
        return !length;
    }

    auto save() const
    {
        return vebTree!(inclusive, root)(frontKey, backKey, length);
    }

    size_t toHash() const nothrow { assert(0); }

    /**
    for comparison with an iterable, the iterable will be iterated, as the current object.
    */
    bool opEquals(T)(auto ref T input) const if (isIterable!T)
    {
        static if (is(T == typeof(this)))
            return root == input.root;

        static if (hasLength!T)
            if (length != input.length)
                return false;

        auto copy = this.save;

        foreach (el; input)
        {
            if (el != copy.front)
                return false;
            copy.popFront();
        }

        return true;
    }
}