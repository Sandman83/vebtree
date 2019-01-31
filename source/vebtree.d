/**
Copyright: Copyright (c) 2016- Alexander Orlov. All rights reserved.
License: $(LINK2 https://opensource.org/licenses/MIT, MIT License).
Authors: Alexander Orlov, $(LINK2 mailto:sascha.orlov@gmail.com, sascha.orlov@gmail.com) 
*/

/**
This module implements a Van Emde Boas tree container.
All corrections, bug findings pull requests and comments are welcome. 
The main idea of the container is, to restrict the capacity of the tree by the next power of two universe size,
given an arbitrary size at the initialization. 
*/

/**
The main advantage of the Van Emde Boas tree appears on a large amount of elements, as the provided standard
operations of the tree are constant in time and of order O(lg2(lg2(U))), where U is the capacity of the tree, constant 
after creation. For small amount of elements the overhead coming along with the structure take over. However, if the 
universe size becomes bigger, the tree performance becomes better.
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
further helpful source was the C++ implementation found here, 
http://www.keithschwarz.com/interesting/code/van-emde-boas-tree/
where the idea of bit operations is taken from. 
*/

module vebtree;
import core.bitop;
import std.traits : ReturnType, isIterable, arity;
import std.typecons : Flag, Yes, No;
import std.math : nextPow2;
import core.stdc.limits : CHAR_BIT;

debug import std.format : format;

version (unittest)
{
    import std.parallelism : parallel;
    import std.conv : to;
    import core.stdc.stdio : printf;
    import std.container.rbtree : redBlackTree;

    import std.range;
    import std.random;
    import std.format;
    import std.container; // red black tree may be used in unittests for comparison.
    import std.math : sqrt;

    // helping function for output a given value in binary representation
    void bin(size_t n)
    {
        /* step 1 */
        if (n > 1)
            bin(n / 2);
        /* step 2 */

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

    auto generateVEBtree(size_t baseSize)(uint currentSeed, size_t front, size_t back, ref size_t M)
    {
        static assert(baseSize > 1);
        static assert((baseSize & (baseSize - 1)) == 0);
        assert(front >= 2);
        rndGen.seed(currentSeed); //initialize the random generator
        M = uniform(front, back + 1); // parameter for construction
        return vebRoot!baseSize(M);
    }
    string generateDebugString(string identifier1, size_t identifier2, size_t baseSize, uint currentSeed, size_t M)
    {
        return format!"%s: %d baseSize: %d; seed: %d M: %d"(identifier1, identifier2, baseSize, currentSeed, M);
    }
}

// bit mask representing uint.max. 
enum size_t lowerMask = size_t.max >> (size_t.sizeof * CHAR_BIT / 2);
// bit mask representing size_t.back without uint.max. 
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
        auto retVal = VEBtree!(inclusive, root)(root.front, root.back, root.length);
    }

    return retVal;
}

static foreach (_; 1 .. size_t.sizeof - 1)
{
    unittest
    {
        enum baseSize = 1 << _;
        foreach (b; (CHAR_BIT * size_t.sizeof * testMultiplier).iota.parallel)
        {
            auto currentSeed = unpredictableSeed();
            size_t M;

            auto vT = generateVEBtree!(1 << _)(currentSeed, 2UL, baseSize, M);
            assert(vT.universe == M);  
            const errorString = generateDebugString("UT: white box test: ", b, baseSize, currentSeed, M);

            assert(vT.value_ == 0, errorString);
            assert(vT.ptr_ is null, errorString);
            assert(vT.capacity == baseSize, errorString);
            assert(vT.empty == true, errorString);
            assert(vT.front == NIL, errorString);
            assert(vT.back == NIL, errorString);
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
                assert(vT.front == cacheArray.front, errorString);
                assert(vT.back == cacheArray.back, errorString);
            }
            else
            {
                assert(vT.front == NIL, errorString);
                assert(vT.back == NIL, errorString);
            }

            auto currElement = vT.front;
            foreach (el; cacheArray.uniq)
            {
                assert(currElement == el, errorString);
                currElement = vT.next(currElement);
            }
            currElement = vT.back;
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
            assert(vT.prev(vT.front) == NIL, errorString);
            assert(vT.next(vT.back) == NIL, errorString);
            assert(vT == deepCopy, errorString);
            assert(vT == deepCopy(), errorString);

            if (cacheArray.length)
            {
                auto val = cacheArray.uniq.array.randomCover.front;
                vT.remove(val);
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
                    assert(vT.remove(key), errorString);
                }
                else
                {
                    assert(!(vT.remove(key)), errorString);
                }
            }
            assert(vT.value_ == 0, errorString);
            assert(vT.empty, errorString);
        }
    }
}

static foreach (_; 1 .. size_t.sizeof - 1)
{
    ///
    unittest
    {
        import std.range : iota; 
        foreach (b; (CHAR_BIT * size_t.sizeof * testMultiplier).iota.parallel)
        {
            auto currentSeed = unpredictableSeed();
            size_t M;
            auto vT = generateVEBtree!(1 << _)
                    (currentSeed, CHAR_BIT * size_t.sizeof, CHAR_BIT * size_t.sizeof * CHAR_BIT * size_t.sizeof, M);
            const errorString = 
                generateDebugString("UT: black box test capacity and universe: ", b, 1 << _, currentSeed, M); 
            
            assert(vT.universe == M, errorString);
            assert(vT.capacity == (vT.universe - 1).nextPow2,
                    to!string("vT.capacity: " ~ to!string(
                        vT.capacity) ~ " vT.universe: " ~ to!string(vT.universe)));
            assert(!(vT.ptr_ is null), errorString);
            assert(vT.capacity == (vT.universe - 1).nextPow2, errorString);
        }
    }
}

static foreach (_; 1 .. size_t.sizeof - 1)
{
    ///
    unittest
    {
        import std.range : iota; 
        foreach (b; (CHAR_BIT * size_t.sizeof * testMultiplier).iota.parallel)
        {
            auto currentSeed = unpredictableSeed();
            currentSeed = 3989648295; 
            size_t M;
            auto vT = generateVEBtree!(1 << _)
                (currentSeed, CHAR_BIT * size_t.sizeof, CHAR_BIT * size_t.sizeof * CHAR_BIT * size_t.sizeof, M);
            const errorString = 
                generateDebugString("UT: black box test outer interface: ", b, 1 << _, currentSeed, M); 
            size_t N = uniform(0UL, 2 * M); // independent parameter for testing

            // make an array of length N
            size_t[] testArray, cacheArray;
            testArray = new size_t[N];
            cacheArray.reserve(N);
            // fill the array with all possible values 
            foreach (ref el; testArray)
                el = (2 * M).iota.choice;

            auto rbt = redBlackTree!size_t();

            foreach (val; testArray)
            {
                assert(vT.universe == M, errorString);
                assert(vT.length == rbt.length, errorString);

                bool insertExpectation;
                if (val < vT.capacity && !(val in vT))
                {
                    insertExpectation = true;
                }
                const insertResult = vT.insert(val);

                assert(insertResult == insertExpectation, errorString);

                if (insertResult)
                {

                    assert(val in vT, errorString);
                    assert(!vT.empty, errorString);
                    rbt.insert(val);
                    assert(vT.front == rbt.front, errorString);
                    assert(vT.back == rbt.back,
                            "val:" ~ to!string(val) ~ " vT.back: " ~ to!string(
                                vT.back) ~ " rbt.back: " ~ to!string(rbt.back));

                    cacheArray ~= val;
                }
                else
                {
                    if (!(val in rbt))
                    {
                        assert(!(val in vT), errorString);
                    }
                    else
                    {
                        assert(val in vT, errorString);
                    }
                }
            }

            import std.algorithm.sorting : sort; 
            cacheArray.sort;

            foreach (i, el; cacheArray)
            {
                assert(el in vT, errorString);
                if (i + 1 != cacheArray.length)
                {
                    assert(vT.next(el) == cacheArray[i + 1],errorString);
                }
                else
                {
                    assert(vT.next(el) == NIL, errorString);
                }
            }

            foreach (i, el; vT)
                assert(el == cacheArray[i], errorString);
            
            assert(vT == cacheArray, errorString); 

            auto vT2 = vT.dup; 
            assert(vT == vT2); 

            if(cacheArray.length)
            {
                auto rndNum = cacheArray.choice; 
                vT2.remove(rndNum); 
                assert(!(rndNum in vT2));
                assert(rndNum in vT);
                assert(vT != vT2); 
                rndNum = uniform(0UL, vT2.capacity);
                if(!(rndNum in vT))
                {
                    assert(!(rndNum in vT), errorString ~ format!"rndNum: %d"(rndNum));
                    assert(vT2.insert(rndNum), errorString);
                }
                assert(vT != vT2); 
                //auto vT3 = vT2; 
                //vT3.insert(rndNum); 
                //assert(rndNum in vT3);
                //assert(rndNum in vT2); 
                //assert(vT2.length == vT3.length); 
            }

            const rangeExclusive = vT(); 
            assert(vT == rangeExclusive); 

            auto rangeInclusive = vT[]; 
            import std.range : enumerate; 
            foreach(i, el; rangeInclusive.enumerate)
            {
                if(i == 0)
                {
                    if(!(0 in vT))
                    {
                        continue;
                    }
                }
                else if(i + 1 != rangeInclusive.length)
                {
                    assert(el in vT, errorString ~ format!" el: %d"(el)); 
                }
                else if(i + 1 == rangeInclusive.length)
                {
                    assert(el == vT.universe || el == vT.capacity);
                    if(el == vT.universe)
                    {
                        assert(vT.back <= vT.universe || vT.back == NIL, errorString ~ format!" length: %d"(vT.length)); 
                    }
                    else
                    {
                        assert(vT.back > vT.universe, errorString); 
                        assert(vT.back < vT.capacity, errorString); 
                    }
                }
                else
                {
                    assert(0); 
                }
            }

            import std.range : retro, enumerate; 
            foreach (i, el; cacheArray.retro.enumerate)
            {
                assert(el in vT, errorString);
                if (i + 1 != cacheArray.length)
                {
                    assert(vT.prev(el) == cacheArray[($ - 1) - (i + 1)], errorString);
                }
                else
                {
                    assert(vT.prev(el) == NIL, errorString);
                }
            }

            foreach (val; testArray)
            {
                assert(vT.length == rbt.length, errorString);
                if (val in rbt)
                {
                    assert(val in vT, errorString);
                    rbt.removeKey(val);
                    assert(vT.remove(val), errorString);
                }
                else
                {
                    assert(!(val in vT), errorString);
                    assert(!vT.remove(val), errorString);
                }
                assert(!(val in rbt), errorString);
                assert(!(val in vT), errorString);
            }
            assert(vT.length == 0, errorString);
            assert(rbt.length == 0, errorString);
        }
    }
}

/**
define the absence of a key to be -1. 
*/
enum NIL = ptrdiff_t(-1);

/**
The tree creator function. Optionally, the base size can be provided at compile time, however, the best results are 
achieved with the default base size of CHAR_BIT * size_t.sizeof
*/
auto vebRoot(size_t baseSize = CHAR_BIT * size_t.sizeof)(size_t universe)
{
    /**
    Two parameters are provided: 
    - the base size is the maximal amount bits can be stored in a single node without branching (generating children)
    - the universe is the user provided input, providing the expected amount of keys, going to be stored in the tree
    */
    return VEBroot!baseSize(universe);
}

/**
A van Emde Boas node implementation
*/
struct VEBroot(size_t baseSize)
{
    size_t toHash() const nothrow { assert(0); }

    /**
    yields a deep copy of the node. I. e. copies all data in children and allocates another tree 
    */
    typeof(this) dup()
    {
        auto retVal = typeof(this)(universe);
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
            if (length != input.length)
                return false;

        size_t currentElem = this.front;

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
            if (key == this.front || key == this.back)
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
        universe = val;
        setEmpty;
        
        assert(!length_ == this.empty);

        if (!isLeaf)
        {
            assert(this.capacity == (universe - 1).nextPow2);
            const arrSize = this.capacity.hSR + 1;
            
            // reserve enough place for the summary and the children cluster
            ptr_ = (new typeof(this)[arrSize]).ptr;

            // add higher square root children with lower square root universe each.
            foreach (i, ref el; cluster)
                el = typeof(this)(this.capacity.lSR);

            // add the summary with its universe of higher squaure root of the current universe
            summary = typeof(this)(this.capacity.hSR);
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
    the empty method to inform of an empty state of the tree. 
    */
    bool empty() const
    {
        return isLeaf ? value_ == 0 : value_ == -NIL;
    }

    /**
    This yields whether the node is a leaf node.
    */
    bool isLeaf() const @nogc
    {
        return universe <= baseSize;
    }

    /**
    The minimal contained key in the van Emde Boas tree
    */
    size_t front() @nogc const
    {
        if (empty) // do not proceed at all, if the root is empty
            return NIL;
        if (isLeaf) // pass control to the node
            return bsf(value_);
        return value_ & lowerMask;
    }

    /**
    The maximal contained key in the van Emde Boas tree
    */
    size_t back() @nogc const
    {
        if (empty) // do not proceed at all, if the root is empty
            return NIL;
        if (isLeaf) // pass control to the node
            return bsr(value_);
        return (value_ & higherMask) >> (CHAR_BIT * size_t.sizeof / 2);
    }

    /**
    As a usual container, van Emde Boas tree provides the notion of capacity
    */
    size_t capacity() @nogc const
    {
        return isLeaf ? baseSize : (universe - 1).nextPow2;
    }

    /**
    remove method of the van Emde Boas tree
    */
    bool remove(size_t val)
    {
        if (val >= capacity) // do not proceed at all, if the value can't be in the tree 
            return false;
        if (empty) // do not proceed at all, if the root is empty
            return false;
        if (isLeaf) // pass control to the node
            return length(length - (btr(&value_, val) != 0));
        if (front == back) // if the current node contains only a single value
        {
            assert(length == 1);
            if (front != val)
                return false; // do nothing if the given value is not the stored one 
            assert(length == 1);
            return length(length - 1);
        }

        if (val == front) // if we met the minimum of a node 
        {
            auto treeOffset = summary.front; // calculate an offset from the summary to continue with        
            if (treeOffset == NIL) // if the offset is invalid, then there is no further hierarchy and we are going to 
            {
                front = back; // store a single value in this node. 
                assert(length == 2);
                return length(length - 1);
            }
            auto m = cluster[treeOffset].front; // otherwise we get the minimum from the offset child
            // remove it from the child 
            cluster[treeOffset].remove(m);
            if (cluster[treeOffset].empty)
                summary.remove(treeOffset);
            //anyway, the new front of the current node become the restored value of the calculated offset. 
            front = index(treeOffset, m);
            assert(length);
            return length(length - 1);
        }
        
        if (val == back) // if we met the maximum of a node 
        {
            // calculate an offset from the summary to contiue with 
            auto treeOffset = summary.back;
            // if the offset is invalid, then there is no further hierarchy and we are going to 
            if (treeOffset == NIL)
            {
                // store a single value in this node. 
                back = front;
                assert(length == 2);
                return length(length - 1);
            }
            // otherwise we get maximum from the offset child 
            auto m = cluster[treeOffset].back;
            // remove it from the child 
            cluster[treeOffset].remove(m);
            if (cluster[treeOffset].empty)
                summary.remove(treeOffset);
            // anyway, the new back of the current node become the restored value of the calculated offset. 
            back = index(treeOffset, m);
            assert(length);
            return length(length - 1);
        }
        // if no condition was met we have to descend deeper. We get the offset by reducing the value to high(value, uS)
        auto treeOffset = high(val);
        auto res = length(length - cluster[treeOffset].remove(low(val)));
        if (cluster[treeOffset].empty)
            summary.remove(treeOffset);
        return res;
    }
    
    /**
    The successor search method of the van Emde Boas tree. 
    */
    size_t next(size_t val) @nogc const
    {
        if (empty) // do not proceed at all, if the root is empty
            return NIL;
        if (isLeaf) // pass control to the node
        {
            if (val + 1 >= baseSize) // all vals are reduced by one. 
                return NIL;

            // create a mask, which hides all lower bits of the stored value up to the given bit number, then apply
            // bit search from the lowest bit. 
            auto maskedVal = value_ & ~((size_t(1) << (val + 1)) - 1);
            
            if (maskedVal != 0)
                return maskedVal.bsf;

            return NIL;
        }
        // if given value is less then the front, return the front as successor
        if (val < front)
            return front;
        // if given value is greater then the back, no predecessor exists
        if (val >= back)
            return NIL;
        // if none of the break conditions was met, we have to descent further into the tree. 
        // calculate the child index by high(value, uS)
        const childIndex = high(val);
        // look into the child for its maximum
        const maxlow = cluster[childIndex].back;
        // if the maximum exists and the lowered given value is less then the child's maximum 
        if ((maxlow != NIL) && (low(val) < maxlow))
        {
            auto offset = cluster[childIndex].next(low(val));
            // the result is given by reconstruction of the answer
            return index(childIndex, offset);
        }
        else // otherwise we can not use the maximum of the child 
        {
            auto succcluster = summary.next(childIndex);
            // if the successor cluster is null
            if (succcluster == NIL)
                return back;
            assert(succcluster != NIL);
            assert(cluster[succcluster].front != NIL);
            // if the successor cluster exists, the offset is given by its minimum
            // and the result by the reconstruction of the offset. 
            return index(succcluster, cluster[succcluster].front);
        }
    }

    /**
    The predecessor search method of the van Emde Boas tree. 
    */
    size_t prev(size_t val) @nogc
    {
        if (empty) // do not proceed at all, if the root is empty
            return NIL;
        if (isLeaf) // pass control to the node
        {
            if (val != 0)
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
        // if given value is greater then the stored back, the predecessor is back
        if (val > back)
            return back;
        // if given value is less then the front, no predecessor exists. 
        if (val <= front)
            return NIL;
        // if none of the break conditions was met we have to descend further into the tree. 
        auto childIndex = high(val); // calculate the child index by high(value, uS)
        const minlow = cluster[childIndex].front; // look into the child for its minimum
        // if the minimum exists and the lowered given value is greater then the child's minimum
        if ((minlow != NIL) && (low(val) > minlow))
        {
            auto offset = cluster[childIndex].prev(low(val));
            // the result is given by reconstruction of the answer. 
            return index(childIndex, offset);
        }
        else // otherwise we can not use the minimum of the child 
        {
            auto predcluster = summary.prev(childIndex);
            // if the predecessor cluster is null return the current front, as this is the last remaining value 
            if (predcluster == NIL)
                return front;
            // if the predecessor cluster exists, the offset is given by its maximum
            // and the result by the reconstruction of the offset. 
            return index(predcluster, cluster[predcluster].back);
        }
    }

    /**
    The insertion method of the van Emde Boas tree. 
    */
    bool insert(size_t val)
    {
        if (val >= capacity) // do not proceed at all, if the value won't fit into the tree 
            return false;
        if (isLeaf) // pass control to the node
            return length(length + (bts(&value_, val) == 0));
        if (empty) // if the current node does not contain anything put the value inside. 
        {
            assert(empty);
            front = val;
            back = val;
            assert(front == val);
            assert(!empty);
            assert(front == back);
            assert(!empty);
            return length(length + 1);
        }

        assert(!empty);
        assert(front != NIL);
        assert(back != NIL);

        if (val == front || val == back) // if the value coincides with existing values, return 
            return false;
        // if the node contains a single value only, expand the node to a range and leave. 
        if (front == back)
        {
            if (front > val)
                front = val;
            if (back < val)
                back = val;
            return length(length + 1);
        }
        /*
            if none of the cases above was true (all of them are break conditions) we have to compare the given value
            with the values present and adapt the range limits. This replaces the value we want to insert. 
        */

        // a swap can not be used here, as front is itself a (property) method 
        if (val < front)
        {
            const tmpKey = val;
            val = front;
            front = tmpKey;
            assert(front == tmpKey);
        }

        // a swap can not be used here, as back is itself a (property) method 
        if (val > back)
        {
            const tmpKey = val;
            val = back;
            back = tmpKey;
            assert(back == tmpKey);
        }

        // calculate the index of the children cluster by high(value, uS) we want to descent to. 
        const nextTreeIndex = high(val);
        if (cluster[nextTreeIndex].empty)
            summary.insert(nextTreeIndex);
        return length(length + cluster[nextTreeIndex].insert(low(val)));
    }

    /**
    The cached value of the universe, provided on creation
    */
    size_t universe() @nogc const
    {
        return universe_;
    }
    private:
    bool front(size_t val)
    {
        if (isLeaf) // pass control to the node
            return insert(val);
        value_ = value_ & higherMask; // otherwise, set the lower part of the value, keeping the higher bits
        const retVal = ((value_ & lowerMask) == val) ? false : true;
        value_ = value_ | val;
        return retVal; // this is a bug!
    }

    bool back(size_t val)
    {
        if (isLeaf) // pass control to the node
            return insert(val);
        value_ = value_ & lowerMask; // otherwise, set the higher part of the value, keeping the lower bits
        const retVal = (value_ & higherMask) == (val << (CHAR_BIT * size_t.sizeof / 2)) ? false : true;
        value_ = value_ | (val << (CHAR_BIT * size_t.sizeof / 2));
        return retVal; // this is a bug!
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

    size_t index(size_t x, size_t y) const @nogc
    {
        return .index(this.capacity, x, y);
    }

    size_t low(size_t val) const @nogc
    {
        return .low(this.capacity, val); 
    }

    size_t high(size_t val) const @nogc
    {
        return .high(this.capacity, val); 
    }

    void universe(size_t val)
    {
        universe_ = val; 
    }

    size_t value_;
    size_t universe_;
    size_t length_;
    typeof(this)* ptr_;

    ref summary() inout
    in(!isLeaf)
    { // return the last element of the array of children, stored in the node. 
        return ptr_[capacity.hSR];
    }

    auto cluster() inout
    in(!isLeaf)
    { // return all of the children in the stored array, but the last element 
        return ptr_[0 .. capacity.hSR];
    }

    // The empty setter of a node. This function is kept for consistency in this module. 
    void setEmpty() @nogc
    {
        value_ = isLeaf ? 0 : -NIL;
    }

    // with the trick of https://forum.dlang.org/thread/erznqknpyxzxqivawnix@forum.dlang.org
    int opApplyImpl(O)(O operations) const
    {
        int result;
        size_t leading = this.front;

        //for(size_t leading = front; leading < back; leading = this.next(leading)) 

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

    this(ptrdiff_t front, ptrdiff_t back, size_t _length)
    {
        length = _length; 

        static if (inclusive)
        {
            if(!length)
            {
                backKey = root.universe; 
                length = 2; 
            }
            else
            {
                if(front > 0)
                {
                    ++length;
                }

                if(back <= root.universe)
                {
                    backKey = root.universe; 
                    ++length; 
                }
                else if(back <= root.capacity)
                {
                    backKey = root.capacity; 
                    ++length; 
                }
                else
                {
                    debug
                    {
                        assert(back == root.universe || back == -1, format!"back: %d\n"(back));
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
            frontKey = front;
            backKey = back;
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
    in(!empty)
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