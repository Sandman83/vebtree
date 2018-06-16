/**
Copyright: Copyright (c) 2016- Alexander Orlov. All rights reserved.
License: $(LINK2 https://opensource.org/licenses/MIT, MIT License).
Authors: Alexander Orlov, $(LINK2 mailto:sascha.orlov@gmail.com, sascha.orlov@gmail.com) 
*/

/**
This module implements a Van Emde Boas tree container.
The module is still a work in progress. So, if you find an error by chance, please let me know in any way.
The main idea of the container is, to restrict the capacity of the tree by the next power of two universe size,
given an arbitrary size at the initialization. The tree can be used in two different modes: 
1. Tree contains keys only. Supported operations are 
inserting, deletion, membership testing, neighborhood searching. All queries are of order (lglg U), where U is the 
capacity of the tree, set on initialization. 
2. Tree contains keys and values. Additionally to the above operations the indexing operation is supported. It 
yields the pointer to a stored object, if the key is contained in the tree, otherwise null. 
For optimization purposes, the size limit is size_t.max/2 + 1. The tree was tested on 64- and 32-bit arch. 
So the largest element which can be stored is 4.294.967.295 on a 64-bit architecture. 
*/

// (optional) todo: provide functionality to contain non-unique keys, i. e. exercise 20.3.1 from Cormen

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
import std.algorithm : each, map, until, find, sort, uniq, sum, setSymmetricDifference, min, max; 

private enum vdebug = true; 

version(unittest)
{
    static if(vdebug)
    {
        import std.stdio;
        // helping function for output a given value in binary representation
        void bin(size_t n)
        {
            /* step 1 */
            if (n > 1) bin(n/2);
            /* step 2 */
            write(n % 2);
        }
    }

    /// precalculated powers of two table for unit testing
    enum powersOfTwo = iota(0, CHAR_BIT * size_t.sizeof).map!(a => size_t(1) << a); 
    import std.random; 
    import std.datetime.stopwatch; 
    import std.conv : to;
    import std.container; // red black tree may be used in unittests for comparison.
    import std.math : sqrt; 
    
    Random rndGenInUse; 

    // during tests it is ok a tree with a random capacity not going up to the maximum one. 
    enum testedSize = 1 << 2 * size_t.sizeof; //3 * size_t.sizeof;
    // during tests helping static arrays are used, which have an absolute maximum of size_t.sizeof * 2^20 elements
    enum allowedArraySize = 1 << size_t.sizeof; //(2 * size_t.sizeof + size_t.sizeof/2); 
    // choosed arbitrary, to avoid seg. faults
    /**
    up to 1 << 27 = 1 << (32 - bsf(sizeof(VEBroot!()))) any capacity works for unit testing. 
    */ 
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
enum maxSizeBound = size_t(1) << baseSize/2; // == uint.max + 1 on a 64-bit system

/**
The default response of a tree node on a key request is null. I. e. if a key is not contained, null is returned. 
*/
alias Response = Nullable!(size_t, maxSizeBound); 

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
size_t hSR(size_t value) @nogc nothrow 
{
    return size_t(1) << (bsr(value)/2 + ((bsr(value) & 1) || ((value != 0) && (value & (value - 1))))); 
}
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: hSR               "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
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
size_t lSR(size_t value) @nogc nothrow 
{
    return size_t(1) << (bsr(value)/2);
}
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: lSR               "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    auto lSR = lSR(M); 
    
    assert((lSR & (lSR - 1)) == 0); 
    assert(lSR * lSR < M);
    auto check = powersOfTwo.find(lSR).array; 
    
    if(lSR < size_t.max/2) assert((check[1]) > sqrt(to!float(M))); 
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
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: high              "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    auto U = nextPow2(M); 
    auto x = uniform(0U, U, rndGenInUse); 

    assert(high(U, x) == x / lSR(U)); 
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
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: low               "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(1U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    auto U = nextPow2(M); 
    auto x = uniform(0U, U, rndGenInUse); 

    assert(low(U, x) == (x & (lSR(U) - 1)));
}

/**
This is an index function to retain the searched value. It is defined as x * lSR(u) + y. Beyond this, the
relation holds: x = index(high(x), low(x)). This is the ideal indexing function of the tree. 
*/
private size_t index(size_t universe, size_t x, size_t y) @nogc nothrow
{
    return (x * lSR(universe) + y);
}
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: index             "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(0U,size_t.max/2, rndGenInUse); //set universe size to some integer. 
    
    auto U = nextPow2(M); 
    auto x = uniform(0U, U, rndGenInUse); 
    
    assert(index(U, high(U, x), low(U, x)) == x); 
}

/// convenience method for initializing a van emde boas tree root. This is the default method to get a tree. 
auto vebRoot(size_t universe)
in
{
    assert(universe); 
}
do
{
    return VEBroot!()(universe); 
}
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: 1. use case       "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    
    auto M = uniform(2U, baseSize, rndGenInUse); //set universe size to some integer (small). 
    auto N = uniform(1U, M, rndGenInUse); //set universe size to some integer (small). 
    
    auto vT = vebRoot(M); 
    assert(vT.empty); 

    size_t[] testArray = new size_t[N]; 
    M.iota.randomCover(rndGenInUse).take(N)
            .enumerate
            .tee!(el => testArray[el.index] = el.value)
            .each!(el => vT.insert(el.value));

    assert(vT.front == testArray.sort.front); 
    assert(vT.back == testArray.sort.back); 
    assert(vT().front == testArray.sort.front);  
    assert(vT().back == testArray.sort.back); 
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe);
    assert(vT.length == testArray.length); 
    assert(vT() == testArray); 
    assert(vT.capacity == baseSize); 
    assert(vT.universe == M); 
    assert(!vT.empty); 
    testArray.each!(el => assert(el in vT)); 
    size_t counter; 
    for(auto el = vT.front; el != vT.back; el = vT.successor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        ++counter; 
    }
    for(auto el = vT.back; el != vT.front; el = vT.predecessor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        --counter; 
    }
    auto secondElementQ = vT.successor(testArray.sort[0]); 
    if(!secondElementQ.isNull)
    {
        assert(testArray.sort.lowerBound(secondElementQ.get).length == 1); 
    }

    auto randomElement = testArray[uniform(0, testArray.length, rndGenInUse)]; 
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
    assert(vTdeepCopy2.length == testArray.length - 1); 
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
    static assert(is(typeof(vTdeepCopy) : VEBroot!T, T...)); 
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
        assert(inclusiveSlice.front == vTdeepCopy.successor(0));
    }
    else
    {
        assert(inclusiveSlice.front == vTdeepCopy.front); 
    }
    
    assert(vTdeepCopy() == testArray);
    auto vTdeepCopy3 = vT.dup; 
    auto vTshallowCopy = vT; 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
    vTdeepCopy.remove(vTdeepCopy.front.get); 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
 
    assert(vTshallowCopy == vT);
    assert(vTdeepCopy3 == vT); 

    assert(vT() == vT); 
    assert(vT == vT());
}
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: 2. use case       "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    
    auto M = uniform(baseSize + 1, testedSize, rndGenInUse); //set universe size to some integer (small). 
    auto N = uniform(1U, min(M, allowedArraySize), rndGenInUse); //set universe size to some integer (small). 
    
    auto vT = vebRoot(M); 
    assert(vT.empty); 

    size_t[] testArray = new size_t[N]; 
    
    M.iota.randomCover(rndGenInUse).take(N)
            .enumerate
            .tee!(el => testArray[el.index] = el.value)
            .each!(el => vT.insert(el.value));

    assert(vT.front == testArray.sort.front); 
    assert(vT.back == testArray.sort.back); 
    assert(vT().front == testArray.sort.front);  
    assert(vT().back == testArray.sort.back); 
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe);
    assert(vT.length == testArray.length); 
    assert(vT() == testArray); 
    assert(vT.capacity == M.nextPow2); 
    assert(vT.universe == M); 
    assert(!vT.empty); 
    
    testArray.each!(el => assert(el in vT)); 
    size_t counter; 
    for(auto el = vT.front; el != vT.back; el = vT.successor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        ++counter; 
    }
    for(auto el = vT.back; el != vT.front; el = vT.predecessor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        --counter; 
    }

    auto secondElementQ = vT.successor(testArray.sort[0]); 
    if(!secondElementQ.isNull)
    {
        assert(testArray.sort.lowerBound(secondElementQ.get).length == 1); 
    }

    auto randomElement = testArray[uniform(0, testArray.length, rndGenInUse)]; 
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
    assert(vTdeepCopy2.length == testArray.length - 1); 

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
        assert(inclusiveSlice.front == vTdeepCopy.successor(0));
    }
    else
    {
        assert(inclusiveSlice.front == vTdeepCopy.front); 
    }
    
    assert(vTdeepCopy() == testArray);
    auto vTdeepCopy3 = vT.dup; 
    auto vTshallowCopy = vT; 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
    vTdeepCopy.remove(vTdeepCopy.front.get); 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
 
    assert(vTshallowCopy == vT);
    assert(vTdeepCopy3 == vT); 

    assert(vT() == vT); 
    assert(vT == vT());
}
///
unittest
{
    auto currentSeed = 2139424061U; //unpredictableSeed();
    static if(vdebug){write("UT: 3. use case       "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    
    auto M = uniform(2U, baseSize, rndGenInUse); //set universe size to some integer (small). 
    auto N = uniform(1U, M, rndGenInUse); //set universe size to some integer (small). 
    
    auto vT = vebRoot!size_t(M); 
    assert(vT.empty); 

    size_t[] testArray = new size_t[N]; 
    size_t[] testValArray = new size_t[N]; 
    testValArray.each!((ref el) => el = uniform(0UL, size_t.max, rndGenInUse)); 
    
    M.iota.randomCover(rndGenInUse).take(N)
            .enumerate
            .tee!(el => testArray[el.index] = el.value)
            .each!(el => vT.insert(el.value, testValArray[el.index]));

    assert(vT.front == testArray.sort.front); 
    writeln(testValArray); 
    foreach(el; vT())
    {
        write(*vT[el]); 
        write(" ");
    }
    writeln(); 
    assert(*vT[vT.front] == testValArray[0]);
    assert(vT.back == testArray.sort.back); 
    assert(vT().front == testArray.sort.front);  
    assert(vT().back == testArray.sort.back); 
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe);
    assert(vT.length == testArray.length); 
    assert(vT() == testArray); 
    assert(vT.capacity == baseSize); 
    assert(vT.universe == M); 
    assert(!vT.empty); 
    testArray.each!(el => assert(el in vT)); 
    size_t counter; 
    for(auto el = vT.front; el != vT.back; el = vT.successor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        ++counter; 
    }
    for(auto el = vT.back; el != vT.front; el = vT.predecessor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        --counter; 
    }
    auto secondElementQ = vT.successor(testArray.sort[0]); 
    if(!secondElementQ.isNull)
    {
        assert(testArray.sort.lowerBound(secondElementQ.get).length == 1); 
    }
    auto randomElement = testArray[uniform(0, testArray.length, rndGenInUse)]; 
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
    assert(vTdeepCopy2.length == testArray.length - 1); 

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
    static assert(is(typeof(vTdeepCopy) : VEBroot!T, T...)); 
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
        assert(inclusiveSlice.front == vTdeepCopy.successor(0));
    }
    else
    {
        assert(inclusiveSlice.front == vTdeepCopy.front); 
    }
    
    assert(vTdeepCopy() == testArray);
    auto vTdeepCopy3 = vT.dup; 
    auto vTshallowCopy = vT; 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
    vTdeepCopy.remove(vTdeepCopy.front.get); 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
 
    assert(vTshallowCopy == vT);
    assert(vTdeepCopy3 == vT); 

    assert(vT() == vT); 
    assert(vT == vT());
}
///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: 4. use case       "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    
    auto M = uniform(baseSize + 1, testedSize, rndGenInUse); //set universe size to some integer (small). 
    auto N = uniform(1U, min(M, allowedArraySize), rndGenInUse); //set universe size to some integer (small). 
    
    auto vT = vebRoot!size_t(M); 
    assert(vT.empty); 

    size_t[] testArray = new size_t[N]; 
    
    M.iota.randomCover(rndGenInUse).take(N)
            .enumerate
            .tee!(el => testArray[el.index] = el.value)
            .each!(el => vT.insert(el.value));
    
    assert(vT.front == testArray.sort.front); 
    assert(vT.back == testArray.sort.back); 
    assert(vT().front == testArray.sort.front);  
    assert(vT().back == testArray.sort.back); 
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe);
    assert(vT.length == testArray.length); 
    assert(vT() == testArray); 
    assert(vT.capacity == M.nextPow2); 
    assert(vT.universe == M); 
    assert(!vT.empty); 
    
    testArray.each!(el => assert(el in vT)); 
    size_t counter; 
    for(auto el = vT.front; el != vT.back; el = vT.successor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        ++counter; 
    }
    for(auto el = vT.back; el != vT.front; el = vT.predecessor(el.get))
    {
        assert(el.get == testArray.sort[counter]); 
        --counter; 
    }

    auto secondElementQ = vT.successor(testArray.sort[0]); 
    if(!secondElementQ.isNull)
    {
        assert(testArray.sort.lowerBound(secondElementQ.get).length == 1); 
    }

    auto randomElement = testArray[uniform(0, testArray.length, rndGenInUse)]; 
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
    assert(vTdeepCopy2.length == testArray.length - 1); 

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
        assert(inclusiveSlice.front == vTdeepCopy.successor(0));
    }
    else
    {
        assert(inclusiveSlice.front == vTdeepCopy.front); 
    }
    
    assert(vTdeepCopy() == testArray);
    auto vTdeepCopy3 = vT.dup; 
    auto vTshallowCopy = vT; 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
    vTdeepCopy.remove(vTdeepCopy.front.get); 
    assert(shallowCopyFromRoot.front == vTdeepCopy.front); 
 
    assert(vTshallowCopy == vT);
    assert(vTdeepCopy3 == vT); 

    assert(vT() == vT); 
    assert(vT == vT());
}

/**
the public interface of the root is: 

front
back

opApply(size_t) & (opApply(size_t, ref T))

size_t capacity()
size_t universe()
size_t length() 
dup
(opIndex & opIndexAssign)

opIndex() & opCall()

bool empty()
opBinaryRight
put = insert(size_t key) 
remove(size_t key)
predecessor(size_t key)
successor(size_t key)

the public interface of the tree is: 

length
front() & popFront()
back() & popBack()
predecessor & successor
(void opIndex(auto ref E value, size_t key))
opApply
empty 
auto save()
dup
opEquals()
*/

//
unittest
{
    auto currentSeed = unpredictableSeed(); // 83_843; 898_797_859; 
    static if(vdebug){write("UT: vN, opBinaryIn    "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator

    auto value = uniform(0U, size_t.max, rndGenInUse);
    auto bitNum = uniform(0U, baseSize, rndGenInUse);
    auto vN = vebRoot(baseSize); 
    *vN.val = value; 
    
    if((*vN.val & size_t(1) << bitNum) != 0 ) 
    {
        assert(bitNum in vN); 
    }

    if((*vN.val & size_t(1) << bitNum) == 0 )
    {
        assert(!(bitNum in vN)); 
    }
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: vN, predecessor   "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto v = uniform(2U, testedSize, rndGenInUse); //set universe size to some integer. 
    auto x = uniform(1U, baseSize, rndGenInUse);
    auto vN = vebRoot(baseSize); 
    *vN.val = v; 

    bool found; 

    for(size_t index = x - 1; index >= 0; --index)
    {
        if (v & (size_t(1) << index)) 
        {
            found = true; 
            assert(!vN.empty);
            assert(vN.predecessor(x) == index); 
            break; 
        }
        if(!index) break; 
    }

    if(!found) assert(vN.predecessor(x).isNull); 
}
//
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: vN, successor     "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto v = uniform(0U, size_t.max, rndGenInUse); //set universe size to some integer. 
    auto x = uniform(0U, baseSize, rndGenInUse);
    auto vN = vebRoot(baseSize); 
    *vN.val = v; 
    bool found; 

    for (size_t index = x + 1; index < baseSize; ++index)
    {
        if (v & (size_t(1) << index)) 
        {
            found = true; 
            assert(vN.successor(x).get == index); 
            break; 
        }
    }
    if(!found) assert(vN.successor(x).isNull);
}

auto vebRoot(T)(size_t universe)
in
{
    assert(universe); 
}
do
{
    return VEBroot!T(universe); 
}
/// 
unittest
{
    auto vr = vebRoot!size_t(100);   
    assert(vr.empty); 
    
    size_t input = 42; 
    
    vr.insert(3, input); 
    assert(vr.front == 3); 
    assert(*vr[3] == 42);
    
    size_t input2 = 73; 
    vr.insert(3, input2); 
    assert(*vr[3] == 42);
    *vr[3] = 73; 
    assert(*vr[3] == 73);

    assert(vr[8] is null); 
    vr[15] = input2;
    assert(vr[15] !is null); 
    vr.remove(15); 
    assert(vr[15] is null); 
}

/*
private auto vebRoot(alias source)(size_t universe)
{
    static if(!is(typeof(source) == typeof(null)))
    {
        assert(source.length == universe); 
        return vebRoot!(source.dup)(universe); 
    }
    else
    {
        return vebRoot!(universe); 
    }
}
*/
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
struct VEBroot(T = void)
{
    @property size_t capacity()
    in
    {
        assert(stats !is null); 
    }
    do
    {
        if(universe <= baseSize)
        {
            return baseSize; 
        }
        else
        {
            return universe.nextPow2; 
        }
    }

    @property size_t universe() const
    in
    {
        assert(stats !is null); 
    }
    do
    {
        return (*stats & higherMask) >> (size_t.sizeof * CHAR_BIT/2);     
    }

    @property size_t length()
    in
    {
        assert(stats !is null); 
    }
    do
    {
        return *stats & lowerMask; 
    }

    /**
    the opApply method grants the correct foreach behavior
    */
    int opApply(scope int delegate(ref size_t) /*@nogc*/ operations) //@nogc
    {
        int result; 
        
        for(auto leading = front; !leading.isNull; leading = successor(leading.get)) 
        {
            result = operations(leading.get); 

            if(result)
            {
                break; 
            }
        }

        return result;
    }

    static if(!is(T == void))
    {
        /**
        opApply method in case of present source for iterating over key value pairs
        */
        int opApply(scope int delegate(ref size_t, ref T) /*@nogc*/ operations) //@nogc
        {
            int result; 
        
            for(auto leading = front; !leading.isNull; leading = successor(leading.get)) 
            {
                result = operations(leading.get, *(dataArr[leading.get])); 

                if(result)
                {
                    break; 
                }
            }

            return result;
        }
    }

    /**
        method returning either the lower part of the stored value (intermediate node) or the lowest bit set (bit vector
        mode. If the node does not contain any value (min > max or value == 0) Nullable.null is returned. 
    */
    @property Response front() // @nogc nothrow 
    {
        // define the result as a nullable 
        typeof(return) retVal; 
        /*
            we have only a chance to get a value, if a value is present.
            if it is a leaf, handle the val as a bit array and find the first bit set from the right. 
            if it is not a leaf, get the minimum. 
        */ 
        if(!empty) 
        {
            if(isLeaf)
            {
                retVal = bsf(*val);
            }
            else
            {
                retVal = *val & lowerMask; 
            }   
        }
        // return the result, even if it was not set to a value. 
        return retVal;  
    }


    /** 
        method returning either the higher part of the stored value (intermediate node) or the highest bit set (bit
        vector mode. If the node does not contain any value (min > max or value == 0) Nullable.null is returned. 
    */
    @property Response back() // @nogc nothrow 
    {
        // define the result as a nullable
        typeof(return) retVal; 
        /*
            we have only a chance to get a value, if a value is present. 
            if it is a leaf, handle the val as a bit array and find the first bit set from the left. 
            if it is not a leaf, get the max. 
        */
        if(!empty)
        {
            if(isLeaf)
            {
                retVal = bsr(*val); 
            }   
            else
            {
                retVal = (*val & higherMask) >> (size_t.sizeof * CHAR_BIT/2);
            }
        }
        // return the result, even if it was not set to a value. 
        return retVal;  
    }

    typeof(this) dup()
    {
        auto copy = this;
        copy.stats = new size_t(); 
        copy.val = new size_t();  
        *copy.stats = *this.stats;
        *copy.val = *this.val; 
        if(isLeaf)
        {
            static if(!is(T == void))
            {
                copy.dataArr = this.dataArr[0 .. baseSize].dup.ptr;     
            }
        }
        else
        {
            
            static if(!is(T == void))
            {
                copy.ptrArr = this.ptrArr[0 .. hSR(universe.nextPow2) + 1].dup.ptr;
                copy.dataArr = this.dataArr[0 .. 2].dup.ptr;     
            }
            else
            {
                copy.ptrArr = this.ptrArr[0 .. hSR(universe.nextPow2) + 1].dup;
            }

            copy.ptrArr[0 .. hSR(universe.nextPow2) + 1].each!((ref n) => n = n.dup);
        }
        
        return copy;
    }

    static if(!is(T == void))
    {
        auto ref opIndex(size_t key) @nogc
        {
            assert(universe); 
            if(key > universe.nextPow2)
            {
                return null; 
            }
            if(isLeaf)
            {
                assert(key < baseSize);
                return dataArr[key];
            }
            else
            {
                if(empty)
                {
                    // if an empty intermediate node is found, nothing is stored below it. 
                    return null; 
                } 
                // case of a single valued range. 
                if(key == front)
                {
                    return dataArr[0]; 
                }

                if(key == back)
                {
                    return dataArr[1];
                }
                
                /*
                    else we have to descend, using the recursive indexing: 
                    1. take the high(value, uS)-th child and 
                    2. ask it about the reduced low(value, uS) value
                    3. use the lSR(uS) universe size of the childe node. 
                */
                
                assert(cluster[high(key)].universe == lSR(universe.nextPow2));
                return cluster[high(key)][low(key)]; 
            }
        }

        void opIndexAssign(ref T value, size_t key)
        {
            insert(key, value); 
        }
    }

    auto opIndex()
    {
        return VEBtree!(Yes.inclusive, typeof(this))(this);  
    }

    auto opCall()
    {
        return VEBtree!(No.inclusive, typeof(this))(this);  
    }

    /** 
    method to check whether the current node holds a value
    */
    @property bool empty() // @nogc nothrow 
    in
    {
        assert(val !is null); 
    }
    do
    {
        if(isLeaf)
        {
            return *val == 0; 
        }
        else
        {
            return (*val & lowerMask) > ((*val & higherMask) >> (size_t.sizeof * CHAR_BIT/2)); 
        }
    }

    /**
    member method for the case universe size < base size. Overloads by passing only one parameter, which is
    the bit number of interest. Returns whether the appropriate bit inside the bitvector is set.
    */
    bool opBinaryRight(string op)(size_t key) if(op == "in")  // @nogc nothrow 
    {
        assert(universe); 
        if(key > universe.nextPow2)
        {
            return false; 
        }
        if(isLeaf)
        {
            assert(key < baseSize);
            return bt(val, key) != 0;
        }
        else
        {
            if(empty)
            {
                // if an empty intermediate node is found, nothing is stored below it. 
                return false; 
            } 
            // case of a single valued range. 
            if(key == front || key == back)
            {
                return true; 
            }
            
            /*
                else we have to descend, using the recursive indexing: 
                1. take the high(value, uS)-th child and 
                2. ask it about the reduced low(value, uS) value
                3. use the lSR(uS) universe size of the childe node. 
            */
            
            assert(cluster[high(key)].universe == lSR(universe.nextPow2));
            return low(key) in cluster[high(key)]; 
        }
    }

    alias put = insert; 
    /**
    insert method. this method is called from class with a universe size given. It performs recursion calls untill
    the universe size is reduced to the base size. Then the overloaded insert method is called. 
    */
    bool insert(T...)(size_t key, ref T value) 
        if((is(T == void) && T.length == 0) || (!is(T == void) && T.length < 2))// @nogc nothrow 
    {
        
        typeof(return) res; 
        scope(exit)
        {
            length = length + res; 
        }
        
        if(key > capacity)
        {
            res = false; 
            return res;     
        }

        // if descended so far, do not use other functionality any more. 
        if(isLeaf)
        {
            assert(val !is null); 
            res = bts(val, key) == 0;
            static if(T.length)
            {
                if(res)
                {
                    writeln("dataArr[key]: ", dataArr[key]); 
                    dataArr[key] = &value[0]; 
                    writeln("*dataArr[key]: ", *dataArr[key]); 
                }
            }
            return res; 
        }

        if(empty) // if the current node does not contain anything put the value inside. 
        {
            front(key, value); // the setters of min handle the value appropriately and do not need the universe size
            back(key, value); // being explicitely provided, as they can check the isLeaf property. 
            assert(!empty); 
            res = true; 
            return res; 
        }

        assert(!empty);
        assert(!front.isNull); 
        assert(!back.isNull); 

        if(key == front || key == back)
        {
            res = false; // return, if value is already here.
            return res; 
        }

        if(front == back) // if the node contains a single value only, expand the node to a range and leave. 
        {
            if(front > key)
            {
                front(key, value); 
            }
            if(back < key)
            {
                back(key, value); 
            }
            
            res = true; 
            return res; 
        }
        /*
            if none of the cases above was true (all of them are break conditions) we have to compare the given value
            with the values present and adapt the range limits. This replaces the value we want to insert. 
        */
        // a swap can not be used here, as min is itself a (property) method 
        if(key < front)
        {
            auto tmpKey = key; 

            static if(T.length)
            {
                auto tmpVal = value[0]; 
            }

            key = front.get;

            static if(T.length)
            {
                value[0] = *this[front.get]; 
            }
            
            static if(T.length)
            {
                front(tmpKey, tmpVal);
            }
            else
            {
                front(tmpKey); 
            }
            
        }
        // a swap can not be used here, as max is itself a (property) method 
        if(key > back)
        {
            auto tmpKey = key; 
            
            static if(T.length)
            {
                auto tmpVal = value[0]; 
            }
            
            key = back.get; 
            
            static if(T.length)
            {
                value[0] = *this[back.get]; 
            }

            static if(T.length)
            {
                back(tmpKey, tmpVal); 
            }
            else
            {
                back(tmpKey); 
            }
        }
        
        // calculate the index of the children cluster by high(value, uS) we want to descent to. 
        auto nextTreeIndex = high(key); 
        
        // if the child is happened to be null we have to update the summary and insert value of high(value, uS) into it
        assert(summary.universe == hSR(universe.nextPow2));
        
        if(cluster[nextTreeIndex].empty)
        {
            summary.insert(high(key), value);
        }
        
        // in any case we pass the lowered value low(value, uS) to the child. 
        assert(cluster[nextTreeIndex].universe == lSR(universe.nextPow2));
        res = cluster[nextTreeIndex].insert(low(key), value); 
        
        return res;
    }

    /**
    remove method. this method is called from class with a universe size given. It performs recursion calls untill
    the universe size is reduced to the base size. Then the overloaded remove method is called. 
    */
    auto remove(size_t key) // @nogc nothrow 
    {
        bool res; 
        static if(!is(T == void))
        {
            T* value; 
        }

        scope(exit)
        {
            length = length - res; 
        }
        // if descended so far, do not use other functionality any more. 
        if(isLeaf)
        {
            res = btr(val, key) != 0;
            static if(!is(T == void))
            {
                if(res)
                {
                    value = dataArr[key]; 
                    dataArr[key] = null; 
                }
            }

            static if(is(T == void))
            {
                return res; 
            }
            else
            {
                return value; 
            }
        }

        if(empty) 
        {
            // if the current node is null, there is nothing to remove. 
            res = false; 
            static if(is(T == void))
            {
                return res; 
            }
            else
            {
                return value; 
            }
        }
        
        if(front == back) // if the current node contains only a single value
        {
            if(front != key)
            {
                // do nothing if the given value is not the stored one 
                res = false; 

                static if(is(T == void))
                {
                    return res; 
                }
                else
                {
                    return value; 
                }
            } 

            // set this node to the sentinel-null if it does.
            static if(!is(T == void))
            {
                value = this.nullify; 
            }
            else
            {
                this.nullify; 
            }
            
            res = true; 

            static if(is(T == void))
            {
                return res; 
            }
            else
            {
                return value; 
            }
        }

        if(key == front) // if we met the minimum of a node 
        {
            auto treeOffset = summary.front; // calculate an offset from the summary to continue with
            if(treeOffset.isNull) // if the offset is invalid, then there is no further hierarchy and we are going to 
            {
                front = back; // store a single value in this node. 
                res = true; 

                static if(is(T == void))
                {    
                    return res; 
                }
                else
                {
                    value = dataArr[0]; 
                    dataArr[0] = dataArr[1]; 
                    return value; 
                }
            }
            auto min = cluster[treeOffset.get].front; // otherwise we get the minimum from the offset child
            
            assert(cluster[treeOffset].universe == lSR(universe.nextPow2)); 

            // remove it from the child 
            static if(is(T == void))
            {
                cluster[treeOffset.get].remove(min); 
            }
            else
            {
                auto minVal = cluster[treeOffset.get].remove(min); 
            }

            // if it happens to become null during the remove process, we also remove the offset entry from the summary 
            assert(summary.universe == hSR(universe.nextPow2));
            if(cluster[treeOffset.get].empty)
            {
                summary.remove(treeOffset.get); 
            }

            //anyway, the new min of the current node become the restored value of the calculated offset. 
            static if(is(T == void))
            {
                front(index(treeOffset.get, min)); 
            }
            else
            {
                value = dataArr[0]; 
                front(index(treeOffset.get, min), *minVal); 
            }
            
            res = true; 
            static if(is(T == void))
            {
                return res; 
            }
            else
            {
                return value; 
            }
            
        }

        // if we met the maximum of a node 
        if(key == back) 
        {
            // calculate an offset from the summary to contiue with 
            auto treeOffset = summary.back; 
            // if the offset is invalid, then there is no further hierarchy and we are going to 
            if(treeOffset.isNull) 
            {
                // store a single value in this node. 
                back = front; 
                res = true; 
                static if(is(T == void))
                {
                    return res; 
                }
                else
                {
                    value = dataArr[1]; 
                    dataArr[1] = dataArr[0]; 
                    return value;
                }   
            }

            // otherwise we get maximum from the offset child 
            auto max = cluster[treeOffset.get].back; 
            assert(cluster[treeOffset.get].universe == lSR(universe.nextPow2));

            // remove it from the child 
            static if(is(T == void))
            {
                cluster[treeOffset.get].remove(max); 
            }
            else
            {
                auto maxValue = cluster[treeOffset.get].remove(max); 
            }
            

            // if it happens to become null during the remove process, we also remove the offset enty from the summary 
            assert(summary.universe == hSR(universe.nextPow2));
            if(cluster[treeOffset.get].empty) summary.remove(treeOffset.get); 

            // anyway, the new max of the current node become the restored value of the calculated offset. 
            static if(is(T == void))
            {
                back(index(treeOffset.get, max)); 
            }
            else
            {
                value = dataArr[1]; 
                back(index(treeOffset.get, max), *maxValue); 
            }
            
            res = true; 
            static if(is(T == void))
            {
                return res; 
            }
            else
            {
                return value; 
            }
            
        }

        // if no condition was met we have to descend deeper. We get the offset by reducing the value to high(value, uS)
        auto treeOffset = high(key); 
        // and remove low(value, uS) from the offset child. 
        assert(cluster[treeOffset].universe == lSR(universe.nextPow2));

        static if(is(T == void))
        {
            res = cluster[treeOffset].remove(low(key)); 
        }
        else
        {
            auto prelength = cluster[treeOffset].length; 
            value = cluster[treeOffset].remove(low(key)); 
        }

        // if the cluster become null during the remove process we have to update the summary node. 
        assert(summary.universe == hSR(universe.nextPow2));
        if(cluster[treeOffset].empty)
        {
            summary.remove(treeOffset); 
        }

        static if(is(T == void))
        {
            return res; 
        }
        else
        {
            res = prelength > cluster[treeOffset].length; 
            return value; 
        }        
    }

    /**
    predecessor method. this method is called from class with a universe size given. It performs recursion calls
    until the universe size is reduced to the base size. Then the overloaded predecessor method is called. 
    */
    Response predecessor(size_t value) // @nogc nothrow
    {
        typeof(return) retVal; 

        // if descended so far, do not use other functionality any more. 
        if(isLeaf)
        {   
            if(!empty && (value != 0))
            {
                /*
                create a mask, which hides all higher bits of the stored value down to the given bit number, then apply
                bit search from the highest bit. 
                */
                auto maskedVal = *val & ((size_t(1) << value) - 1); 
                if(maskedVal != 0)
                {
                     retVal = bsr(maskedVal);
                }
            }
            return retVal; 
        }
        // if this node is empty, no predecessor can be found here or deeper in the tree
        if(empty)
        {
            return retVal; 
        }
        // if given value is greater then the stored max, the predecessor is max
        if(value > back)
        {
            return back; 
        }
        // if given value is less then the min, no predecessor exists. 
        if(value <= front)
        {
            return retVal; 
        }
        /*
        if none of the break conditions was met we have to descend further into the tree. 
        */
        auto childIndex = high(value); // calculate the child index by high(value, uS)
        auto minlow = cluster[childIndex].front; // look into the child for its minimum
        // if the minimum exists and the lowered given value is greater then the child's minimum
        if(!minlow.isNull && low(value) > minlow) 
        {
            // calculate an offset to continue with by asking the child on predecessor of the lowered value. 
            assert(cluster[childIndex].universe == lSR(universe.nextPow2));
            auto offset = cluster[childIndex].predecessor(low(value)); 
            // the result is given by reconstruction of the answer. 
            retVal = index(childIndex, offset); 
        }
        else // otherwise we can not use the minimum of the child 
        {
            // ask the summary for the predecessor cluster. 
            assert(summary.universe == hSR(universe.nextPow2)); 
            auto predcluster = summary.predecessor(childIndex);
            // if the predecessor cluster is null return the current min, as this is the last remaining value 
            if(predcluster.isNull) return front; 
            // if the predecessor cluster exists, the offset is given by its maximum
            // and the result by the reconstruction of the offset. 
            retVal = index(predcluster, cluster[predcluster].back); 
        }
        return retVal; 
    }

    /**
    successor method. this method is called from class with a universe size given. It performs recursion calls until
    the universe size is reduced to the base size. Then the overloaded successor method is called. 
    */
    Response successor(size_t value) //@nogc nothrow 
    {
        // if descended so far, do not use other functionality any more. 
        typeof(return) retVal; 
        if(isLeaf)
        {        
            if(!empty && (value + 1 < baseSize)) 
            {
                // create a mask, which hides all lower bits of the stored value up to the given bit number, then apply
                // bit search from the lowest bit. 
                auto maskedVal = *val & ~((size_t(1) << (value + 1)) - 1); 
                if(maskedVal != 0) retVal = bsf(maskedVal);
            }
            return retVal; 
        } 
        if(empty) return retVal; // if this node is empty, no successor can be found here or deeper in the tree
        if(value < front) return front; // if given value is less then the min, return the min as successor
        if(value >= back) return retVal; // if given value is greater then the max, no predecessor exists
        
        /*
            if none of the break conditions was met, we have to descent further into the tree. 
        */
        auto childIndex = high(value); // calculate the child index by high(value, uS)
        auto maxlow = cluster[childIndex].back; // look into the child for its maximum
        // if the maximum exists and the lowered given value is less then the child's maximum 
        if(!maxlow.isNull && low(value) < maxlow)
        {
            // calculate an offset to continue with by asking the child on predecessor of the lowered value
            assert(cluster[childIndex].universe == lSR(universe.nextPow2));
            auto offset = cluster[childIndex].successor(low(value)); 
            // the result is given by reconstruction of the answer
            retVal = index(childIndex, offset);
        }
        else // otherwise we can not use the maximum of the child 
        {
            // ask the summary for the successor cluster. 
            assert(summary.universe == hSR(universe.nextPow2)); 
            auto succcluster = summary.successor(childIndex); 
            // if the successor cluster is null
            if(succcluster.isNull) return back; // return the current max, as this is the last remaining value 
            // if the successor cluster exists, the offset is given by its minimum
            // and the result by the reconstruction of the offset. 
            retVal = index(succcluster, cluster[succcluster].front); 
        }
        return retVal; 
    }

    // comparing to its range does not need another operator (?) ok... 
    /* 
    bool opEquals(S)(auto ref const S slice) const if(is(TemplateOf!(S) == VEBtree))
    {
        assert(0); 
    }
    */


    bool opEquals(O)(ref const O input) const if(is(Unqual!O == Unqual!(typeof(this))))
    {
        // short circuit, if pointers are the same
        if(stats == input.stats)
        {
            assert(val == input.val); 
            return true; 
        }

        // otherwise we have to check the whole structure.
        if(*stats != *input.stats)
        {
            return false; 
        }
        if(*val != *input.val)
        {
            return false; 
        }
        if(!isLeaf)
        {
            if(summary != input.summary)
            {
                return false; 
            }
            foreach(i, ref c; cluster)
            {
                if(c != input.cluster[i])
                {
                    return false; 
                }
            }    
        }
        else
        {
            if(!input.isLeaf)
            {
                return false; 
            }
        }
        return true; 
    }

    private: 
    /*
    This pointer acts as an array to nodes like this one. As the universe size is not provided, the length of the
    array can not be used to calculate the most of operations, so no explicit array is needed. The only remaining
    property is whether the pointer is set at all. From this property the node can decide, whether it is a leaf or
    an intermediate node. // the first member behaves different, as the others, as it is the summary node. 
    */

    static if(!is(T == void))
    {
        T** dataArr; 
        typeof(this)* ptrArr; 
    }
    else
    {
        typeof(this)[] ptrArr; 
    }
    
    // contains max and min, or the bit array of keys
    size_t* val;
    // contains universe size and the current length
    size_t* stats; 
    
    // property returning the summary node 
    @property auto ref summary() inout// @nogc nothrow 
    in
    {
        assert(!isLeaf);
    }
    do
    {
        return ptrArr[0];
    }
    
    // property returning the cluster array 
    @property auto ref cluster() inout// @nogc nothrow 
    in
    {
        assert(!isLeaf);
    }
    do
    {
        return ptrArr[1 .. hSR(universe.nextPow2) + 1];
    }
    
    @property void universe(size_t input)
    in
    {
        assert(stats !is null); 
        assert(input < maxSizeBound);
    }
    do
    {
        *stats = *stats & lowerMask; 
        *stats = *stats | (input << (size_t.sizeof * CHAR_BIT/2));
    }

    @property void length(size_t input)
    in
    {
        assert(stats !is null); 
        assert(input < maxSizeBound);
    }
    do
    {
        *stats = *stats & higherMask; 
        *stats = *stats | input; 
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
    this(size_t uS) // nothrow 
    {
        stats = new size_t(); 
        val = new size_t(); 

        universe = uS; 

        static if(!is(T == void))
        {
            T*[] tmpDataArr;
        }
        
        assert(stats !is null); 
        if(universe > baseSize)
        {
            // reserve enough place for the summary and the children cluster
            typeof(this)[] tmpArr; 
            assert(stats !is null); 
            tmpArr.length = hSR(universe.nextPow2) + 1; 
            
            static if(!is(T == void))
            {
                ptrArr = tmpArr.ptr;
                tmpDataArr.length = 2; 
            }
            else
            {
                ptrArr = tmpArr;
            }

            // add the summary with its universe of higher squaure root of the current universe
            assert(stats !is null); 
            summary = typeof(this)(hSR(universe.nextPow2)); 
            assert(stats !is null); 
            assert(ptrArr[0].stats !is null); 
            assert(ptrArr[0].universe == hSR(universe.nextPow2));
            // add higher square root children with lower square root universe each.
            assert(stats !is null); 

            cluster.each!((ref el) => el = typeof(this)(lSR(universe.nextPow2)));
            assert(stats !is null); 
            ptrArr[1 .. hSR(universe.nextPow2) + 1].each!((ref el) => assert(el.universe == lSR(universe.nextPow2)));
            
        }
        else
        {
            static if(!is(T == void))
            {
                tmpDataArr.length = baseSize; 
            }
        }
        static if(!is(T == void))
        {
            dataArr = tmpDataArr.ptr; 
        }
        nullify; // set the value to the sentinel value to represent the empty state. 
    }

    /** convinience method to check, if the node belongs to the lowest level in the tree */
    @property bool isLeaf() const // @nogc nothrow 
    in
    {
        assert(stats !is null); 
    }
    do
    {
        return universe <= baseSize;
    }

    /** method executing the appropriate steps to nullify the current node */
    @property auto nullify() // @nogc nothrow 
    in
    {
        assert(val !is null); 
    }
    do
    {
        if(isLeaf)
        {
            *val = 0; 
        }
        else
        {
            *val = 1; 
        }

        static if(!is(T == void))
        {
            T* retVal; 
            if(isLeaf)
            {
                foreach(el; dataArr[0 .. baseSize])
                {
                    if(el !is null)
                    {
                        assert(retVal is null); 
                        retVal = el; 
                        version(release)
                        {
                            break; 
                        }
                    }
                }
                dataArr[0 .. baseSize] = null; 
            }
            else
            {
                assert(dataArr[0] == dataArr[1]); 
                retVal = dataArr[0]; 
                dataArr[0 .. 2] = null; 
                
            }
            return retVal; 
        }
    }  

    /**
    setter for the min, setting either the lowest bit or the min part of the value. 
    */
    @property void front(T...)(size_t key, ref T value) 
        if((is(T == void) && T.length == 0) || (!is(T == void) && T.length < 2))// @nogc nothrow 
    {
        if(isLeaf)
        {
            assert(front > key);
            insert(key, value); 
        }
        else
        {
            // the passed value should not exceed the allowed size of a size/2
            assert(key < maxSizeBound);
            *val = *val & higherMask;
            *val = *val | key;
            static if(T.length)
            {
                dataArr[0] = &value[0];
            }
        }
    }

    /**
    setter for the max, setting either the highest bit or the max part of the value. 
    */
    @property void back(T...)(size_t key, ref T value) 
        if((is(T == void) && T.length == 0) || (!is(T == void) && T.length < 2))// @nogc nothrow 
    {
        if(isLeaf) 
        {
            assert(back < key); 
            insert(key, value); 
        }
        else
        {
            // the passed value should not exceed the allowed size of a size/2
            assert(key < maxSizeBound); 
            *val = *val & lowerMask; 
            *val = *val | (key << (size_t.sizeof * CHAR_BIT/2));
            static if(T.length)
            {
                dataArr[1] = &value[0]; 
            }
        }
    }

    size_t low(size_t key) //@nogc nothrow
    {
        return .low(universe.nextPow2, key); 
    }

    size_t high(size_t key) //@nogc nothrow 
    {
        return .high(universe.nextPow2, key); 
    }

    size_t index(size_t x, size_t y) //@nogc nothrow 
    {
        return .index(universe.nextPow2, x, y); 
    }
}

///
unittest
{
    
    auto vN = vebRoot(baseSize); 
    assert(vN.empty); 
    static assert(vN.sizeof == 4 * size_t.sizeof); 
    assert(vN.isLeaf); 
    assert(vN.empty); 
    *vN.val = 3; 
    assert(vN.front == 0);
    assert(1 in vN);
    assert(!(2 in vN));
    assert(vN.isLeaf);
    assert(vN.ptrArr == null); 
    vN.nullify; 
    assert(vN.empty); 
    assert(*vN.val == 0); 
    
}

///
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
    auto vT3 = vT.dup(); 
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

///
unittest
{
    
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: vT, [], ()        "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator

    auto M = uniform(2U,testedSize, rndGenInUse); //set universe size to some integer. 
    auto vT = vebRoot(M); //create the tree
    assert(M.iota.map!(i => vT.insert(uniform(0, vT.universe, rndGenInUse))).sum == vT.length); 
    
    assert(vT[].front == 0); 
    assert(vT[].back == vT.universe); 
    
}
///
unittest
{
    
    auto vT = vebRoot(1000); 
    assert(vT.capacity == 1024); 
    assert(vT.front.isNull); 
    assert(vT.insert(2)); 
    assert(vT.insert(5));
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
    
    //TODO: reactivate this by slicing assert(vT[].predecessor(2) == 0); 
    
    assert(vT.predecessor(2).isNull); 
    
    assert(vT.successor(6) == 8); 
    assert(vT.successor(5) == 8); 
    
    assert(vT.successor(4) == 5); 
    assert(vT.successor(1) == 2); 
    assert(vT.successor(75) == 88); 
    assert(vT.successor(90).isNull); 
    //TODO: reactivate this by slicing assert(vT[].successor(90) == vT.universe);
    
    assert(!(1029 in vT)); 
    
    assert(vT.successor(1025).isNull);
    assert(vT.successor(1025).isNull);
    
    auto vT2 = vebRoot(500); 
    assert(vT2.empty); 
    vT2.insert(50); 
    vT2.insert(500); 
    assert(vT2.back == 500); 
    assert(vT2.front == 50); 
    assert(vT2.successor(40) == 50);
    assert(vT2.successor(50) == 500); 
    
    vT2 = vebRoot(500); 
    assert(vT2.empty); 
    vT2.insert(50); 
    vT2.insert(500); 
    assert(vT2.back == 500); 
    assert(vT2.front == 50); 
    assert(vT2.successor(40) == 50);
    assert(vT2.successor(50) == 500); 

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

///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: rand, succ        "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator

    auto M = uniform(2U,testedSize, rndGenInUse); //set universe size to some integer. 
    auto vT = vebRoot(M); //create the tree
    assert(vT.capacity == nextPow2(M-1)); 

    auto filled = M.iota.map!(i => vT.insert(uniform(0, vT.universe, rndGenInUse))).sum; 
    assert(filled == vT.length); 

    size_t n; 
    auto i = vT.back; 

    // discover the thousend (or little less) values with the predecessor method
    while(!i.isNull)
    {
        ++n;
        i = vT.predecessor(i); 
        if(n > filled) break; 
    }
    
    size_t o;
    i = vT.front; 
    while(!i.isNull)
    {
        ++o; 
        i = vT.successor(i.get);
        if(o - 1 > filled) break; 
    }
    
    // assert, that all members are discovered, iff when no predecessors are left
    assert(n == filled); 
    assert(o == filled); 
}

///
unittest
{
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, pred        "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    assert(M.iota.map!(i => vT.insert(uniform(0, vT.universe, rndGenInUse))).sum == vT.length); 
    auto i = vT.back; 

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
    static if(vdebug){write("UT: rand, remove      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    assert(M.iota.map!(i => vT.insert(uniform(0, vT.universe, rndGenInUse))).sum == vT.length); 
    auto i = vT.front;
    
    // remove all members beginning from the minimum
    bool result; 
    while(!i.isNull)
    {        
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
    auto M = testedSize; 
    auto vT = vebRoot(M); 
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
    auto M = testedSize; 
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

/// 
unittest
{
    //stress test
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, stress      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    // last test says: see below. 
    auto M = uniform(2U, allowedArraySize, rndGenInUse); // set universe size to some integer. 
    auto vT = vebRoot(M); 

    size_t[] arr; 
    arr.length = 31 * vT.capacity/typeof(vT).sizeof; 
    (vT.capacity - 1).iota.randomCover(rndGenInUse).take(arr.length)
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
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, member      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer.
    size_t[] sourceArr; 
    sourceArr.length = M; 
    // generate a random array as the source for the tree
    iota(M).each!(i => sourceArr[i] = uniform(0U, M, rndGenInUse));
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

///
unittest
{
    auto currentSeed = unpredictableSeed();
    static if(vdebug){write("UT: rand, opSlice     "); writeln("seed: ", currentSeed);}  
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 16", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    auto M = uniform(2U, allowedArraySize, rndGenInUse); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    size_t[] arr; 
    arr.length = 16 * vT.capacity/typeof(vT).sizeof; 
    (vT.capacity - 1).iota.randomCover(rndGenInUse).take(arr.length)
            .enumerate
            .tee!(el => arr[el.index] = el.value)
            .each!(el => vT.insert(el.value));

    assert(setSymmetricDifference(vT(), arr.sort).empty); 
}

///
unittest
{ 
    static assert(!isInputRange!(VEBroot!())); 
    static assert(isIterable!(VEBroot!()));
    static assert(isBidirectionalRange!(typeof(VEBroot!()[])));
    auto root = vebRoot!(size_t)(4);
    auto res = root[2];
    //static assert(is(typeof((typeof(VEBroot!(new size_t[0])[]) r) => r[0]))); 
}

///
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

///
unittest
{
    /*
    //another stress test
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: stress test 2  "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    
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
    //stress test
    auto currentSeed = unpredictableSeed(); 
    static if(vdebug){write("UT: rand, ranges      "); writeln("seed: ", currentSeed);} 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    // last test says: see below. 
    auto M = uniform(2U, testedSize, rndGenInUse); // set universe size to some integer. 
    auto vT = vebRoot(M); 
    /*testing the range methods*/
    assert(vT.empty); 
    
    size_t[] sourceArr; 
    sourceArr.length = uniform(2U, M, rndGenInUse); 
    iota(sourceArr.length).each!(i => sourceArr[i] = uniform(0U, sourceArr.length, rndGenInUse));
    
    auto uniqueArr = sourceArr.sort.uniq; 

    // constructor to test

    auto vTnew = vebRoot(sourceArr.length); 
    uniqueArr.each!(el => vTnew.insert(el)); 

    assert(!vTnew.empty); 
    assert(vTnew.length == uniqueArr.array.length); 
    auto vT2 = vTnew; 
    static assert(isIterable!(typeof(vTnew))); 
    auto slice = vTnew(); 
    assert(slice.front == uniqueArr.front); 
    assert(vTnew() == uniqueArr.array); 
    assert(!vTnew.empty);
    assert(!vT2.empty);

    size_t N = 100; 
    auto vT3 = vebRoot(N); 
    assert(vT3.empty); 
    auto unique3 = N.iota.map!(i => uniform(0U, N, rndGenInUse)).array.sort.uniq;
    unique3.each!(u => vT3.insert(u));
    unique3.each!(u => assert(u in vT3));
    assert(vT3.length == unique3.array.length); 
    auto sl3 = vT3[]; 
    
    if(unique3.array.front == 0 && unique3.array.back == vT3.universe)
    {
        assert(sl3.length == unique3.array.length);
    }
    else if(unique3.array.front == 0 || unique3.array.back == vT3.universe)
    {
        assert(sl3.length == unique3.array.length + 1);
    }
    else
    {
        assert(sl3.length == unique3.array.length + 2);
    }
    assert(sl3.length); 
    assert(!sl3.empty); 

    unique3.each!(u => vT3.remove(u));
    assert(vT3.empty); 
    

    //writeln(vT3[].array); 
    //* Works. Duration in debug mode: about 35 seconds. 
    //auto vTT = vebRoot((size_t(1) << 27) - 1); 
    //assert(vTT.insert(42)); 
    //assert(42 in vTT);
    //*/
}

private struct VEBtree(Flag!"inclusive" inclusive, R : Root!Source, alias Root, Source...)
{
    static assert(isBidirectionalRange!(typeof(this)));
    
    R root; 
    
    auto  opBinaryRight(string op)(size_t key) if(op == "in")  // @nogc nothrow 
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
        Response frontKey; 
        Response backKey; 
    }

    size_t length; 
    
    private this(R val)
    {
        root = val;
        length = root.length; 

        static if(inclusive)
        {
            if(root.empty)
            {
                backKey = root.universe;
                assert(!length); 
                length += 2; 
            }
            else
            {
                if(root.back.get <= root.universe)
                {
                    backKey = root.universe;
                    if(root.back.get < root.universe)
                    {
                        length += 1; 
                    }
                }
                else
                {
                    assert(root.back.get < root.capacity); 
                    backKey = root.capacity; 
                    length += 1; 
                }

                if(root.front.get) // i. e. front != 0
                {
                    length += 1; 
                }
            }
        }
        else
        {
            frontKey = root.front; 
            backKey = root.back; 
        }
    }

    auto front()
    {
        return frontKey; 
    }

    auto popFront()
    in
    {
        assert(!empty); 
    }
    do
    {
        auto front = root.successor(frontKey.get); 
        static if(inclusive)
        {
            if(front.isNull)
            {
                frontKey = root.universe; 
            }
            else
            {
                frontKey = front.get; 
            }
        }
        else
        {
            frontKey = front; 
        }

        --length; 
    }

    auto back()
    {
        return backKey; 
    }

    auto popBack()
    in
    {
        assert(length); 
    }
    do
    {
        auto back = root.predecessor(backKey.get); 
        static if(inclusive)
        {      
            if(back.isNull)
            {
                backKey = 0; 
            }
        }
        else
        {
            backKey = back; 
        }
        --length; 
    }

    auto predecessor(size_t key)
    {
        return root.predecessor(key); 
    }

    auto successor(size_t key)
    {
        return root.successor(key); 
    }
    
    static if(!is(Source[0] == void))
    {
        static assert(!is(Source[0] == void));
        auto ref opIndex(size_t key) //@nogc
        {
            return root[key]; 
        }

        /**
        opApply method in case of present source for iterating over key value pairs
        */
        int opApply(scope int delegate(size_t, ref Source[0]) /*@nogc*/ operations) //@nogc
        {
            int result; 
            
            //for(auto leading = front; !leading.isNull; leading = successor(leading.get)) 
            for(auto leading = front; !empty; popFront) 
            {
                result = operations(leading.get, *root[leading.get]); 

                if(result)
                {
                    break; 
                }
            }

            return result;
        }

        /**
        opApply method in case of present source for iterating over key value pairs
        */
        int opApply(scope int delegate(size_t) /*@nogc*/ operations) //@nogc
        {
            int result; 
            
            //for(auto leading = front; !leading.isNull; leading = successor(leading.get)) 
            for(auto leading = front; !empty; popFront) 
            {
                result = operations(leading.get); 

                if(result)
                {
                    break; 
                }
            }

            return result;
        }
    }
    
    bool empty()
    {
        return !length; 
    }

    auto save()
    {
        return this; 
    }
    
    typeof(this) dup()
    {
        auto copy = this; 
        copy.root = root.dup; 
        return copy; 
    }

    size_t toHash()
    {
        assert(0);
    }

    /**
    for comparison with an iterable, the iterable will be iterated, as the current object. If the iterable object is an 
    input range, it will be destroyed. 
    */
    bool opEquals(T)(auto ref T input) if(isIterable!T)
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
            if(el != copy.front.get)
            {
                return false; 
            }
            copy.popFront; 
        }
        
        return true; 
    }
}

private : 
size_t get(size_t input) @nogc
{
    return input; 
}
bool isNull(size_t input) @nogc
{
    return false; 
}