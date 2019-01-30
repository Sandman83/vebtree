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
import vebtree.vebroot;
import std.traits : TemplateOf;

version (unittest)
{
    import std.parallelism : parallel;
    import std.conv : to;
    import core.stdc.stdio : printf;
    import std.container.rbtree : redBlackTree;
}

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
As a usual container, van Emde Boas tree provides the notion of capacity
*/
size_t capacity(T)(const ref T root) @nogc
{
    if (root.isLeaf) // pass control to the node
        return root.capacityImpl;
    return (root.universe - 1).nextPow2;
}

/**
The universe used for initializing is stored within the van Emde Boas tree. 
*/
size_t universe(T)(ref T root) @nogc
{
    return root.universe_; // the value is saved in each node, as defined in Cormen
}

static foreach (_; 1 .. size_t.sizeof - 1)
{
    ///
    unittest
    {
        foreach (b; (CHAR_BIT * size_t.sizeof * testMultiplier).iota.parallel)
        {
            auto currentSeed = unpredictableSeed();
            size_t M;
            auto vT = generateVEBtree!("UT: black box test capacity and universe: ", 1 << _)
                    (b, currentSeed, CHAR_BIT * size_t.sizeof, CHAR_BIT * size_t.sizeof * CHAR_BIT * size_t.sizeof, M);
            assert(vT.universe == M);
            assert(vT.capacity == (vT.universe - 1).nextPow2,
                    to!string("vT.capacity: " ~ to!string(
                        vT.capacity) ~ " vT.universe: " ~ to!string(vT.universe)));
        }
    }
}

/**
The predecessor search method of the van Emde Boas tree. 
*/
size_t prev(T)(ref T root, size_t val) @nogc
{
    if (root.empty) // do not proceed at all, if the root is empty
        return NIL;
    if (root.isLeaf) // pass control to the node
        return root.prevImpl(val);
    // if given value is greater then the stored max, the predecessor is max
    if (val > root.max)
        return root.max;
    // if given value is less then the min, no predecessor exists. 
    if (val <= root.min)
        return NIL;
    // if none of the break conditions was met we have to descend further into the tree. 
    auto childIndex = root.high(val); // calculate the child index by high(value, uS)
    const minlow = root.cluster[childIndex].min; // look into the child for its minimum
    // if the minimum exists and the lowered given value is greater then the child's minimum
    if ((minlow != NIL) && (root.low(val) > minlow))
    {
        auto offset = root.cluster[childIndex].prev(root.low(val));
        // the result is given by reconstruction of the answer. 
        return root.index(childIndex, offset);
    }
    else // otherwise we can not use the minimum of the child 
    {
        auto predcluster = root.summary.prev(childIndex);
        // if the predecessor cluster is null return the current min, as this is the last remaining value 
        if (predcluster == NIL)
            return root.min;
        // if the predecessor cluster exists, the offset is given by its maximum
        // and the result by the reconstruction of the offset. 
        return root.index(predcluster, root.cluster[predcluster].max);
    }
}

/**
The successor search method of the van Emde Boas tree. 
*/
size_t next(T)(const ref T root, size_t val) @nogc
{
    if (root.empty) // do not proceed at all, if the root is empty
        return NIL;
    if (root.isLeaf) // pass control to the node
        return root.nextImpl(val);
    // if given value is less then the min, return the min as successor
    if (val < root.min)
        return root.min;
    // if given value is greater then the max, no predecessor exists
    if (val >= root.max)
        return NIL;
    // if none of the break conditions was met, we have to descent further into the tree. 
    // calculate the child index by high(value, uS)
    const childIndex = root.high(val);
    // look into the child for its maximum
    const maxlow = root.cluster[childIndex].max;
    // if the maximum exists and the lowered given value is less then the child's maximum 
    if ((maxlow != NIL) && (root.low(val) < maxlow))
    {
        auto offset = root.cluster[childIndex].next(root.low(val));
        // the result is given by reconstruction of the answer
        return root.index(childIndex, offset);
    }
    else // otherwise we can not use the maximum of the child 
    {
        auto succcluster = root.summary.next(childIndex);
        // if the successor cluster is null
        if (succcluster == NIL)
            return root.max;
        assert(succcluster != NIL);
        assert(root.cluster[succcluster].min != NIL);
        // if the successor cluster exists, the offset is given by its minimum
        // and the result by the reconstruction of the offset. 
        return root.index(succcluster, root.cluster[succcluster].min);
    }
}

/**
The maximal contained key in the van Emde Boas tree
*/
size_t max(T)(const ref T root) @nogc
{
    if (root.empty) // do not proceed at all, if the root is empty
        return NIL;
    if (root.isLeaf) // pass control to the node
        return root.maxImpl;
    return (root.value_ & higherMask) >> (CHAR_BIT * size_t.sizeof / 2);
}

/**
The minimal contained key in the van Emde Boas tree
*/
size_t min(T)(const ref T root) @nogc
{
    if (root.empty) // do not proceed at all, if the root is empty
        return NIL;
    if (root.isLeaf) // pass control to the node
        return root.minImpl;
    return root.value_ & lowerMask;
}

/**
The insertion method of the van Emde Boas tree. 
*/
bool insert(T)(ref T root, size_t val)
{
    if (val >= root.capacity) // do not proceed at all, if the value won't fit into the tree 
        return false;
    if (root.isLeaf) // pass control to the node
        return root.insertImpl(val);
    if (root.empty) // if the current node does not contain anything put the value inside. 
    {
        assert(root.empty);
        root.min = val;
        root.max = val;
        assert(root.min == val);
        assert(!root.empty);
        assert(root.min == root.max);
        assert(!root.empty);
        return root.length(root.length + 1);
    }

    assert(!root.empty);
    assert(root.min != NIL);
    assert(root.max != NIL);

    if (val == root.min || val == root.max) // if the value coincides with existing values, return 
        return false;
    // if the node contains a single value only, expand the node to a range and leave. 
    if (root.min == root.max)
    {
        if (root.min > val)
            root.min = val;
        if (root.max < val)
            root.max = val;
        return root.length(root.length + 1);
    }
    /*
        if none of the cases above was true (all of them are break conditions) we have to compare the given value
        with the values present and adapt the range limits. This replaces the value we want to insert. 
    */

    // a swap can not be used here, as min is itself a (property) method 
    if (val < root.min)
    {
        const tmpKey = val;
        val = root.min;
        root.min = tmpKey;
        assert(root.min == tmpKey);
    }

    // a swap can not be used here, as max is itself a (property) method 
    if (val > root.max)
    {
        const tmpKey = val;
        val = root.max;
        root.max = tmpKey;
        assert(root.max == tmpKey);
    }

    // calculate the index of the children cluster by high(value, uS) we want to descent to. 
    const nextTreeIndex = root.high(val);
    if (root.cluster[nextTreeIndex].empty)
        root.summary.insert(nextTreeIndex);
    return root.length(root.length + root.cluster[nextTreeIndex].insert(root.low(val)));
}

/**
remove method of the van Emde Boas tree
*/
bool remove(T)(ref T root, size_t val)
{
    if (val >= root.capacity) // do not proceed at all, if the value can't be in the tree 
        return false;
    if (root.empty) // do not proceed at all, if the root is empty
        return false;
    if (root.isLeaf) // pass control to the node
        return root.removeImpl(val);
    if (root.min == root.max) // if the current node contains only a single value
    {
        assert(root.length == 1);
        if (root.min != val)
            return false; // do nothing if the given value is not the stored one 
        assert(root.length == 1);
        return root.length(root.length - 1);
    }

    if (val == root.min) // if we met the minimum of a node 
    {
        auto treeOffset = root.summary.min; // calculate an offset from the summary to continue with        
        if (treeOffset == NIL) // if the offset is invalid, then there is no further hierarchy and we are going to 
        {
            root.min = root.max; // store a single value in this node. 
            assert(root.length == 2);
            return root.length(root.length - 1);
        }
        auto m = root.cluster[treeOffset].min; // otherwise we get the minimum from the offset child
        // remove it from the child 
        root.cluster[treeOffset].remove(m);
        if (root.cluster[treeOffset].empty)
            root.summary.remove(treeOffset);
        //anyway, the new min of the current node become the restored value of the calculated offset. 
        root.min = root.index(treeOffset, m);
        assert(root.length);
        return root.length(root.length - 1);
    }
    
    if (val == root.max) // if we met the maximum of a node 
    {
        // calculate an offset from the summary to contiue with 
        auto treeOffset = root.summary.max;
        // if the offset is invalid, then there is no further hierarchy and we are going to 
        if (treeOffset == NIL)
        {
            // store a single value in this node. 
            root.max = root.min;
            assert(root.length == 2);
            return root.length(root.length - 1);
        }
        // otherwise we get maximum from the offset child 
        auto m = root.cluster[treeOffset].max;
        // remove it from the child 
        root.cluster[treeOffset].remove(m);
        if (root.cluster[treeOffset].empty)
            root.summary.remove(treeOffset);
        // anyway, the new max of the current node become the restored value of the calculated offset. 
        root.max = root.index(treeOffset, m);
        assert(root.length);
        return root.length(root.length - 1);
    }
    // if no condition was met we have to descend deeper. We get the offset by reducing the value to high(value, uS)
    auto treeOffset = root.high(val);
    auto res = root.length(root.length - root.cluster[treeOffset].remove(root.low(val)));
    if (root.cluster[treeOffset].empty)
        root.summary.remove(treeOffset);
    return res;
}

static foreach (_; 1 .. size_t.sizeof - 1)
{
    ///
    unittest
    {
        foreach (b; (CHAR_BIT * size_t.sizeof * testMultiplier).iota.parallel)
        {
            auto currentSeed = unpredictableSeed();
            size_t M;
            auto vT = generateVEBtree!("UT: black box test outer interface: ", 1 << _)(b, currentSeed,
                    CHAR_BIT * size_t.sizeof, CHAR_BIT * size_t.sizeof * CHAR_BIT * size_t.sizeof,
                    M);
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

            auto rbt = redBlackTree!size_t();

            foreach (val; testArray)
            {
                assert(vT.universe == M);
                assert(vT.length == rbt.length);

                bool insertExpectation;
                if (val < vT.capacity && !(val in vT))
                {
                    insertExpectation = true;
                }

                /*
                if(debugFunction == "insert")
                {
                    trace("val: ", val);
                }
                */

                const insertResult = vT.insert(val);

                assert(insertResult == insertExpectation);

                if (insertResult)
                {

                    assert(val in vT);
                    assert(!vT.empty);
                    rbt.insert(val);

                    /*
                    if(debugNumbers.canFind(val) && debugFunction == "insert")
                    {
                        trace("val: ", val, 
                            " vT.min: ", vT.min, 
                            " vT.max: ", vT.max, 
                            " rbt.front: ", rbt.front, 
                            " rbt.back: ", rbt.back
                        );
                    }
                    */

                    assert(vT.min == rbt.front);
                    assert(vT.max == rbt.back,
                            "val:" ~ to!string(val) ~ " vT.max: " ~ to!string(
                                vT.max) ~ " rbt.back: " ~ to!string(rbt.back));

                    cacheArray ~= val;
                }
                else
                {
                    if (!(val in rbt))
                    {
                        assert(!(val in vT));
                    }
                    else
                    {
                        assert(val in vT);
                    }
                }
            }

            cacheArray.sort;

            foreach (i, el; cacheArray)
            {
                assert(el in vT);
                if (i + 1 != cacheArray.length)
                {
                    assert(vT.next(el) == cacheArray[i + 1]);
                }
                else
                {
                    assert(vT.next(el) == NIL);
                }
            }

            foreach (i, el; cacheArray.retro.enumerate)
            {
                assert(el in vT);
                if (i + 1 != cacheArray.length)
                {
                    assert(vT.prev(el) == cacheArray[($ - 1) - (i + 1)]);
                }
                else
                {
                    assert(vT.prev(el) == NIL);
                }
            }

            foreach (val; testArray)
            {
                assert(vT.length == rbt.length);

                /*
                if(debugFunction == "remove")
                {
                    trace("val: ", val);
                }
                */

                /*
                if(debugNumbers.canFind(val) && debugFunction == "remove")
                {
                    trace("val: ", val, 
                        " vT.min: ", vT.min, 
                        " vT.max: ", vT.max, 
                        " rbt.front: ", rbt.front, 
                        " rbt.back: ", rbt.back
                    );
                }
                */
                if (val in rbt)
                {
                    assert(val in vT);

                    /*
                    if(debugNumbers.canFind(val) && debugFunction == "remove")
                    {
                        trace("... existing");
                    }
                    */

                    rbt.removeKey(val);
                    assert(vT.remove(val));
                }
                else
                {
                    assert(!(val in vT));

                    /*
                    if(debugNumbers.canFind(val) && debugFunction == "remove")
                    {
                        trace("... non-existing");
                    }
                    */

                    assert(!vT.remove(val));
                }
                assert(!(val in rbt));
                assert(!(val in vT));
            }
            assert(vT.length == 0);
            assert(rbt.length == 0);
        }
    }
}

/**
the empty method to inform of an empty state of the tree. 
*/
bool empty(T)(ref T root) @nogc if (__traits(isSame, TemplateOf!T, VEBroot))
{
    if (root.isLeaf) 
        return root.emptyImpl; // pass control to the node
    return root.value_ == -NIL;
}

private:
bool min(T)(ref T root, size_t val)
{
    if (root.isLeaf) // pass control to the node
        return root.minImpl(val);
    root.value_ = root.value_ & higherMask; // otherwise, set the lower part of the value, keeping the higher bits
    const retVal = ((root.value_ & lowerMask) == val) ? false : true;
    root.value_ = root.value_ | val;
    return retVal; // this is a bug!
}

bool max(T)(ref T root, size_t val)
{
    if (root.isLeaf) // pass control to the node
        return root.maxImpl(val);
    root.value_ = root.value_ & lowerMask; // otherwise, set the higher part of the value, keeping the lower bits
    const retVal = (root.value_ & higherMask) == (val << (CHAR_BIT * size_t.sizeof / 2)) ? false : true;
    root.value_ = root.value_ | (val << (CHAR_BIT * size_t.sizeof / 2));
    return retVal; // this is a bug!
}

ref summary(T)(inout ref T root)
in(!root.isLeaf)
{ // return the last element of the array of children, stored in the node. 
    return root.ptr_[root.capacity.hSR];
}

auto cluster(T)(inout ref T root)
in(!root.isLeaf)
{ // return all of the children in the stored array, but the last element 
    return root.ptr_[0 .. root.capacity.hSR];
}