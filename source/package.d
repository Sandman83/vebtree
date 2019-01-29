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
For optimization purposes, the size limit is halfSizeT.max + 1. The tree was tested on 64- and 32-bit arch. 
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
i$(RPAREN) to keep the size of a single node also depending from the underlying architecture. 
ii$(RPAREN) for bitoperations, which the tree is relying on, to use the native word size of the architecture without
emulating bigger entities. 
*/

//extern(C) __gshared string[] rt_options = [ "gcopt=gc:precise" ];
//gc:conservative|precise|manual
//"--DRT-gcopt=profile:1 minPoolSize:16"

module vebtree; 
public import vebtree.root; 
import std.typecons : Flag, Yes, No; 
import std.experimental.logger; 

/**
As a usual container, van Emde Boas tree provides the notion of capacity
*/
size_t capacity(T)(const ref T root) @nogc
{
    //mixin(condImplCall!(__FUNCTION__, ""));
    if(root.isLeaf) return root.capacityImpl; 
    return (root.universe-1).nextPow2;    
}
///
static foreach(_; 1 .. size_t.sizeof - 1)
{
    unittest
    {
        foreach(b; (defaultBaseSize * testMultiplier).iota)
        {
            auto currentSeed = unpredictableSeed();
            
            size_t M; 
            auto vT = generateVEBtree!("UT: black box test capacity: ", 1 << _)
                (b, currentSeed, defaultBaseSize, defaultBaseSize * defaultBaseSize, M);
            import std.conv : to; 
            assert(vT.capacity == (M - 1).nextPow2,
                to!string("vT.capacity: " ~ to!string(vT.capacity) ~ " M: " ~ to!string(M)));
        }
    }
}


/**
The universe used for initializing is stored within the van Emde Boas tree. 
*/
size_t universe(T)(ref T root) @nogc
{
    return root.universe_; 
}
///
static foreach(_; 1 .. size_t.sizeof - 1)
{
    unittest
    {
        foreach(b; (defaultBaseSize * testMultiplier).iota)
        {
            auto currentSeed = unpredictableSeed();
            size_t M; 
            auto vT = generateVEBtree!("UT: black box test universe: ", 1 << _)
                    (b, currentSeed, defaultBaseSize, defaultBaseSize * defaultBaseSize, M);
            assert(vT.universe == M); 
        }
    }
}

/**
The predecessor search method of the van Emde Boas tree. 
*/
size_t prev(T)(ref T root, size_t val) @nogc
{
    if(root.empty) { return NIL; }
    //mixin(condImplCall!(__FUNCTION__));
    if(root.isLeaf) return root.prevImpl(val); 
    // if given value is greater then the stored max, the predecessor is max
    if(val > root.max)
    {
        return root.max; 
    }
    // if given value is less then the min, no predecessor exists. 
    if(val <= root.min)
    {
        return NIL;
    }
    /*
    if none of the break conditions was met we have to descend further into the tree. 
    */
    auto childIndex = root.high(val); // calculate the child index by high(value, uS)
    const minlow = root.cluster[childIndex].min; // look into the child for its minimum
    // if the minimum exists and the lowered given value is greater then the child's minimum
    if((minlow != NIL) && (root.low(val) > minlow))
    {
        auto offset = root.cluster[childIndex].prev(root.low(val)); 
        // the result is given by reconstruction of the answer. 
        return root.index(childIndex, offset); 
    }
    else // otherwise we can not use the minimum of the child 
    {
        auto predcluster = root.summary.prev(childIndex);
        // if the predecessor cluster is null return the current min, as this is the last remaining value 
        if(predcluster == NIL)
        {
            return root.min; 
        }
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
    if(root.empty) { return NIL; }
    //mixin(condImplCall!(__FUNCTION__));
    if(root.isLeaf) return root.nextImpl(val); 
    // if given value is less then the min, return the min as successor
    if(val < root.min) return root.min; 
    // if given value is greater then the max, no predecessor exists
    if(val >= root.max) return NIL; 
    // if none of the break conditions was met, we have to descent further into the tree. 
    // calculate the child index by high(value, uS)
    const childIndex = root.high(val); 
    // look into the child for its maximum
    const maxlow = root.cluster[childIndex].max; 
    // if the maximum exists and the lowered given value is less then the child's maximum 
    if((maxlow != NIL) && (root.low(val) < maxlow))
    {
        auto offset = root.cluster[childIndex].next(root.low(val)); 
        // the result is given by reconstruction of the answer
        return root.index(childIndex, offset);
    }
    else // otherwise we can not use the maximum of the child 
    {
        auto succcluster = root.summary.next(childIndex); 
        // if the successor cluster is null
        if(succcluster == NIL)
        {
            // return the current max, as this is the last remaining value
            return root.max; //? return nil?
        }
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
    if(root.empty) { return NIL; }
    //mixin(condImplCall!(__FUNCTION__, ""));
    if(root.isLeaf) return root.maxImpl; 
    return (root.value_ & higherMask) >> (defaultBaseSize/2);
}
/**
The minimal contained key in the van Emde Boas tree
*/
size_t min(T)(const ref T root) @nogc
{
    if(root.empty) { return NIL; } 
    //mixin(condImplCall!(__FUNCTION__, ""));
    if(root.isLeaf) return root.minImpl; 
    return root.value_ & lowerMask; 
}
/**
The insertion method of the van Emde Boas tree. 
*/
bool insert(T)(ref T root, size_t val)
{
    debug
    {
    }
    
    if(val >= root.capacity)
    {
        return false;
    }

    //mixin(condImplCall!(__FUNCTION__));
    if(root.isLeaf) return root.insertImpl(val); 

    if(root.empty) // if the current node does not contain anything put the value inside. 
    {
        min(root, val);
        max(root, val); 
        
        return root.length = root.length + 1; 
    }

    assert(!root.empty);
    assert(root.min != NIL); 
    assert(root.max != NIL); 

    if(val == root.min || val == root.max)
    {
        return false; 
    }

    if(root.min == root.max) // if the node contains a single value only, expand the node to a range and leave. 
    {
        if(root.min > val)
        {
            root.min = val; 
        }
        if(root.max < val)
        {
            root.max = val; 
        }
        
        return root.length = root.length + 1; 
    }
    /*
        if none of the cases above was true (all of them are break conditions) we have to compare the given value
        with the values present and adapt the range limits. This replaces the value we want to insert. 
    */
    // a swap can not be used here, as min is itself a (property) method 
    if(val < root.min)
    {
        const tmpKey = val; 

        val = root.min;

        root.min = tmpKey;
        
    }
    // a swap can not be used here, as max is itself a (property) method 
    if(val > root.max)
    {
        const tmpKey = val; 
        
        val = root.max; 
        
        root.max = tmpKey; 
    }
    
    // calculate the index of the children cluster by high(value, uS) we want to descent to. 
    auto nextTreeIndex = root.high(val); 
    
    if(root.cluster[nextTreeIndex].empty)
    {
        root.summary.insert(root.high(val));
    }
    return root.length = root.length + root.cluster[nextTreeIndex].insert(root.low(val)); 
}

/**
remove method of the van Emde Boas tree
*/
bool remove(T)(ref T root, size_t val)
{
    if(root.empty) return false; 
    //mixin(condImplCall!(__FUNCTION__));
    if(root.isLeaf) return root.removeImpl(val); 
    if(root.min == root.max) // if the current node contains only a single value
        {
            assert(root.length == 1);

            if(root.min != val)
            {
                // do nothing if the given value is not the stored one 
                return false; 
            } 

            root.nullify;

            assert(root.length); 
            return root.length = root.length - 1; 
        }

        if(val == root.min) // if we met the minimum of a node 
        {
            auto treeOffset = root.summary.min; // calculate an offset from the summary to continue with
            if(treeOffset == NIL) // if the offset is invalid, then there is no further hierarchy and we are going to 
            {
                root.min = root.max; // store a single value in this node. 
                
                assert(root.length); 
                return root.length = root.length - 1; 
            }
            auto min = root.cluster[treeOffset].min; // otherwise we get the minimum from the offset child

            // remove it from the child 
            root.cluster[treeOffset].remove(min); 
            
            if(root.cluster[treeOffset].empty)
            {
                root.summary.remove(treeOffset); 
            }

            //anyway, the new min of the current node become the restored value of the calculated offset. 
            root.min = root.index(treeOffset, min); 
            
            assert(root.length); 
            return root.length = root.length - 1; 
        }

        // if we met the maximum of a node 
        if(val == root.max) 
        {
            // calculate an offset from the summary to contiue with 
            auto treeOffset = root.summary.max; 
            // if the offset is invalid, then there is no further hierarchy and we are going to 
            if(treeOffset == NIL) 
            {
                // store a single value in this node. 
                root.max = root.min; 

                assert(root.length); 
                return (root.length = root.length - 1);
            }

            // otherwise we get maximum from the offset child 
            auto max = root.cluster[treeOffset].max; 

            // remove it from the child 
            root.cluster[treeOffset].remove(max); 

            if(root.cluster[treeOffset].empty) root.summary.remove(treeOffset); 

            // anyway, the new max of the current node become the restored value of the calculated offset. 
            root.max = root.index(treeOffset, max); 
            
            assert(root.length); 
            return root.length = root.length - 1; 
        }

        // if no condition was met we have to descend deeper. We get the offset by reducing the value to high(value, uS)
        auto treeOffset = root.high(val); 

        auto res = (root.length = root.length - root.cluster[treeOffset].remove(root.low(val))); 
        
        if(root.cluster[treeOffset].empty)
        {
            root.summary.remove(treeOffset); 
        }

        return res;
}

///
static foreach(_; 1 .. size_t.sizeof - 1)
{
    unittest
    {
        foreach(b; (defaultBaseSize * testMultiplier).iota)
        {
            
            auto currentSeed = unpredictableSeed();
            size_t M; 
            auto vT = generateVEBtree!("UT: black box test outer interface: ", 1 << _)
                    (b, currentSeed, defaultBaseSize, defaultBaseSize * defaultBaseSize, M);
            size_t N = uniform(0UL, 2 * M); // independent parameter for testing
            
            // make an array of length N
            size_t[] testArray = new size_t[N]; 
            // fill the array with all possible values 
            foreach(ref el; testArray)
            {
                el = vT.maxSizeBound.iota.choice;
            }

            
            
        }
    }
}

///
/+ TODO: 
static foreach(_; 0 .. baseSize * testMultiplier)
{
    /*
    unittest
    {
        auto currentSeed = unpredictableSeed();
        //currentSeed = 
        trace("UT: white box test #2: ", _, "; seed: ", currentSeed); 

        rndGen.seed(currentSeed); //initialize the random generator
        size_t M = uniform(baseSize, 2 * baseSize); // parameter for construction
        auto vT = vebRoot(M);

        assert(!(vT.ptr is null));
        assert(vT.empty == true);
        assert(vT.value_ == 0);
        assert(vT.min == NIL);
        assert(vT.max == NIL);
        assert(vT.length == 0); 
        if(powersOfTwo.canFind(M))
        {
            assert(vT.capacity == M); 
        }
        else
        {
            assert(vT.capacity == M.nextPow2); 
        }

        assert(vT[].front == 0);
        assert(vT[].back == vT.universe);
        assert(vT().front == NIL);
        assert(vT().back == NIL);
        assert(vT.length == 0);
        assert(vT.universe == M);

        size_t N = uniform(0U, baseSize); // independent parameter for testing
        auto testArray = (2 * M).iota.randomCover.array; 
        auto cacheArray = new size_t[N];
        
        size_t counter; 

        foreach(testNumber; testArray)
        {
            if(counter == N) break; 

            const insertResult = vT.insert(testNumber);
            
            if(insertResult)
            {
                assert(!vT.empty);
                cacheArray[counter] = testNumber;
                ++counter;
            }
        }
        
        auto originalCacheArray = cacheArray.dup; 
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
            if(cacheArray.uniq.array.canFind(val))
            {
                assert(val in vT); 
            }
            else
            {
                assert(!(val in vT));
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
            vT.remove(valToRemove);
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
        
        foreach(val; 0 .. vT.capacity)
        {
            if(cacheArray.uniq.array.canFind(val))
            {
                assert(vT.remove(val)); 
            }
            else
            {
                assert(!(vT.remove(val)));
            }
        }
        assert(vT.value_ == 0); 
        assert(vT.empty);
    }
    */
}
+/

private: 
bool min(T)(ref T root, size_t val)
{
    if(root.min <= val){ return false; }
    //mixin(condImplCall!(__FUNCTION__));
    if(root.isLeaf) return root.minImpl(val); 
    root.value_ = root.value_ & higherMask;
    root.value_ = root.value_ | val;
    return true; 
}

bool max(T)(ref T root, size_t val)
{
    if(root.max >= val) { return false; }
    //mixin(condImplCall!(__FUNCTION__));
    if(root.isLeaf) return root.maxImpl(val); 
    root.value_ = root.value_ & lowerMask; 
    root.value_ = root.value_ | (val << (defaultBaseSize/2));
    return true;
}
/**
insert method. this method is called from class with a universe size given. It performs recursion calls untill
the universe size is reduced to the base size. Then the overloaded insert method is called. 
*/
bool nullify(T)(ref T root) @nogc
{
    root.filled_ = false; 
    //mixin(condImplCall!(__FUNCTION__, ""));
    if(root.isLeaf) return root.nullifyImpl; 
    return true; 
}
/*
template condImplCall(string FunName, string Arg = "val") //pragma(msg, ImplCall!(__FUNCTION__));
{
    import std.array : split, join; 
    enum condImplCall = "if(root.isLeaf) return root." ~ FunName.split(".")[1..$].join(".") ~ "Impl(" ~ Arg ~ ");";
}
*/