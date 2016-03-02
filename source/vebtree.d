/**
Copyright: Copyright (c) 2016- Alexander Orlov. All rights reserved.
License: $(LINK2 https://opensource.org/licenses/MIT, MIT License).
Authors: Alexander Orlov, $(LINK2 mailto:sascha.orlov@gmail.com, sascha.orlov@gmail.com) 
*/

/**
This module implements a Van Emde Boas tree container.

The module is still a work in progress. So, if you find an error by chance, please let me know in any way.

The main idea of the container is, to restrict the capacity of the tree by the next power of two universe size, given a
maximum element at the initialization. As long as the usage is intended to contains keys, as in the current version,
this restriction is not only a restriction of the amount of elements but also on the contained element values. 
*/

// TODO: provide functionality to contain non-unique keys, i. e. exercise 20.3.1 from Cormen
// TODO: provide functionality to contain associated data with the keys, i. e. exercise 20.3.2 from Cormen

/**
In this version, the maximum size of the universe possible is 2^32. With this restriction all unsigned integers could
be used as keys, if the appropriate maximum value is given on initialization. 

The main advantage of the Van Emde Boas tree appears on a large amount of elements, as the provided standard operations
of the tree are constant in time and of order O(lg2(lg2(U))), where U is the capacity of the tree. For small amount of
elements the overhead coming along with the structure take over. For example, for a universe size of 2^14 and 15872
insertion operatios the duration for the Van Emde Boas tree is about 1*10^(-3) times smaller. As one of the unittests
shows. 
*/

/**
Be aware, the current container is intended to be used with keys. This implies, that the capacity, fixed on its
initialization has two meanings. As usual, it shows the maximum amount of elements the instanciated tree can keep. But 
also, it states, that no value bigger then capacity - 1 exists in the tree. This, and the fact, that only non-negative 
values can be used are infered from the term "key".
*/

/**
See_also: Thomas H. Cormen, Clifford Stein, Ronald L. Rivest, and Charles E. Leiserson. 2001. <em>Introduction to
Algorithms</em> (2nd ed.). McGraw-Hill Higher Education.
*/

module vebtree; 

import std.typecons; /// used for Nullable!uint 
import core.bitop; 

version(unittest) { import std.random; Random rndGenInUse; }

// this would be useful in case of coding the keys as a bitfield
// enum uint WORD = uint.sizeof * 8;

// defines the base universe size of a tree node. 
ubyte BASE_SIZE = 2; 

// Convinience function to return the ceiling to the next power of two number of the given input. 
size_t nextPowerOfTwo(size_t value) { return 1 << (bsr(value) + 1); }
///
unittest
{
    assert(nextPowerOfTwo(1000) == 1024); 
}

/** 
This is the interface of a VEB tree. Besides the methods described below, the tree class implements the needed methods
for being a range. It is a bidirectional range with slice operations.
*/
interface Iveb
{
    //
    void insert(uint x); 
    void insert(uint[] arr); 
    //
    void remove(uint x); 
    //
    bool member(uint x); 
    //
    Nullable!uint min(); 
    //
    Nullable!uint max(); 
    //
    Nullable!uint successor(uint x); 
    //
    Nullable!uint predecessor(uint x); 
}

/*
This function returns the upper square root of the given input as integer. It is needed in the initialization step of
the VEB tree to calculate the number of children of a given layer. The upper square root is defined by 2^{\lceil(\lg
u)/2\rceil}
*/
uint higherSquareRoot(size_t value){return 1 << (value.lowerSqrtShift + (value > (1 << value.bsr) || value.bsr & 1));}
///
unittest
{
    assert(higherSquareRoot(5) == 4);
    assert(higherSquareRoot(17) == 8);
    assert(higherSquareRoot(88) == 16); 
    assert(higherSquareRoot(64) == 8); 
    assert(higherSquareRoot(128) == 16); 
}

/*
This function returns the floored log2 value of the input. This is done by counting up to the position of the leading
bit position and dividing this value by two. This method is needed both by the higher and lower square root
calculation. 
*/
uint lowerSqrtShift(size_t value) { return bsr(value)/2; }

/*
This function returns the lower square root of the given input as integer. It is needed by the indexing functions
high(x), low(x) and index(x,y) of elements in the tree. The lower square root is defined by 2^{\lfloor(\lg u)/2\rfloor}
*/
uint lowerSquareRoot(size_t value) { return 1 << lowerSqrtShift(value); }
///
unittest
{
    assert(lowerSquareRoot(5) == 2);
    assert(lowerSquareRoot(17) == 4);
    assert(lowerSquareRoot(88) == 8);
    assert(lowerSquareRoot(64) == 8); 
}

/*
This is an index function defined as \lfloor x/lowerSquareRoot(u)\rfloor. It is needed to find the appropriate cluster
of a element in the tree. 
*/
uint high(uint value, size_t universeSize) { return value/lowerSquareRoot(universeSize); }
///
unittest
{
    assert(.high(7,16) == 1); 
}

/*
This is an index function defined as fmod(value, lowerSquareRoot(universeSize)). It is needed to find the appropriate
value inside a cluster. 
*/
uint low(uint value, size_t universeSize){ return value & (lowerSquareRoot(universeSize) - 1); }
///
unittest
{
    assert(.low(7,16) == 3); 
}

/*
This is an index function to retain the searched value. It is defined as x * lowerSquareRoot(u) + y. Beyond this, the
relation holds: x = index(high(x), low(x))
*/
uint index(size_t universeSize, uint x, uint y){ return (x * lowerSquareRoot(universeSize) + y); }

/**
This is the class to represent a VEB tree node. As memebers it contains the universeSize, the min and the max value as
well as a link to a summary node and a cluster, which is a range of VEB tree nodes of size higherSquareRoot(u). Each
child node has a universe size of lowerSquareRoot(u)
*/
private struct vebNode
{    
    immutable size_t _universeSize;
    @property size_t universeSize(){ return _universeSize; }
    
    // min value is contained in the node as a separate value, this value can't be found in child nodes. 
    Nullable!uint _min; 
    @property void min(uint value){ _min = value; }
    @property Nullable!uint min() { return _min; }
    
    // max value is contained in the node as a separate value, this can be found in child nodes.
    Nullable!uint _max; 
    @property void max(uint value){ _max = value; }
    @property Nullable!uint max(){ return _max; }
    
    // the node is empty, iff neither min nor max is set. 
    @property bool empty() { return min.isNull; }
    
    // VEB node containing the summary node. 
    private vebNode* _summary; 
    // VEB cluster containing the child nodes.
    private vebNode[] _cluster;
    
    
    @disable this(); // initializing without providing a universe size is prohibited. 
    this(size_t universeSize) // ditto
    {
        this._universeSize = universeSize; 
        initializeChildren(universeSize); 
    }
    
    // after constructing the node, construct every of its children. 
    private void initializeChildren(size_t universeSize)
    {
        if(universeSize > BASE_SIZE)
        {
            import std.algorithm; 
            import std.range; 
            auto childUniverseSize = higherSquareRoot(universeSize); 
            _summary = new vebNode(childUniverseSize); 
            _cluster = iota(0,childUniverseSize).map!(a => vebNode(lowerSquareRoot(universeSize))).array; 
        }
    }
    
    // this function inserts a value into an empty node. The difference between empty and non empty insert is, that the
    // algorithm doesn't look into deepness of the tree, it just inserts the node to the separately stored min and max
    // members. 
    private void emptyInsert(uint x)
    {
        min = x; 
        max = x; 
    }
    
    // this function inserts a value into a generic node. If the member exists, no insertion will be done. 
    void insert(uint x)
    {        
        if(this.empty)
            emptyInsert(x); 
        else 
        {
            if(x < min)
            {//import std.algorithm; swap(min.get, x); 
                auto temp = x; x = min; min = temp; 
            }
            
            if(universeSize > BASE_SIZE)
            {
                if(_cluster[high(x)].min.isNull)
                {
                    _summary.insert(high(x)); 
                    _cluster[high(x)].emptyInsert(low(x)); 
                }
                else
                    _cluster[high(x)].insert(low(x)); 
            }
            if(x > max)
                max = x; 
        }
    }
    
    // this function removes a value from the tree. If the value doesn't exist in the tree nothing will be happen. 
    void remove(uint x)
    {  
        // case: there is only single element
        if(min == max)
        {
            _min.nullify; 
            _max.nullify; 
        }
        else if(BASE_SIZE == universeSize)
        {
            min = (x == 0) ? 1 : 0; 
            max = min; 
        }
        else 
        {
            if(x == min)
            {
                auto firstcluster = _summary.min; 
                x = index(firstcluster, _cluster[firstcluster].min); 
                min = x; 
            }
            _cluster[high(x)].remove(low(x)); 
            if(_cluster[high(x)].min.isNull)
            {
                _summary.remove(high(x)); 
                if(x == max)
                {
                    auto summarymax = _summary.max;
                    if(summarymax.isNull)
                        max = min; 
                    else
                        max = index(summarymax, _cluster[summarymax].max); 
                }
            }
            else if(x == max)
                max = index(high(x), _cluster[high(x)].max); 
        }
    }
    
    // this function returns the successor of the given value, even, if the value is not present in the tree. 
    // If the value is maximum or greater then the maximum of the tree null is returned. 
    Nullable!uint successor(uint x)
    {
        Nullable!uint result; 
        
        if(BASE_SIZE == universeSize)
        {
            if(x == 0 && max == 1)
                result = 1; 
        }
        else
        {
            if(!min.isNull && x < min)
                result = min; 
            else
            {
                if(!max.isNull && x < max)
                {
                    auto maxlow = _cluster[high(x)].max;
                    if(!maxlow.isNull && low(x) < maxlow)
                    {
                        auto offset = _cluster[high(x)].successor(low(x));
                        result = index(high(x), offset); 
                    }
                    else
                    {
                        auto succcluster = _summary.successor(high(x)); 
                        if(!succcluster.isNull)
                        {
                            auto offset = _cluster[succcluster].min; 
                            result = index(succcluster, offset); 
                        }
                    }
                }
            }
        }
        return result; 
    }
    
    // this function returns the predecessor of the given value, even, if the value is not present in the tree. 
    // if the value is the minimum or smaller then the minimum of the tree null is returned.
    Nullable!uint predecessor(uint x)
    {
        Nullable!uint result; 
        if(BASE_SIZE == universeSize)
        { 
            if(x == 1 && !min.isNull && min == 0)
                result = 0; 
        }
        else
        {
            if(!max.isNull && x > max)
                result = max; 
            else
            {
                auto minlow = _cluster[high(x)].min; 
                if(!minlow.isNull && low(x) > minlow)
                {
                    auto offset = _cluster[high(x)].predecessor(low(x)); 
                    result = index(high(x), offset); 
                }
                else
                {
                    auto predcluster = _summary.predecessor(high(x)); 
                    if(predcluster.isNull)
                    {
                        if(!min.isNull && x > min)
                            result = min; 
                    }
                    else
                    {
                        auto offset = _cluster[predcluster].max; 
                        result = index(predcluster, offset); 
                    }
                }
            }
        }
        return result; 
    }
    
    // This function returns whether the input key is currently member of the tree. 
    bool member(uint x)
    {
        bool returnVal;
       
        if(x < universeSize)
        {
            if(!min.isNull && (min == x || max == x))
                returnVal = true; 
            else 
            {
                if(BASE_SIZE != universeSize)
                    returnVal = _cluster[high(x)].member(low(x));
            }
        }
        return returnVal; 
    }
    
    // this function is an concretization of the module wide indexing function 
    uint index(uint x, uint y){ return .index(universeSize, x, y); }

    // this function is an concretization of the module wide indexing function     
    uint high(uint x){ return .high(x, universeSize); }

    // this function is an concretization of the module wide indexing function     
    uint low(uint x){ return .low(x, universeSize); }
}

/**
This class represents the VEB tree itself. For the sake of convinience it saves the provided at the initialization step
wished maximum element. However at the point of development it is only used for testing. Beyond this, it stores only
the reference to the root element, as the theory tells. 
*/
struct vebTree // : Iveb
{
    // the root element of the tree. 
    private vebNode root; 
    private uint _elementCount; 
    /// default constructor of a VEB tree is disabled. 
    @disable this(); 
    /// to construct a VEB tree one should provide the maximum element one wish to be able to store. 
    this(uint maximumElement)
    {
        root = vebNode(nextPowerOfTwo(maximumElement));
        
        version(unittest){ _maximumElement = maximumElement; }
    }
    
    /// another possibility is to construct a VEB tree by providing an array.
    this(uint[] range)
    {
        import std.exception; 
        // check, whether the range is not too long. 
        enforce(cast(uint)range.length == range.length);
        
        // first, we have to determine the size of the tree. 
        // it is either derived from the length of the given tree or its greatest element
        uint limit = cast(uint)range.length; 
        foreach(uint i; range) limit = i > limit ? i : limit;
        
        // initialize the root, with the found limit 
        root = vebNode(nextPowerOfTwo(limit));
        
        foreach(uint i; range) insert(i); 
    }
    
    /** 
        this method returns the capacity of the tree. It is equal to the next power of two with regard to the maximum
        element 
    */
    size_t capacity(){ return root.universeSize; }
    
    /// this method is used to add an element to the tree. duplicate values will be ignored. 
    void insert(uint x)
    { 
        if(x < capacity && !member(x))
        {
            root.insert(x); 
            _elementCount++; 
        }
    }
    
    /// this method overrides the insert method to directly use arrays
    void insert(uint[] arr){ foreach(uint i; arr) insert(i); }
    
    /// this method is used to remove elements from the tree. not existing values will be ignored. 
    void remove(uint x)
    { 
        if(member(x))
        {
            root.remove(x); 
            _elementCount--; 
        }
    }
    
    /// this method is used to determine, whether an element is currently present in the tree
    bool member(uint x){ return root.member(x); }
    
    /// this method is used to determine the minimum of the tree
    @property Nullable!uint min(){ return front; }

    /// this method is used to determine the maximum of the tree    
    @property Nullable!uint max(){ return back; }
    
    /// this method retrieves the successor of the given input.
    Nullable!uint successor(uint x){ return root.successor(x); }
    
    /// this method retrieves the predecessor of the given input. 
    Nullable!uint predecessor(uint x){ return root.predecessor(x); }
    
    // this method is used to determine, whether the tree is currently containing an element. 
    @property bool empty(){ return root.empty; }
    
    // this method returns the minimium. 
    @property Nullable!uint front(){ return root.min; }
    
    // this method removes the minimum element
    void popFront(){ if(!empty) remove(min); }
    
    // forward range also needs save. This is a draft version of the save function, it uses the opslice of the class to 
    // construct a new one via an array
    @property vebTree save(){ return vebTree(this[]); }
    
    /**
    opSlice operator to get the underlying array. 
    This is a draft version, as it uses the successor method of the class. So getting the underlying array is 
    proportional to n. As this functionaly is not seen as crucial, it is enough for the first time. 
    */
    uint[] opSlice()
    {
        uint[] retArray; 
        if(!min.isNull)
        {
            retArray ~= min;
            if(min != max)
            {
                retArray.reserve(capacity);
                while(retArray[$-1] != max)
                    retArray ~= successor(retArray[$-1]); 
            }
        }
        return retArray; 
    }
    
    /**
    opSlice operator to get the underlying array between given bounds. 
    This is a draft version, as it uses the successor method of the class. So getting the underlying array is 
    proportional to min(n, m), where n is the number of elements between bounds and m are the number of present 
    elements in the tree. 
    */
    uint[] opSlice(uint begin, uint end)
    {
        uint[] retArray; 
        if(begin < end && begin < max)
        {
            if(!min.isNull)
            {
                if(this.member(begin))
                    retArray ~= begin; 
                else
                {
                    uint i = successor(begin);
                    if(i < end)
                        retArray ~= i; 
                }
                if(min != max)
                {
                    import std.algorithm.comparison;
                    uint limit = min(end, this.max); 
                    
                    retArray.reserve(limit-begin); 
                    uint i = successor(retArray[$-1]); 
                    while(i < limit)
                    {
                        retArray ~= i; 
                        i = successor(retArray[$-1]); 
                    }
                }
            }
        }
        return retArray; 
    }
    
    /**
    This is a nontrivial opIndex operator on indizies of the tree. Given an index a range (!) is returned, which is, 
    either the range of elements in the tree build up by [predecessor(i) .. successor(i)] (i. e. excluding the 
    successor(i)), when the given index is not set. Or, if the given index is set, [member(i), successor(i)]. If an 
    index out of bounds is given, an empty array is returned. The tree must not be empty to use this function. 
    */
    uint[] opIndex(uint i)
    {
        import std.algorithm;
        import std.range;
        import std.exception; 
        enforce(!this.empty);

        uint[] retArr;         
        if(i < this.capacity)
        {
            uint absoluteMin; 
            uint absoluteMax; 
            
            if(i < this.min)
            {
                
                absoluteMin = 0; 
                absoluteMax = this.min; 
            }
            else
            {
                if(i >= this.max)
                {
                    absoluteMax = cast(uint)(capacity - 1); 
                    absoluteMin = this.max; 
                }
                else
                {
                    absoluteMax = successor(i); 
                    if(this.member(i))
                        absoluteMin = i; 
                    else
                        absoluteMin = predecessor(i); 
                }
            }
            retArr = iota(absoluteMin, absoluteMax).array;    
            if(i >= this.max)
                retArr ~= absoluteMax; 
        }
        return retArr; 
    }
    
    // TODO: implement some kind of cool output as a graphViz pic, similiar to the graphs in Cormen. 
    
    // bidirectional range also needs
    @property Nullable!uint back() { return root.max; }
    
    // this method removes the maximum element 
    void popBack() { if(!empty) remove(max); }
    
    /**
    This method returns the amount of elements currently present in the tree.
    This is a draft version, as it uses the slice operator of the class. So getting this number has a complexity
    proportional to n. As this functionaly is not seen as crucial, it is enough for the first time. 
    */
    @property size_t length(){ return _elementCount; }
    
    version(unittest)
    {
        // this member stores the provided input on initialization. This value could be used to hard prevent of adding
        // elements between this value and the capacity of the tree. 
        private uint _maximumElement; 
        @property size_t elementCount(){ return this[].length; }
        
        uint fill(uint m)
        {
            uint n; 
            for(uint i = 0; i < m; ++i)
            {
                uint x = uniform(0, _maximumElement+1, rndGenInUse);
                // the check for membership is done to add only on inserting to the counter, not just 
                // because visiting the the loop
                if(!member(x))
                {
                    insert(x); 
                    ++n; 
                }
            }
            return n; 
        }
        
        uint fill(ref uint[] arr, uint fillPercentage = 31)
        {
            uint n; 
            while(n != fillPercentage * capacity/32)
            {
                uint x = uniform(0, cast(uint)(capacity - 1), rndGenInUse);
                // the check for membership is done to add only on inserting to the counter, not just 
                // because visiting the the loop
                if(!member(x))
                {
                    insert(x); 
                    arr ~= x; 
                    ++n; 
                }
            
            }
            assert(n == fillPercentage*capacity/32); 
            return n; 
        }
    }
}

///
unittest
{
    assert(!__traits(compiles, new vebTree())); 
    vebTree vT = vebTree(1000); 
    assert(vT.capacity == 1024); 
    assert(vT.min.isNull); 
    
    vT.insert(2); 
    vT.insert(5); 
    assert(!vT.member(8)); 
    vT.insert(88);
    vT.insert(8); 
    assert(vT.predecessor(75) == 8); 
    assert(vT.successor(6) == 8); 
    assert(!vT.member(1029)); 
    vT.insert(1029); 
    assert(!vT.member(1029)); 


    assert(!vT.member(865)); 
    vT.insert(865); 
    assert(vT.member(865)); 
    vT.insert(865); 
    assert(vT.member(865)); 
    assert(!vT.member(866)); 
    vT.remove(866); 
    assert(vT.member(865)); 
    vT.remove(865); 
    assert(!vT.member(865)); 
}

///
unittest
{
    uint currentSeed = 83843; // unpredictableSeed();
    rndGenInUse.seed(currentSeed); //initialize the random generator
    uint M = uniform(0U,1 << 14, rndGenInUse); //set universe size to some integer. 
    //M = 30_000_000; 
    vebTree vT = vebTree(M); //create the tree
    assert(vT.capacity == nextPowerOfTwo(M)); 
    uint m = vT.fill(1000); //(try to) fill the tree with thousend values 
    uint n; 
    Nullable!uint i = vT.predecessor(vT.max)+1; 
    // discover the thousend (or little less) values with the predecessor method
    while(!i.isNull)
    {
        ++n; 
        i = vT.predecessor(i); 
    }
    // assert, that all members are discovered, iff when no predecessors are left
    assert(n == m); 
}

///
version(unittest)
{   
    ///
    vebTree fill(uint M)
    {
        vebTree vT = vebTree(M); 
        for(auto i = 0; i < 1000; i++)
        {
            uint x = uniform(0U, vT._maximumElement, rndGenInUse); 
            vT.insert(x); 
        }
        return vT; 
    }
}

///
unittest
{
    uint currentSeed = 433849; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    vebTree vT = fill(M); //fill the tree with some values 
    Nullable!uint i = vT.max; 
    
    // remove all members beginning from the maximum
    while(!i.isNull)
    {
        vT.remove(i); 
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
    uint currentSeed = 438749; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    vebTree vT = fill(M); //fill the tree with some values 
    Nullable!uint i = vT.min-1;
    
    // remove all members beginning from the minimum
    while(!i.isNull)
    {
        vT.remove(i); 
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
    vebTree vT = vebTree(M); 
    vT.insert(0x000f); 
    assert(vT.predecessor(0x000f).isNull);
    vT.insert(0x00f0);
    assert(vT.predecessor(0x00f0) == 0x000f); 
    vT.insert(0x0f00); 
    assert(vT.predecessor(0x0f00) == 0x00f0); 
    vT.insert(0xf000); 
    assert(vT.predecessor(0xf000) == 0x0f00);
    
    vT.remove(0xf000); 
    assert(vT.predecessor(0xf000) == 0x0f00);
    vT.remove(0x0f00); 
    assert(vT.predecessor(0x0f00) == 0x00f0); 
    vT.remove(0x00f0); 
    assert(vT.predecessor(0x00f0) == 0x000f); 
    vT.remove(0x000f); 
    assert(vT.predecessor(0x000f).isNull);
}

///
unittest
{
    uint M = 1 << 16; 
    vebTree vT = vebTree(M); 
    vT.insert(0xf000); 
    assert(vT.member(0xf000)); 
    vT.insert(0x0f00); 
    assert(vT.member(0x0f00)); 
    vT.insert(0x00f0);
    assert(vT.member(0x00f0)); 
    vT.insert(0x000f); 
    assert(vT.member(0x000f)); 
    
    vT.remove(0xf000); 
    assert(!vT.member(0xf000)); 
    vT.remove(0x0f00); 
    assert(!vT.member(0x0f00)); 
    vT.remove(0x00f0); 
    assert(!vT.member(0x00f0)); 
    vT.remove(0x000f); 
    assert(!vT.member(0x000f)); 
}

/// 
unittest
{
    //stress test
    uint currentSeed = 1948642567; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    uint M = uniform(0U, 1 << 14, rndGenInUse); // set universe size to some integer. 
    vebTree vT = vebTree(M); 
    uint[] arr; 
    auto howMuchFilled = vT.fill(arr); 
    assert(arr.length == howMuchFilled); 
    
    vebTree vT2 = vebTree(M); 
    assert(vT2.capacity == vT.capacity); 
    
    import std.datetime; import std.conv : to;
    import std.container;
    auto rbt = redBlackTree!uint(0); 
    rbt.clear; 
    
    void fill1()
    {
        foreach(uint i; arr)
        {
            vT2.insert(i); 
        }
    }
    
    void fill2()
    {
        foreach(uint i; arr)
        {
            rbt.insert(i); 
        }
    }
    
    /*
    import std.stdio; 
    writeln("howMuchFilled: ", howMuchFilled);
    auto r = benchmark!(fill1, fill2)(1); 
    auto f0Result = to!Duration(r[0]); 
    auto f1Result = to!Duration(r[1]); 
    writeln("VEB: ", f0Result); 
    writeln("rbt: ", f1Result); 
    assert(f0Result < f1Result); 
    */
}

///
unittest
{
    import std.algorithm; 
    uint currentSeed = 1230394; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer.
    uint[] sourceArr; 
    sourceArr.length = M; 
    // generate a random array as the source for the tree
    for(uint i = 0; i < M; i++) sourceArr[i] = uniform(0U, M, rndGenInUse); 
    
    // constructor to test
    vebTree vT = vebTree(sourceArr); 
    
    // make the array values unique. 
    auto uniqueArr = sort(sourceArr).uniq;
    // check, that all values are filled 
    foreach(uint i; uniqueArr)
    {
        assert(vT.member(i)); 
        vT.remove(i); 
    }
    // check, that no other elements are present. 
    assert(vT.empty); 
}

///
unittest
{
    uint currentSeed = 2349062; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    vebTree vT = vebTree(M); 
    uint[] arr; 
    vT.fill(arr, 16); 
    import std.algorithm;
    assert(setSymmetricDifference(vT[], sort(arr)).empty); 
}

///
unittest
{
    uint currentSeed = 2309532090; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    vebTree vT = vebTree(M); 
    uint[] arr; 
    vT.fill(arr, 16); 
    
    uint begin = 5; 
    uint end = 100; 
    
    import std.algorithm; 
    auto filterRes = sort(arr).filter!(a => a >= begin && a < end); 
    assert(setSymmetricDifference(filterRes, vT[begin..end]).empty); 
}

///
unittest
{
    uint currentSeed = 1223409; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    vebTree vT = vebTree(M); 
    uint[] arr; 
    vT.fill(arr, 16); 
    assert(vT.length == vT.elementCount); 
}

///
unittest
{
    uint currentSeed = 1435856534; //unpredictableSeed(); 
    rndGenInUse.seed(currentSeed); //initialize the random generator
    // do not use more then "1 << 15", as for the red-black tree the insertion duration is almost 4 (!) minutes. 
    uint M = uniform(0U, 1 << 16, rndGenInUse); // set universe size to some integer. 
    vebTree vT = vebTree(M); 
    uint[] arr; 
    vT.fill(arr, 16); 
    
    assert(!vT.member(0));
    assert(!vT.member(1)); 
    import std.algorithm; 
    assert(startsWith(vT[1], 0)); 
    assert(vT.successor(vT[1][$-1]) == vT.successor(1));
    assert(startsWith(vT[vT.successor(1)],vT.min)); 
    assert(!vT.member(65535)); 
    assert(vT[65535] == [65534, 65535]); 
    assert(vT.member(4)); 
    assert(startsWith(vT[4],4)); 
    assert(!vT.member(vT[4][$-1])); 
    assert(!vT.member(5)); 
    assert(startsWith(vT[5],4)); 
    assert(vT[5][$-1] == vT[4][$-1]);
}

unittest
{
    import std.range;
    assert(isBidirectionalRange!vebTree);
}