# README #

This repository contains a simplified Van Emde Boas tree written in D. Its operate on (currently) only unique integer keys. 

Example usage: 

```
import vebtree; 

assert(!__traits(compiles, new vebTree())); 
vebTree vT = new vebTree(1000); 
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
```

Copyright: Copyright (c) 2016- Alexander Orlov. All rights reserved.

License: http://boost.org/LICENSE_1_0.txt, Boost License 1.0.

Authors: Alexander Orlov, sascha.orlov@gmail.com