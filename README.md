# README #

This repository contains a Van Emde Boas tree written in D. It operates on unique integer keys. 

See

https://en.wikipedia.org/wiki/Van_Emde_Boas_tree

and 

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein. Introduction to Algorithms, Third Edition. MIT Press, 2009. ISBN 978-0-262-53305-8. Chapter 20: The van Emde Boas tree, pp. 531–560.

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

License: https://opensource.org/licenses/MIT, MIT License

Author: Alexander Orlov, sascha.orlov@gmail.com