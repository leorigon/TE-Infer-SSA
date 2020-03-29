This is prototype for project master's degree in computer application on UDESC.
 
Abstract:
```
The static single assignment form which is used by compilers of imperative programming languages is, as noted by Kelsey, 
a functional language. Local mutability is removed by renaming variables, and control flow is split into basic blocks, which are, in turn, a set of mutually recursive lambda abstractions. This suggests that such constructs could be used as the foundation for a functional language.

In this paper, we present the core of a purely functional programming language with an 
imperative look-and-feel and with a type and effect system based on that of Leijen's Koka. 
We also discuss our initial results with a prototype implementation and a type and effect inference algorithm.
```
requirements: 
  - stack
  - some text editor
  - graphviz to show the CFG in visual mode (.dot files) 
  
to run:
  - edit `test.lc` file
  - on terminal: `stack build and stack exec lambdaC`
  
