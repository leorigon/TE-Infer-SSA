This is prototype for project master's degree in computer application on UDESC.
 
Abstract:
```
One of the main functions of a type system is to assist at construction of programs with a lower 
incidence of errors. For example, the type system used in the Haskell language guarantees the absence of 
type errors during program execution, which, together with the absence of side effects, 
makes it possible to create programs that are more likely to be correct. However the 
manipulation of data that implicitly causes some side effect is not very intuitive for 
the programmer accustomed to working with imperative languages. The functional programming 
language Koka defines a syntax closer to imperative programming languages, as well as 
allowing the verification of the types of functions, the language also allows 
the inference of side effects, guaranteeing more security to the programs written in the same. 
SSA (Static Single Assigment) is an intermediate representation of code, generally 
used to aid the optimization process. This representation is easily translated into a functional 
representation. The objective of this project is to define the core of an imperative language and 
the construction of a compiler that guarantees some properties of types and effects of the 
implemented codes. For this, it is proposed to translate the source code of this language 
into the functional representation of SSA through control flow graphs. It will as well defined 
an algorithm capable of inferring types and side effects of this representation.
```
requirements: 
  - stack
  - some text editor
  - graphviz to show the CFG in visual mode (.dot files) 
  
to run:
  - edit `test.lc` file
  - on terminal: `stack build and stack exec lambdaC`
  
