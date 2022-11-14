Hefty Algebras -- The Artifact
==============================

This is the artifact accompanying the POPL 2023 paper [Hefty Algebras: Modular Elaboration for Higher-Order Algebraic Effects](http://casperbp.net/store/hefty-algebras.pdf).

The entry point for the artifact is the file `src/index.agda`.


### Building

To build the artifact, you need the following:

- A checkout of the Agda Standard Library in the `lib/agda-stdlib` folder.
- A working installation of Agda version 2.6.2.1 or higher

Assuming you have Agda installed, you can generate browsable HTML for the artifact by running the following in the root folder of this artifact:

```
$ git submodule init
$ git submodule update
$ agda src/index.agda --html
```

Or as a one-liner:

```
$ git submodule init && git submodule update && agda src/index.agda --html
```

### Extra Material

The `haskell` folder of the artifact contains a Haskell port of the framework described in the paper.
