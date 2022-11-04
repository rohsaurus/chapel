# Inspector-executor Examples

This directory contains various benchmarks/apps to test and evaluate the inspector-executor (IE) optimization.
Each benchmark has its own directory and accompanying README, which will detail current status in terms of
usage, implementation and IE performance.

## common

This directory contains module files for common data structures and routines used in the different example applications.
** The versions of the files in this directory are stale. We moved them into the internals directory so that they can
be used without use-statements (makes it easier for the compiler during the optimizations). I'll eventually remove
this directory. **

## NAS-CG

NAS Parallel Benchmark implementation on Conjugate Gradient (CG). It runs across multiple locales and uses an
adjacency list-like data structure for the sparse matrix. The target of the IE optimization is the sparse matrix-vector
multiply (SpMV), which is performed many times as part of the CG iterations.

## PageRank

Fairly straight forward implementation of the PageRank algorithm. It runs across multiple locales and operates on
a read-in graph. There is a separate program to convert graphs from MatrixMarket format to a binary representation
that is used in the PageRank application. For the IE optimization, the target is the main kernel that essentially
accesses each vertex's neighbors. This kernel is repeated multiple times until the algorithm converges.
