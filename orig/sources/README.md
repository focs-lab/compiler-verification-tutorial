# EUTYPES 2019 summer school

This is the Coq source companion for Xavier Leroy's lectures on compiler verification at the EUTYPE 2019 Summer School on Types for Programming and Verification, 30 August- 4 September, 2019, Ohrid, Macedonia,
https://sites.google.com/view/2019eutypesschool/

## Files

- IMP.v: abstract syntax and semantics of a small imperative language
- Compil.v: compiling IMP to a stack-based abstract machine
- Constprop.v: constant propagation, an optimization based on a forward dataflow analysis
- Deadcode.v: dead code elimination, an optimization based on liveness analysis (a backward dataflow analysis)
- Fixpoints.v: fixed points and how to compute them effectively
- Sequences.v: a library to work with sequences of transitions in operational semantics

## Building the sources

```
    make -f CoqMakefile
```

## Licensing

These files are copyright 2019,2025 Xavier Leroy <xavier.leroy@college-de-france.fr> and distributed under the terms of the GNU Lesser General Public License as published by the Free Software Foundation; either version 2.1 of the License, or (at your option) any later version.  A copy of the license is included in file LICENSE.md.
