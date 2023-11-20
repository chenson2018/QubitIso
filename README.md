# Overview

This repository constructs a proof of the group homomorphism between SU(2) and SO(3), with minimal dependencies. The proof is mostly mechanical, showing the isomorphism between SU(2) and unit quaternions (versors), then explicitly constructing the homomorphism from the versors to SO(3).

# Presentation

The repo includes a [presentation](presentation/presentation.pdf) prepared for a seminar course on quantum computing at Drexel University (led by professors Ali Shokoufandeh and Ali Shokoufandeh).

# Dependencies 

This repo relies on [QuantumLib](https://github.com/inQWIRE/QuantumLib) for the definitions of complex numbers and matrices.

Tested using Coq version 8.15.0

# Files

- [Group.v](Group.v) - Typeclass definitions for groups, group homomorphism, and group isomorphism. The most interesting part of this is that these typeclasses take an equivalence relation as an argument, which does not need to be the same for all groups.
- [Quaternion.v](Quaternion.v) - Definition of the quaternions as pairs of real numbers and the subset type of versors. Versors are shown to be a group.
- [SU2.v](SU2.v) - Definition of the group SU(2), with elements being represented using subset types on the Matrices provided by QuantumLib
- [SO3.v](SO3.v) - Definition of the group SO(3), with elements being represented using subset types on the Matrices provided by QuantumLib
- [SU2_Iso_Versor.v](SU2_Iso_Versor.v) - proof of the isomorpism between SU(2) and the unit quaternions
- [Versor_Homo_SO3.v](Versor_Homo_SO3.v) - proof of the homomorphism between the unit quaternions and SO(3)
- [SU2_Homo_SO3.v](SU2_Homo_SO3.v) - final proof of the homomorphism between SU(2) and SO(3)
- [MatrixAux.v](MatrixAux.v) - Some additional lemmas for matrices, the majority of which are adapted directly from [Verified Quantum Computing](https://rand.cs.uchicago.edu/vqc/index.html)
- [Inverses.v](Inverses.v) - This file is not used. It proves, over general equivalence relations, that left and right inverses imply injection and surjection respectively.
