# Delooping generated groups in homotopy type theory

This repository presents the developments accompanying the paper _Delooping
generated groups in homotopy type theory_ by Camil Champin, Samuel Mimram and
Emile Oleon. They have been tested with
[Agda](https://wiki.portal.chalmers.se/agda/) 2.6.3 with the [cubical Agda
libraray](https://github.com/agda/cubical) version 0.5.

You can [browse the code
online](https://smimram.github.io/generated-deloopings-agda/).

## Delooping with presented Eilenberg-MacLane spaces

- [`EM`](EM.agda)
  - Definition of Eilenberg-MacLane spaces associated to a presentation
  - Equivalence with the traditional definition

## Delooping with (generated) G-sets

- `GSet`
  - Definition of Actions
  - Definition of GSets and the GSet Structure
- `GSetHom`
  - Definition of GSet Homomorphisms
  - Definition of GSetEquiv : GSet Isomorphisms
- `GSetProperties`
  - Equality types for Actions and GSetHoms
  - Properties of GSetEquivs
  - Isomorphisms and paths are equivalent (through fundamental theorem of identity types)
  - Gsets form a groupoid
- `XSet`
  - Definition of Set Actions
  - Definition of XSets and the XSet Structure
- `XSetProperties`
  - The forgetful functor U from GSets to XSets when X is a subset of G
  - Proof that the the loop space of the principal torsor is invariant by U.
- `Comp`
  - Definition of Comp the connected component of a pointed space (A, a0
  - Definition of the fundamental group π₁ for groupoids
  - The Comp of a groupoid is a groupoid
  - π₁(Comp(A, a0)) = π₁(A,a0)
- `Generators`
  - Definition of Group generation
- `PrincipalTorsor`
  - Definition of the principal torsor of a group
- `Deloopings`
  - Delooping by torsors (classical construction and proof)
  - Delooping by generated torsors
  - Caracterisation of the Principal torsor's Aut group
