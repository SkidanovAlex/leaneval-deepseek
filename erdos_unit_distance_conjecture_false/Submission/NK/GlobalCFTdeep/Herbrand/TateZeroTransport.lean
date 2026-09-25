/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_helpers

/-!
# Tools for transporting degree-zero Tate cohomology

Wrapper module re-exporting the two ingredients used to compare the degree-zero Tate cohomology
`Ĥ⁰` of two representations:

* `Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso`, identifying `Ĥ⁰(G, M)`
  with the quotient `Mᴳ ⧸ N(M)` of the invariants by the norm;
* `NK.GlobalCFTdeep.natCard_tateCohomology_zero_of_mulEquiv_res`, the invariance of
  `Nat.card Ĥ⁰` under restricting a representation along a group isomorphism.
-/
