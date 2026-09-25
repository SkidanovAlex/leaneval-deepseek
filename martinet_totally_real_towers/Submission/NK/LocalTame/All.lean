/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalTame`: the tame layer of the local Galois group and the Frobenius correspondence

This is the umbrella module of the `Submission/Work/LocalTame/` subproject: the local input of
the Neukirch–Uchida endgame that matches *Frobenius elements at corresponding places*.

## What is here

* **`Basic`** (`NK.LocalTame.Basic`) — the abstract group theory: the predicates `IsProP`,
  `IsProPrimeToP`, `IsProCyclic` (pro-`p`, pro-prime-to-`p`, pro-cyclic in the finite-quotient
  formulation), the wild-inertia predicate `IsWildInertia`, the tame-inertia characterisation
  `IsMaxNormalProCyclicInQuotient`, the Frobenius-lift predicate `IsTameFrobeniusLift` and the
  `ℤ_ℓ²`-quotient detector `HasZl2Quotient`, together with the invariance of each under group
  isomorphisms.  (No topology: finite index subgroups of profinite groups are open.)
* **`Basic/…`** — supporting group theory delegated to colleagues: the join of two (resp. of any
  family of) normal pro-`p` subgroups is pro-`p`, and the coset structure of `IsTameFrobeniusLift`
  modulo the inertia subgroup.
* **`Galois`** (`NK.LocalTame.Galois`) — the instantiation at `Gal(K'/κ)`: the wild inertia
  `wildInertiaSubgroup p` (the join of all normal pro-`p` subgroups), the tame quotient
  `tameQuotient p = G_κ^{tr}`, the tame inertia `tameInertiaSubgroup p` and the abelianised tame
  quotient `tameAbelianization p` with its torsion `tameTorsion p`.
* **`WildInertiaProP`** — `wildInertiaSubgroup p` is pro-`p`, hence *the* maximal closed normal
  pro-`p` subgroup of `G_κ` (NSW (7.5.7) Corollary), with no arithmetic input.
* **`Inputs`** (`NK.LocalTame.Inputs`) — the named classical inputs: `TameStructureInput` (the
  structure of the tame quotient, NSW (7.5.7) and (7.5.11), Iwasawa), `ResidueCardRecovery` (the
  residue field order from the torsion of the abelianised tame quotient, Shimizu Lemma 2.1),
  `FrobeniusLiftCharacterisation` (Frobenius lifts are detected by their action on the tame
  inertia, NSW (12.1.8), Iwasawa) and `Zl2ResidueChar` (the residue characteristic is the unique
  prime `ℓ` with a `ℤ_ℓ²`-quotient, Shimizu Lemma 2.1), bundled as `TameData`.
* **`Transfer/…`** — transfer of the tame-inertia characterisation and of torsion cardinalities
  along group isomorphisms.
* **`Main`** (`NK.LocalTame.Main`) — the main theorem: an isomorphism `Gal(K'/κ) ≃* Gal(L'/κ₂)`
  of absolute Galois groups of `p`-adic fields maps the wild inertia onto the wild inertia, the
  inertia onto the inertia, forces the residue characteristics and the residue field cardinalities
  to agree, and maps the Frobenius lifts onto the Frobenius lifts
  (`NK.LocalTame.isFrobeniusFor_map_iff`).
* **`Corollaries`** (`NK.LocalTame.Corollaries`) — the local correspondence summarised: for an
  isomorphism of absolute Galois groups of `p`-adic fields, the residue characteristics, residue
  field cardinalities, `ζ_p`-indicators and absolute degrees coincide, and the Frobenius lifts
  correspond (`NK.LocalTame.local_correspondence`).
* **`Global`** (`NK.LocalTame.Global`) — the global corollary for number fields: at places `A`,
  `B` with `Φ(D_A) = D_B`, the Frobenius elements of `D_A` are matched with those of `D_B`
  (`NK.LocalTame.frobenius_matching_at_corresponding_places`).
-/
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalTame.Basic.isTameFrobeniusLift_mul_mem_inertia
import Submission.NK.LocalTame.Basic.isTameFrobeniusLift_of_mul_mem_inertia
import Submission.NK.LocalTame.ProP.isProP_sup_of_normal
import Submission.NK.LocalTame.ProP.isProP_iSup_of_normal
import Submission.NK.LocalTame.Galois
import Submission.NK.LocalTame.Galois.wildInertiaSubgroup_isProP
import Submission.NK.LocalTame.WildInertiaProP
import Submission.NK.LocalTame.Inputs
import Submission.NK.LocalTame.Transfer.IsMaxNormalProCyclicInQuotient_map
import Submission.NK.LocalTame.Transfer.natCard_torsion_mulEquiv
import Submission.NK.LocalTame.Main
import Submission.NK.LocalTame.Corollaries
import Submission.NK.LocalTame.Global
import Submission.NK.LocalTame.Global.inertia_matching_at_corresponding_places
