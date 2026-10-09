/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalAnabelian`: the local input of Neukirch–Uchida

This is the umbrella module of the `Submission/Work/LocalAnabelian/` subproject.  It
provides the local input of the Neukirch–Uchida theorem (CoNF XII (12.1.9) "if"
direction and (12.1.10)): the recovery of the residue characteristic, the residue
field cardinality and the absolute degree of a `p`-adic field `κ` from its absolute
Galois group `Gal(κ̄/κ)`.

## What is here

* **`Basic`** — the group-theoretic vocabulary.  `numIndexSubgroups p G` (the number
  of index-`p` subgroups, i.e. the rank of the maximal elementary abelian
  `p`-quotient), `HasFrattiniRank p r G`, `HasAbelianFrattiniRank p r G`, the `ℓ`-tower
  rank predicate `HasUnboundedTowerRank ℓ G`, and the residue-characteristic detector
  `ResidueCharDetectedBy p G`, together with their invariance under group
  isomorphisms and the uniqueness of the rank (`eq_of_hasFrattiniRank`).

* **(A) the Kummer bridge** (`Kummer/`, `Counting/`, `GaloisCorrespondence/`) —
  for a field `k` containing a primitive `p`-th root of unity,

    `natCard_galois_finrank_eq_p`:
    `#{L : k ⊆ L ⊆ K', L/k Galois of degree p} = (|kˣ/(kˣ)^p| - 1)/(p - 1)`,

  with `numIndexSubgroups_eq_natCard_finrank_eq` (closed index-`p` subgroups are
  degree-`p` subextensions), the canonical Kummer correspondence
  `kummerCorrespondence` (degree-`p` Galois extensions ↔ subgroups of
  `kˣ/(kˣ)^p` of order `p`, equivalently — after `natCard_indexP_subgroups_of_exp_p`
  — indexed by the hyperplanes), and, in `PadicField/FrattiniRank`,

    `hasAbelianFrattiniRank_of_inputs`:
    `HasAbelianFrattiniRank p (d + 1 + δ) (Gal(κ̄/κ))`,

  which says that the abelianised pro-`p` part of `Gal(κ̄/κ)` is `ℤ_p^d × (ℤ/p)^δ`
  (equivalently `frattiniRank p (Gal(κ^{(p)}/κ)) = 1 + [κ:ℚ_p] + δ`), plus
  `hasAbelianFrattiniRank_of_isPrimitiveRoot`, the `ζ_p ∈ κ` case derived from the Kummer
  bridge and the power class count `|κˣ/(κˣ)^p| = p^{d+2}`, the conditional non-abelian
  statement `hasFrattiniRank_of_isPrimitiveRoot`, and — via
  `Bridge.frattiniRank_eq_of_hasAbelianFrattiniRank` — the same result in the vocabulary of
  the sibling project `Submission/Work/ProfiniteP/`:

    `frattiniRank_galois_of_inputs`:
    `NK.ProfiniteP.frattiniRank p (Gal(κ̄/κ)) = 1 + d + δ`.

  *Why the abelianisation*: index-`p` subgroups of the maximal pro-`p` quotient are the
  *normal* index-`p` subgroups of `Gal(κ̄/κ)`, i.e. the index-`p` subgroups of its
  abelianisation, and there are `(p^{d+1+δ}-1)/(p-1)` of them — the number of *cyclic*
  degree-`p` extensions.  The count of **all** degree-`p` extensions differs when
  `δ = 0` (e.g. the Eisenstein cubic `ℚ_3(∛3)` is degree `3` and not Galois), so no
  "all degree-`p` extensions are Galois" input is available there.

* **(B) the residue characteristic** (`ResidueChar/`) — `ResidueCharInput p κ K'`,
  the Ivanov input that `p` is the unique prime of unbounded tower rank, and
  `residueCharDetectedBy_unique`/`residueChar_eq_of_mulEquiv`: the residue
  characteristic is an invariant of the abstract group `Gal(κ̄/κ)`.

* **(C) the residue field cardinality** (`ResidueField/`) — the inertia subgroup
  `inertiaSubgroup`, identified with the fixing subgroup of `κ^ur = κ(μ_{p'})`
  (`unramifiedClosure`, `inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure`), the
  Frobenius normalisation `ActsAsFrobenius p q σ`, and
  `eq_of_actsAsFrobenius`/`eq_of_isFrobeniusFor_of_mem_inertia`: the Frobenius coset
  modulo inertia determines `q`.  `ResidueField/Recovery` adds the `IsFrobeniusFor`
  predicate and the uniqueness modulo inertia.

* **(D) the assembly** (`Assembly`) — `residueChar_eq_of_padicGaloisInputs`,
  `degree_eq_of_padicGaloisInputs` and
  `residueChar_and_degree_eq_of_padicGaloisInputs`: an isomorphism of absolute Galois
  groups of `p`-adic fields preserves both the residue characteristic and
  `[κ : ℚ_p]`.

## What is assumed (the honest hypotheses)

The results are unconditional except for the explicitly named local inputs, collected
in the structure `PadicGaloisInputs p d δ κ K'`:

* `powerQuotient_card`: `|κˣ/(κˣ)^p| = p^{d+1+δ}` — the structure theory of `κˣ`
  (`κˣ ≅ ℤ × μ_κ × U¹`, `U¹ ≅ ℤ_p^d`); **for `κ = ℚ_p` this is
  `Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`**,
  restated in this vocabulary as `natCard_KummerGroup_rat_adic`;
* `abelian_rank`: `HasAbelianFrattiniRank p (d+1+δ) (Gal(κ̄/κ))` — local reciprocity, i.e.
  `Gal(κ̄/κ)^{ab,(p)} = ℤ_p^d × (ℤ/p)^δ`.  For `δ = 1` this *follows* from the power class
  count by the Kummer bridge (`hasAbelianFrattiniRank_of_isPrimitiveRoot`), given that the
  abelian index-`p` count agrees with the Galois-extension count
  (`numIndexSubgroups_abelianization_eq_natCard_galois`); for `δ = 0` it is a genuine input;
* `p_torsion_iff`: `δ = 1 ⟺ Gal(κ̄/κ)^{ab}` has non-trivial `p`-torsion — this is `μ_κ[p]`,
  non-trivial exactly when `ζ_p ∈ κ`;
* `residueChar_detected`: Ivanov's Lemma 3.12 (anti-anabelianity of local fields);
* (`degreeP_isGalois` and `indexP_isClosed` appear only as *explicit hypotheses* of the
  conditional non-abelian statement `hasFrattiniRank_of_isPrimitiveRoot`.)

Similarly, in (C) the existence of a Frobenius element with the `q`-power action is the
classical theory of the unramified extension `κ^ur = κ(μ_{p'})` with
`Gal(κ^ur/κ) ≅ Ẑ`.
-/
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.LocalAnabelian.Counting.natCard_eq_mul_card_of_fiber_natCard
import Submission.NK.LocalAnabelian.Counting.natCard_subtype_ne_one
import Submission.NK.LocalAnabelian.Counting.natCard_indexP_subgroups_of_exp_p
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.NK.LocalAnabelian.Kummer.Quot
import Submission.NK.LocalAnabelian.Kummer.QuotAPI
import Submission.NK.LocalAnabelian.Kummer.Bridge
import Submission.NK.LocalAnabelian.Kummer.kummerCorrespondence
import Submission.NK.LocalAnabelian.KummerAux.kummerField_zpow_eq_of_not_dvd
import Submission.NK.LocalAnabelian.GaloisCorrespondence.numIndexClosedSubgroups_eq_natCard_finrank_eq
import Submission.NK.LocalAnabelian.GaloisCorrespondence.IndexP
import Submission.NK.LocalAnabelian.GaloisCorrespondence.numIndexSubgroups_abelianization_eq_natCard_galois
import Submission.NK.LocalAnabelian.PadicField.Defs
import Submission.NK.LocalAnabelian.Bridge.frattiniRank_eq_of_hasAbelianFrattiniRank
import Submission.NK.LocalAnabelian.PadicField.FrattiniRank
import Submission.NK.LocalAnabelian.PadicField.RatAdic
import Submission.NK.LocalAnabelian.ResidueChar.Defs
import Submission.NK.LocalAnabelian.ResidueField.Defs
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.Recovery
import Submission.NK.LocalAnabelian.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
