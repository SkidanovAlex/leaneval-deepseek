/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `p = 2` route: `NK.Indecomposed.RankDataTrivial 2` from the twisted catalogue

At `p = 2` the cyclotomic coefficient module is the trivial module: `μ_2 = {±1}` is fixed by every
automorphism in characteristic `≠ 2` (on disk: `NK.BrauerTwist.muRep_isTrivial_of_isPrimitiveRoot`
and `NK.BrauerTwist.muLevel_eq_top_of_isPrimitiveRoot`).  Consequently the twisted cohomology
`NK.BrauerTwist.H2Twist 2` and the trivial-coefficient cohomology
`NK.BrauerHasse.H2Profinite 2` of a subgroup compute the same thing, and the `p = 2` route of the
development (`NK.Indecomposed.indecomposedPrime_two_of_rankData`) can be fed from the catalogue of
this chapter.

This module provides

* `NK.IndecomposedDeep.TwistTwoComparison` — **the comparison of the two cohomology theories at
  `p = 2`**, as a named statement: an equivalence of `H2Twist 2 U` with `H2Profinite 2 U` for every
  subgroup `U`, natural for the restriction maps and transferring non-vanishing of a local component.
  It is the "`μ_2`-twist is trivial" statement, and it is the only missing piece of the `p = 2`
  route; see `README.md` §13 for exactly what its proof consists of;
* `NK.IndecomposedDeep.rankDataTrivial_two_of_comparison` — **proved**: the comparison together with
  the twisted catalogue `DeepInputs 2` produces `NK.Indecomposed.RankDataTrivial 2 K K' κ κ'`;
* `NK.IndecomposedDeep.indecomposedPrime_two_of_comparison` — **proved**: the end-to-end `p = 2`
  consumer: the comparison, the twisted catalogue and the local reconstruction at `p = 2` produce
  `NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ'` (via the on-disk
  `NK.Indecomposed.indecomposedPrime_two_of_rankData`).
-/

import Submission.NK.IndecomposedDeep.Endgame

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The comparison of the twisted and trivial coefficient theories at `p = 2`.**

At `p = 2` the cyclotomic coefficient module `μ_2 = {±1}` is the trivial `ℤ/2`-module (in
characteristic `≠ 2`), so the twisted cohomology `NK.BrauerTwist.H2Twist 2 U` and the
trivial-coefficient cohomology `NK.BrauerHasse.H2Profinite 2 U` are equivalent as the subgroup `U`
varies, and the equivalence is natural for the restriction maps and for the localisation at a place.

Concretely the fields are

* `equiv` — the levelwise identification of the two level systems, collated over the finite Galois
  levels: at every level `L` the coefficient modules `μ_2(L) = {±1}` and `ℤ/2` are canonically
  isomorphic and carry the trivial action, and the cochain complexes of the two group cohomologies
  have the same underlying types and the same differentials (Mathlib's `groupCohomology` is the
  cohomology of the inhomogeneous cochain complex, whose differential uses only the group action,
  the addition, and the integer scalars `(-1)^i`);
* `equiv_res` — naturality in the restriction maps `H2Twist.res` / `H2Profinite.res`;
* `equiv_loc` — the transfer of a *non-vanishing local component* at a place.

See `README.md` §13: the mathematical content is the classical triviality of the `p = 2` twist; the
formalisation gap is the change of scalar ring between the two coefficient rings
`NK.BrauerTwist.CoeffInt = ULift ℤ` and `NK.BrauerHasse.Coeff p = ULift (ZMod p)` under which
Mathlib's `groupCohomology` is defined, together with the collation over the two level systems. -/
structure TwistTwoComparison (K K' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] where
  /-- the comparison of the two cohomology theories at every subgroup -/
  equiv : ∀ (U : Subgroup Gal(K'/K)),
    H2Twist (K := K) (K' := K') 2 U ≃ NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 U
  /-- naturality of the comparison in the restriction maps -/
  equiv_res : ∀ {U V : Subgroup Gal(K'/K)} (h : V ≤ U) (x : H2Twist (K := K) (K' := K') 2 U),
    equiv V (NK.HasseTwist.H2Twist.res (K := K) (K' := K') 2 h x)
      = NK.LocalDecomposition.H2Profinite.res (K := K) (K' := K') 2 h (equiv U x)
  /-- the comparison transfers a non-vanishing local component -/
  equiv_loc : ∀ (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K')
      (x : H2Twist (K := K) (K' := K') 2 U),
    NK.BrauerHasse.H2Profinite.loc (K := K) (K' := K') 2 U (equiv U x) A ≠ 0 →
      H2Twist.loc (K := K) (K' := K') 2 U x A ≠ 0

/-- **`NK.Indecomposed.RankDataTrivial 2` from the twisted catalogue and the comparison.**

* `card_global` and `card_local` are transported along the comparison from the corresponding fields
  of `NK.Indecomposed.RankData 2` (which `rankData_of_deepInputs` supplies);
* `surj` is transported as well: the localisation at a place `is` the restriction to the local group
  (`NK.LocalDecomposition.loc_eq_res` for the trivial coefficients), and the comparison is natural
  for the restrictions, so the twisted surjectivity of Neukirch's rank count gives the trivial one. -/
theorem rankDataTrivial_two_of_comparison (h : DeepInputs 2 K K' κ κ')
    (hc : TwistTwoComparison K K') :
    NK.Indecomposed.RankDataTrivial 2 K K' κ κ' where
  hp := Nat.prime_two
  card_global := fun U hU hκ => by
    have h1 : Nat.card (H2Twist (K := K) (K' := K') 2 U) = 2 :=
      (rankData_of_deepInputs h).card_global U hU hκ
    rw [← Nat.card_congr (hc.equiv U), h1]
  card_local := fun H hHcl hκ 𝔭 V hV hne => by
    have h1 : 2 ≤ Nat.card (H2Twist (K := K) (K' := K') 2 V) :=
      (rankData_of_deepInputs h).card_local H hHcl hκ 𝔭 V hV hne
    rw [← Nat.card_congr (hc.equiv V)]
    exact h1
  surj := fun H _hHcl _hκ 𝔭 hguard => by
    obtain ⟨A, x, hx⟩ := hguard
    have hguard' : ∃ (A' : NK.HasseTwist.PlacesOverPrime K K' 𝔭)
        (y : H2Twist (K := K) (K' := K') 2 H),
        H2Twist.loc (K := K) (K' := K') 2 H y A'.toOverFinitePrime ≠ 0 :=
      ⟨A, (hc.equiv H).symm x,
        hc.equiv_loc H A.toOverFinitePrime ((hc.equiv H).symm x) (by
          have hcancel : (hc.equiv H) ((hc.equiv H).symm x) = x :=
            Equiv.apply_symm_apply (hc.equiv H) x
          rw [hcancel]
          exact hx)⟩
    have hsurj := (rankData_of_deepInputs h).surj H _hHcl _hκ 𝔭 hguard'
    intro z
    obtain ⟨y, hy⟩ := hsurj (fun V => (hc.equiv V.1).symm (z V))
    have hy' : ∀ V : ↥(NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭),
        NK.HasseTwist.H2Twist.res (K := K) (K' := K') 2
          (NK.HasseTwist.le_of_mem_localGroupSubgroupsOver (K := K) (K' := K') V.2) y
          = (hc.equiv V.1).symm (z V) := fun V => congrFun hy V
    refine ⟨hc.equiv H y, ?_⟩
    funext V
    simp only [NK.Indecomposed.localisationToTrivial]
    rw [← hc.equiv_res (NK.HasseTwist.le_of_mem_localGroupSubgroupsOver (K := K) (K' := K') V.2) y,
      hy' V]
    exact Equiv.apply_symm_apply (hc.equiv V.1) (z V)

/-- **The `p = 2` consumer, end to end.**

The twisted catalogue at `p = 2`, the comparison `TwistTwoComparison` and the local reconstruction
at `p = 2` produce `NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ'` through the on-disk
`NK.Indecomposed.indecomposedPrime_two_of_rankData`. -/
theorem indecomposedPrime_two_of_comparison (h : DeepInputs 2 K K' κ κ')
    (hc : TwistTwoComparison K K') (hrec : NK.Indecomposed.LocalReconstruction 2 K K' κ κ') :
    NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ' :=
  NK.Indecomposed.indecomposedPrime_two_of_rankData (K := K) (K' := K') (κ := κ) (κ' := κ')
    (rankDataTrivial_two_of_comparison h hc) hrec

end NK.IndecomposedDeep
