import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.t_mem_and_center_quotient
import Submission.Work.ThmF.Setup
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.PSU3.StageA.isStronglyEmbeddedInfSubgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.NotFpfStep2.center_le_centD`

Peterfalvi II, Ch. VII §4 (1) (p. 278), first half: for `U = O^{2'}(C_G(P))`,
`Z(U) ⊆ V = C_D(t)`.

This is the hypothesis `hZV` consumed by the sibling files
`Submission/Work/PSU3/StageB/NotFpfStep2/center_le_P.lean` and
`Submission/Work/PSU3/StageB/centralizerOddResidual_center_le_P.lean`, which continue the
argument and prove the stronger `Z(U) ⊆ P`.

The proof found here is **much cheaper than the source's route**: no Galois theory and no
`W ≠ ⊥` are needed.  Only two facts are used:

* `t ∈ U`, because `P ≤ V = C_D(t)` makes `t` centralise `P` and `orderOf t = 2`;
* `y ∈ U` is nontrivial, because `y ∈ Q` and `P` centralises `y`, so `H ⊓ U` has even order.

Then `Z(U) ⊆ H` by the standard fact that the centre of a finite group lies in every strongly
embedded subgroup: if `U ⊄ H` then `H ⊓ U` is strongly embedded in `U`
(`Work.PSU3.StageA.isStronglyEmbeddedInfSubgroupOf`), whence
`Z(U) ≤ H ⊓ U` (`Work.PSU3.StageA.center_le_of_isStronglyEmbedded`); if `U ≤ H` this is
immediate.  Finally `t ∈ U` gives `Z(U) ⊆ C_G(t)`, so `Z(U) ⊆ H ⊓ C_G(t)`, and since
`Z(U)` commutes with `t` this also gives `Z(U) ⊆ H^t = H^t`, i.e. `Z(U) ⊆ D = H ⊓ H^t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageB.NotFpfStep2

/-- **`Z(U) ⊆ V = C_D(t)`** for `U = O^{2'}(C_G(P))`, Peterfalvi II Ch. VII §4 (1) (p. 278),
in the type-corrected `map subtype` form used by its consumers.

`P ≤ V = C_D(t)` has prime order and centralises `y ∈ Q ∖ Q₀`.  The elements used are
`t ∈ U` (a `2`-element of `C_G(P)`, hence in `O^{2'}(C_G(P))`) and `y ∈ U` (nontrivial, since
`y ∉ Q₀ ∋ 1`); `y` makes `H ⊓ U` even, and then the centre of `U` lies in every strongly
embedded subgroup of `U`. -/
theorem center_le_centD {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y) :
    (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ Submission.Blueprint.centD H t := by
  classical
  let U : Subgroup G := Work.PSU3.StageB.centralizerOddResidual P
  -- ## 1. `t ∈ U`: `t` centralises `P` and has order `2`
  have htC : t ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hPV hp)).2
  have htU : t ∈ U :=
    Work.PSU3.StageA.mem_map_oddResidual_of_orderOf_eq_two_pow htC (k := 1)
      (by rw [hS.split.invol]; norm_num)
  -- ## 2. `y ∈ U` and `y ≠ 1`
  have hyC : y ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Work.PSU3.StageB.mul_comm_of_conj_eq_self (hyc p hp)).symm
  have hyU : y ∈ U := Work.PSU3.StageA.mem_map_oddResidual_of_mem_isPGroup hS.two hyQ hyC
  have hy1 : y ≠ 1 := fun h => hy0 (h ▸ (Work.ThmF.Q0sub H).one_mem)
  -- ## 3. `Z(U) ⊆ H`
  have hZH : ∀ z ∈ Subgroup.center ↥U, (z : G) ∈ H := by
    intro z hz
    by_cases hUH : U ≤ H
    · exact hUH z.2
    · -- `H ⊓ U` is strongly embedded in `U`; it is even because `y ∈ H ⊓ U`
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS.two
      have hdvd : orderOf y ∣ 2 ^ n := by
        rw [← hn]
        exact Subgroup.orderOf_dvd_natCard Q hyQ
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hk1 : 1 ≤ k := by
        by_contra h
        have h0 : k = 0 := by omega
        rw [h0, pow_zero] at hk
        exact hy1 (orderOf_eq_one_iff.mp hk)
      have hyHU : y ∈ H ⊓ U := ⟨hS.split.le hyQ, hyU⟩
      have h2dvd : 2 ∣ Nat.card ↥(H ⊓ U) := by
        have h1 : 2 ∣ orderOf y := by
          rw [hk]
          exact dvd_pow_self 2 (by omega)
        exact h1.trans (Subgroup.orderOf_dvd_natCard (H ⊓ U) hyHU)
      obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
      have hFinv : ∃ u ∈ H ⊓ U, orderOf u = 2 :=
        ⟨(x0 : G), x0.2, by rw [Subgroup.orderOf_coe, hx0]⟩
      have hSE : IsStronglyEmbedded ((H ⊓ U).subgroupOf U) :=
        Work.PSU3.StageA.isStronglyEmbeddedInfSubgroupOf hS.split.stronglyEmbedded hUH hFinv
      exact (Subgroup.mem_subgroupOf.mp
        (Work.PSU3.StageA.center_le_of_isStronglyEmbedded hSE hz)).1
  -- ## 4. Assembly: `z ∈ H`, `z` commutes with `t`, hence `z ∈ D ⊓ C_G(t) = V`
  rintro z hz
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
  have hxH : (x : G) ∈ H := hZH x hx
  have hxt : t * (x : G) = (x : G) * t :=
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) ⟨t, htU⟩)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Work.Models.mem_twoPoint_iff]
    refine ⟨hxH, ?_⟩
    change t⁻¹ * (x : G) * t ∈ H
    rw [mul_assoc, ← hxt, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hxH
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm

end Work.PSU3.StageB.NotFpfStep2
