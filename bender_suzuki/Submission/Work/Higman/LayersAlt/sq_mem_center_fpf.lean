/-
Copyright (c) 2024. All rights reserved.

# Squares of a Suzuki 2-group with a fixed-point-free `ξ` are central

Target: `Work.Higman.LayersAlt.sq_mem_center_fpf`.

`FpfXi ξ` (see `Submission/Work/Higman/typeB.lean`) says that `|P| = |Z(P)|³`, that `ξ` has
order `|Z(P)| - 1` and that every non-trivial power of `ξ` is fixed-point-free on `P ∖ {1}`.
Under this hypothesis the elementary theory of Suzuki 2-groups (Higman 1963, §2, transcribed in
`REFS/higman_suzuki2groups.md`) gives

* `Z(P) = Ω₁(P)` is elementary abelian of order `q = 2 ^ N`, `q ≥ 4`,
* the involutions number `q - 1` and form a single `⟨ξ⟩`-orbit,
* every non-trivial `ξ`-invariant subgroup contains `Z(P)`,

all of which are proved below (see also `LayersAlt.GroupSide`).

The proof of the target is a case split on whether `P` is of class two:

* if `P' ≤ Z(P)`, then `P / Z(P)` has exponent two and every square is central — this is
  `Work.Higman.LayersAlt.class_two_target`;
* otherwise a hypothetical `x` with `x² ∉ Z(P)` forces the structure `P² = P'` with
  `(P')² = Z(P)` (`Work.Higman.LayersAlt.bad_case_structure`), which is excluded by
  `Work.Higman.LayersAlt.class_three_exclusion` (Higman 1963, §4 Lemma 6).

The named subgroups `derivTop = ⁅P,P⁆`, `derivDerivTop` and `sqSub = P²` are introduced in
`Submission/Work/Higman/LayersAlt/fpf_defs.lean`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.typeB
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.LayersAlt.fpf_defs
import Submission.Work.Higman.LayersAlt.GroupSide
import Submission.Work.Higman.BS.fpf
import Submission.Work.Higman.LayersAlt.class_two_target
import Submission.Work.Higman.LayersAlt.class_three_exclusion
import Submission.Work.Higman.LayersAlt.bad_case_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.LayersAlt

variable {P : Type} [Group P] [Finite P]

/-! ## Elementary structure -/

/-- `Z(P) = Ω₁(P)` for a Suzuki 2-group with `FpfXi ξ` (Higman 1963, §2). -/
theorem center_eq_omega1_fpf (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) :
    Subgroup.center P = Work.Higman.omega1 P :=
  center_eq_omega1_of_fpf h hξ

/-- `|Z(P)| ≥ 4`. -/
theorem center_card_ge_four (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) :
    4 ≤ Nat.card ↥(Subgroup.center P) := by
  rw [center_eq_omega1_fpf h hξ]
  exact h.omega1_card_ge_four

/-- The number of involutions of a Suzuki 2-group with `FpfXi ξ` is `|Z(P)| - 1`. -/
theorem invol_ncard_fpf (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) :
    (Work.Higman.Invol P).ncard = Nat.card ↥(Subgroup.center P) - 1 := by
  have hcard : Nat.card ↥(Subgroup.center P) = (Work.Higman.Invol P).ncard + 1 := by
    rw [center_eq_omega1_fpf h hξ]
    exact h.card_omega1
  omega

/-- **The `⟨ξ⟩`-orbit of an involution is the set of all involutions.** -/
theorem orbit_invol_fpf (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ)
    {z w : P} (hz : orderOf z = 2) (hw : orderOf w = 2) : ∃ k : ℕ, (ξ ^ k) z = w := by
  classical
  have hstep : ∀ k : ℕ, orderOf ((ξ ^ k) z) = 2 := by
    intro k
    rw [MulEquiv.orderOf_eq (ξ ^ k) z, hz]
  have hne1 : ∀ k : ℕ, (ξ ^ k) z ≠ 1 := by
    intro k h1
    have h2 := hstep k
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hsub : Set.range (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) z) ⊆
      (Work.Higman.Invol P : Set P) := by
    rintro _ ⟨k, rfl⟩
    rw [Work.Higman.mem_Invol, MulEquiv.orderOf_eq (ξ ^ (k : ℕ)) z, hz]
  have hinj : Function.Injective (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) z) := by
    intro a b hab
    have h1 : (ξ ^ (a : ℕ)) z = (ξ ^ (b : ℕ)) z := hab
    rcases le_total (a : ℕ) (b : ℕ) with hle | hle
    · have h2 : (ξ ^ ((b : ℕ) - (a : ℕ))) ((ξ ^ (a : ℕ)) z) = (ξ ^ (a : ℕ)) z := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hle, h1]
      have h3 : ξ ^ ((b : ℕ) - (a : ℕ)) = 1 := by
        by_contra hc
        exact hne1 _ (hξ.fpf _ hc _ h2)
      have h4 : orderOf ξ ∣ (b : ℕ) - (a : ℕ) := orderOf_dvd_iff_pow_eq_one.mpr h3
      have h5 : (b : ℕ) - (a : ℕ) < orderOf ξ := lt_of_le_of_lt (Nat.sub_le _ _) b.isLt
      have h6 : (b : ℕ) - (a : ℕ) = 0 := by
        rcases Nat.eq_zero_or_pos _ with h0 | hpos
        · exact h0
        · exact absurd (Nat.le_of_dvd hpos h4) (not_le.mpr h5)
      exact Fin.ext (by omega)
    · have h2 : (ξ ^ ((a : ℕ) - (b : ℕ))) ((ξ ^ (b : ℕ)) z) = (ξ ^ (b : ℕ)) z := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hle, ← h1]
      have h3 : ξ ^ ((a : ℕ) - (b : ℕ)) = 1 := by
        by_contra hc
        exact hne1 _ (hξ.fpf _ hc _ h2)
      have h4 : orderOf ξ ∣ (a : ℕ) - (b : ℕ) := orderOf_dvd_iff_pow_eq_one.mpr h3
      have h5 : (a : ℕ) - (b : ℕ) < orderOf ξ := lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
      have h6 : (a : ℕ) - (b : ℕ) = 0 := by
        rcases Nat.eq_zero_or_pos _ with h0 | hpos
        · exact h0
        · exact absurd (Nat.le_of_dvd hpos h4) (not_le.mpr h5)
      exact Fin.ext (by omega)
  have hcard : (Set.range (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) z)).ncard = orderOf ξ := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_fin]
  have hInvol : (Work.Higman.Invol P).ncard = orderOf ξ := by
    rw [invol_ncard_fpf h hξ, hξ.order]
  have heq : Set.range (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) z) =
      (Work.Higman.Invol P : Set P) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hInvol])
  have hwmem : w ∈ Set.range (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) z) := by
    rw [heq]
    exact hw
  obtain ⟨k, hk⟩ := hwmem
  exact ⟨(k : ℕ), hk⟩

/-- **Every non-trivial `ξ`-invariant subgroup contains `Z(P)`.** -/
theorem center_le_of_invariant (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ)
    {K : Subgroup P} (hK : K.map ξ.toMonoidHom = K) (hne : K ≠ ⊥) :
    Subgroup.center P ≤ K := by
  classical
  haveI : Nontrivial ↥K := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hne)
    exact ⟨a, 1, ha⟩
  have hdvd : 2 ∣ Nat.card ↥K := by
    rcases (h.isPGroup.to_subgroup K).card_eq_or_dvd with h1 | h2
    · exact absurd h1 (by
        intro hc
        exact (not_subsingleton_iff_nontrivial.mpr inferInstance)
          (Nat.card_eq_one_iff_unique.mp hc).1)
    · exact h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hpow : ∀ k : ℕ, (ξ ^ k) (z : P) ∈ K := by
    intro k
    induction k with
    | zero => simpa using z.2
    | succ k ih =>
        have h1 : ξ ((ξ ^ k) (z : P)) ∈ K := by
          have h2 : ξ ((ξ ^ k) (z : P)) ∈ K.map ξ.toMonoidHom :=
            Subgroup.mem_map_of_mem _ ih
          rwa [hK] at h2
        rw [pow_succ', MulAut.mul_apply]
        exact h1
  intro y hy
  rcases (show orderOf y = 1 ∨ orderOf y = 2 by
      have h1 : y ∈ Work.Higman.omega1 P := by rw [← center_eq_omega1_fpf h hξ]; exact hy
      have h2 : y ^ 2 = 1 := h.mem_omega1.mp h1
      have h3 : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h4 | h5
      · exact Or.inl h4
      · exact Or.inr h5) with h1 | h2
  · rw [orderOf_eq_one_iff.mp h1]
    exact K.one_mem
  · obtain ⟨k, hk⟩ := orbit_invol_fpf h hξ (z := (z : P)) (w := y)
      (Subgroup.orderOf_coe z ▸ hz) h2
    rw [← hk]
    exact hpow k

/-! ## The target -/

/-- In a Suzuki 2-group with a fixed-point-free automorphism `ξ` of order `|Z(P)| - 1`, every
square is central.  The two cases are the class-two case (`class_two_target`) and the
class-three exclusion (`class_three_exclusion`, Higman 1963, §4 Lemma 6), glued by the structural
reduction `bad_case_structure`. -/
theorem sq_mem_center_fpf {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  by_cases hcl2 : derivTop P ≤ Subgroup.center P
  · exact class_two_target h hξ hcl2
  · by_contra hcon
    push Not at hcon
    obtain ⟨hP2, hsq2⟩ := bad_case_structure h hξ hcon hcl2
    exact class_three_exclusion h hξ hP2 hsq2

end Work.Higman.LayersAlt
