/-
Copyright (c) 2024. All rights reserved.

# The group-theoretic side of the layer dichotomy

For a Suzuki 2-group `P` with `FpfXi ξ` we prove here, without appealing to the classification
of Suzuki 2-groups:

* `center_eq_omega1_of_fpf`: `Z(P) = Ω₁(P)` (Higman 1963, §2) — here in the form that it
  follows from the existence of *some* fixed-point-free automorphism of order `|Z(P)| - 1`;
* `quotMulEquiv_props`: the automorphism induced by `ξ` on `V = P / Z(P)` has order
  `2 ^ N - 1` (`|Z(P)| = 2 ^ N`), acts fixed-point-freely on `V \ {0}`, and `|V| = (2 ^ N) ^ 2`.
-/

import Mathlib
import Submission.Work.Higman.LayersAlt.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

open scoped commutatorElement

namespace Work.Higman.LayersAlt

variable {P : Type} [Group P] [Finite P]

/-! ## `Z(P) = Ω₁(P)` -/

/-- **`Z(P) = Ω₁(P)`** (Higman 1963, §2).  For a Suzuki 2-group `P` admitting a fixed-point-free
automorphism `ξ` of order `|Z(P)| - 1`, the centre is elementary abelian.

Indeed every element of the `⟨ξ⟩`-orbit of an involution `x ≠ 1` is an involution, and these
`orderOf ξ` elements are distinct (a relation `ξ ^ a x = ξ ^ b x`, `a < b < orderOf ξ`, forces the
non-trivial power `ξ ^ (b - a)` to fix `x ≠ 1`, which fixed-point-freeness forbids).  So
`|Z(P)| - 1 = orderOf ξ ≤ #Invol P = |Ω₁(P)| - 1`; with `Ω₁(P) ≤ Z(P)` this gives
`Ω₁(P) = Z(P)`. -/
theorem center_eq_omega1_of_fpf (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) :
    Subgroup.center P = omega1 P := by
  classical
  obtain ⟨x, y, hx2, hy2, hxy⟩ := h.manyInvol
  have hstep : ∀ k : ℕ, orderOf ((ξ ^ k) x) = 2 := by
    intro k
    rw [MulEquiv.orderOf_eq (ξ ^ k) x, hx2]
  have hne1 : ∀ k : ℕ, (ξ ^ k) x ≠ 1 := by
    intro k h0
    have h1 := hstep k
    rw [h0, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  -- the elements `ξ ^ k x`, `k < orderOf ξ`, are distinct
  have key : ∀ a b : ℕ, a < orderOf ξ → b < orderOf ξ →
      (ξ ^ a) x = (ξ ^ b) x → a = b := by
    intro a b ha hb hab
    rcases le_total a b with hle | hle
    · have h2 : (ξ ^ (b - a)) ((ξ ^ a) x) = (ξ ^ b) x := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
      have h3 : (ξ ^ (b - a)) ((ξ ^ a) x) = (ξ ^ a) x := h2.trans hab.symm
      have h4 : ξ ^ (b - a) = 1 := by
        by_contra hc
        exact hne1 a (hξ.fpf (b - a) hc ((ξ ^ a) x) h3)
      have h5 : orderOf ξ ∣ b - a := orderOf_dvd_iff_pow_eq_one.mpr h4
      have h6 : b - a < orderOf ξ := lt_of_le_of_lt (Nat.sub_le b a) hb
      have h7 : b - a = 0 := by
        rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
        · exact h0
        · exact absurd (Nat.le_of_dvd hpos h5) (not_le.mpr h6)
      omega
    · have h2 : (ξ ^ (a - b)) ((ξ ^ b) x) = (ξ ^ a) x := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
      have h3 : (ξ ^ (a - b)) ((ξ ^ b) x) = (ξ ^ b) x := h2.trans hab
      have h4 : ξ ^ (a - b) = 1 := by
        by_contra hc
        exact hne1 b (hξ.fpf (a - b) hc ((ξ ^ b) x) h3)
      have h5 : orderOf ξ ∣ a - b := orderOf_dvd_iff_pow_eq_one.mpr h4
      have h6 : a - b < orderOf ξ := lt_of_le_of_lt (Nat.sub_le a b) ha
      have h7 : a - b = 0 := by
        rcases Nat.eq_zero_or_pos (a - b) with h0 | hpos
        · exact h0
        · exact absurd (Nat.le_of_dvd hpos h5) (not_le.mpr h6)
      omega
  have hinj : Function.Injective (fun k : Fin (orderOf ξ) =>
      (⟨(ξ ^ (k : ℕ)) x, hstep k⟩ : ↥(Invol P))) := by
    intro a b hab
    have h1 : (ξ ^ (a : ℕ)) x = (ξ ^ (b : ℕ)) x := congrArg Subtype.val hab
    exact Fin.ext (key a b a.isLt b.isLt h1)
  have hle : orderOf ξ ≤ (Invol P).ncard := by
    have h1 : Nat.card (Fin (orderOf ξ)) ≤ Nat.card ↥(Invol P) :=
      Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fin, Nat.card_coe_set_eq] at h1
  have hInvol : (Invol P).ncard = Nat.card ↥(omega1 P) - 1 := by
    have h1 := h.card_omega1
    omega
  have hOmZ : Nat.card ↥(omega1 P) ≤ Nat.card ↥(Subgroup.center P) :=
    Nat.card_le_card_of_injective
      (fun u : ↥(omega1 P) => (⟨(u : P), h.omega1_le_center u.2⟩ : ↥(Subgroup.center P)))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have heq1 : Nat.card ↥(omega1 P) - 1 = Nat.card ↥(Subgroup.center P) - 1 := by
    refine le_antisymm (Nat.sub_le_sub_right hOmZ 1) ?_
    rw [← hξ.order, ← hInvol]
    exact hle
  have heq : Nat.card ↥(omega1 P) = Nat.card ↥(Subgroup.center P) := by
    have h1 : 0 < Nat.card ↥(omega1 P) := Nat.card_pos
    have h2 : 0 < Nat.card ↥(Subgroup.center P) := Nat.card_pos
    omega
  exact (Subgroup.eq_of_le_of_card_ge h.omega1_le_center (le_of_eq heq.symm)).symm

/-- In a Suzuki 2-group with `FpfXi ξ`, the centre is elementary abelian. -/
theorem center_sq_one (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) {z : P}
    (hz : z ∈ Subgroup.center P) : z * z = 1 := by
  have hZ : Subgroup.center P = omega1 P := center_eq_omega1_of_fpf h hξ
  have h1 : z ∈ omega1 P := hZ ▸ hz
  have h2 := h.mem_omega1.mp h1
  rwa [pow_two] at h2

/-- If `ξ ^ k` moves `a` inside its coset modulo `Z(P)` (`(ξ ^ k) a = a * z` with `z` central),
then `ξ ^ k` fixes `a * a`. -/
theorem pow_fixes_sq (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) (k : ℕ) {a z : P}
    (hz : z ∈ Subgroup.center P) (hza : (ξ ^ k) a = a * z) :
    (ξ ^ k) (a * a) = a * a := by
  have hz2 : z * z = 1 := center_sq_one h hξ hz
  have hzc : a * z = z * a := Subgroup.mem_center_iff.mp hz a
  calc (ξ ^ k) (a * a) = (ξ ^ k) a * (ξ ^ k) a := map_mul _ _ _
    _ = (a * z) * (a * z) := by rw [hza]
    _ = a * (z * a) * z := by group
    _ = a * (a * z) * z := by rw [hzc]
    _ = (a * a) * (z * z) := by group
    _ = a * a := by rw [hz2, mul_one]

/-- **`ξ ^ k` acts trivially on `V = P / Z(P)` iff `ξ ^ k = 1`.** -/
theorem quotMulEquiv_pow_eq_one_iff (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) (k : ℕ) :
    (quotMulEquiv h ξ) ^ k = 1 ↔ ξ ^ k = 1 := by
  classical
  constructor
  · intro hσ
    by_contra hne
    obtain ⟨a, b, hab⟩ := h.noncomm
    have haZ : a ∉ Subgroup.center P := fun ha =>
      hab ((Subgroup.mem_center_iff.mp ha b).symm)
    have h2 : ((QuotientGroup.mk a : P ⧸ Subgroup.center P)) =
        QuotientGroup.mk ((ξ ^ k) a) := by
      have h1 := quotMulEquiv_pow_mk h ξ k a
      rw [hσ] at h1
      simpa using h1
    have h3 : a⁻¹ * ((ξ ^ k) a) ∈ Subgroup.center P := QuotientGroup.eq.mp h2
    have hza : (ξ ^ k) a = a * (a⁻¹ * ((ξ ^ k) a)) := by group
    have hfix := pow_fixes_sq h hξ k h3 hza
    have haa1 : a * a ≠ 1 := by
      intro haa
      refine haZ ?_
      rw [center_eq_omega1_of_fpf h hξ]
      exact h.mem_omega1.mpr (by rw [pow_two]; exact haa)
    exact haa1 (hξ.fpf k hne (a * a) hfix)
  · intro h1
    ext q
    refine Quotient.inductionOn q (fun x => ?_)
    rw [quotMulEquiv_pow_mk h ξ k x, h1]
    rfl

/-- **The automorphism of `V = P / Z(P)` induced by `ξ` has order `2 ^ N - 1`, acts
fixed-point-freely on `V \ {0}`, and `|V| = (2 ^ N) ^ 2`**, where `|Z(P)| = 2 ^ N`. -/
theorem quotMulEquiv_props (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) {N : ℕ}
    (hN : Nat.card ↥(Subgroup.center P) = 2 ^ N) :
    orderOf (quotMulEquiv h ξ) = 2 ^ N - 1 ∧
    (∀ k : ℕ, (quotMulEquiv h ξ) ^ k ≠ 1 →
      ∀ q : P ⧸ Subgroup.center P, q ≠ 1 → ((quotMulEquiv h ξ) ^ k) q ≠ q) ∧
    Nat.card (P ⧸ Subgroup.center P) = (2 ^ N) ^ 2 ∧ 1 ≤ N := by
  classical
  have hZ : Subgroup.center P = omega1 P := center_eq_omega1_of_fpf h hξ
  have hZ4 : 4 ≤ Nat.card ↥(Subgroup.center P) := by rw [hZ]; exact h.omega1_card_ge_four
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the order is the order of `ξ`
    have hdvd1 : orderOf (quotMulEquiv h ξ) ∣ orderOf ξ := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact (quotMulEquiv_pow_eq_one_iff h hξ (orderOf ξ)).mpr (pow_orderOf_eq_one ξ)
    have hdvd2 : orderOf ξ ∣ orderOf (quotMulEquiv h ξ) := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact (quotMulEquiv_pow_eq_one_iff h hξ (orderOf (quotMulEquiv h ξ))).mp
        (pow_orderOf_eq_one _)
    have h1 : orderOf (quotMulEquiv h ξ) = orderOf ξ := Nat.dvd_antisymm hdvd1 hdvd2
    rw [h1, hξ.order, hN]
  · -- fixed-point-freeness on `V \ {0}`
    intro k hk q hq hfix
    have hk' : ¬ (quotMulEquiv h ξ ^ k = 1) := hk
    rw [quotMulEquiv_pow_eq_one_iff h hξ k] at hk'
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) q
    subst ha
    have haZ : a ∉ Subgroup.center P := fun hc =>
      hq (by rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff a).mpr hc)
    have h2 : ((QuotientGroup.mk a : P ⧸ Subgroup.center P)) =
        QuotientGroup.mk ((ξ ^ k) a) := by
      have h1 : (quotMulEquiv h ξ ^ k) (QuotientGroup.mk a) = QuotientGroup.mk a := by
        simpa [QuotientGroup.mk'_apply] using hfix
      rw [quotMulEquiv_pow_mk h ξ k a] at h1
      exact h1.symm
    have h3 : a⁻¹ * ((ξ ^ k) a) ∈ Subgroup.center P := QuotientGroup.eq.mp h2
    have hza : (ξ ^ k) a = a * (a⁻¹ * ((ξ ^ k) a)) := by group
    have hfix2 := pow_fixes_sq h hξ k h3 hza
    have haa1 : a * a ≠ 1 := by
      intro haa
      refine haZ ?_
      rw [hZ]
      exact h.mem_omega1.mpr (by rw [pow_two]; exact haa)
    exact haa1 (hξ.fpf k hk' (a * a) hfix2)
  · -- cardinality of `V`
    have hcard : Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) =
        Nat.card P := (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)).symm
    have hP : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3 := hξ.card_cube
    have hpos : 0 < Nat.card ↥(Subgroup.center P) := Nat.card_pos
    have h2 : Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) =
        (2 ^ N) ^ 2 * Nat.card ↥(Subgroup.center P) := by
      rw [hcard, hP, hN]; ring
    rw [Nat.mul_right_cancel hpos h2]
  · -- `1 ≤ N`
    have h2 : (2:ℕ) ^ 2 ≤ 2 ^ N := by
      calc (2:ℕ) ^ 2 = 4 := by norm_num
        _ ≤ Nat.card ↥(Subgroup.center P) := hZ4
        _ = 2 ^ N := hN
    have h3 : ¬ (N < 2) := by
      intro hlt
      have h4 : 2 ^ N ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h4
      omega
    omega

end Work.Higman.LayersAlt
