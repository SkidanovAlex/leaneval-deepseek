/-
Copyright (c) 2024. All rights reserved.

# Suzuki 2-groups: elementary structure

Higman, *Suzuki 2-groups* (1963), §2.  Everything in this file is the "evident" part:
in a Suzuki 2-group every involution is central, `Ω₁(P)` is elementary abelian and consists
of `1` together with the involutions, `|Ω₁(P)| = q = 2ⁿ` with `n ≥ 2`, and the cyclic group
`⟨ξ⟩` of automorphisms has order divisible by `q - 1`.
-/

import Submission.Work.Higman.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

theorem one_notMem_Invol : (1 : P) ∉ Invol P := by
  simp

namespace IsSuzuki2Grp

theorem nontrivial (h : IsSuzuki2Grp P) : Nontrivial P := by
  obtain ⟨x, y, hxy⟩ := h.noncomm
  exact ⟨x, y, fun hc => hxy (by rw [hc])⟩

theorem center_nontrivial (h : IsSuzuki2Grp P) : Nontrivial (Subgroup.center P) := by
  haveI := h.nontrivial
  exact h.isPGroup.center_nontrivial

/-- A Suzuki 2-group has a central involution. -/
theorem exists_central_involution (h : IsSuzuki2Grp P) :
    ∃ z : P, z ∈ Subgroup.center P ∧ orderOf z = 2 := by
  haveI := h.nontrivial
  have hZ : IsPGroup 2 (Subgroup.center P) := h.isPGroup.to_subgroup _
  have hZn : Nontrivial (Subgroup.center P) := h.isPGroup.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    rcases hZ.card_eq_or_dvd with h1 | h2
    · exfalso
      exact (not_subsingleton_iff_nontrivial.mpr hZn) (Nat.card_eq_one_iff_unique.mp h1).1
    · exact h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨(z : P), z.2, (Subgroup.orderOf_coe z).trans hz⟩

/-- **Every involution of a Suzuki 2-group is central** (Higman 1963, §2, "evidently"). -/
theorem invol_mem_center (h : IsSuzuki2Grp P) {u : P} (hu : orderOf u = 2) :
    u ∈ Subgroup.center P := by
  obtain ⟨z, hz, hz2⟩ := h.exists_central_involution
  obtain ⟨k, hk⟩ := h.trans z u hz2 hu
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have hw : (h.xi ^ k) ((h.xi ^ k)⁻¹ g) = g := by simp
  have hzw := hz ((h.xi ^ k)⁻¹ g)
  calc g * u = (h.xi ^ k) ((h.xi ^ k)⁻¹ g) * (h.xi ^ k) z := by rw [hw, hk]
    _ = (h.xi ^ k) ((h.xi ^ k)⁻¹ g * z) := by rw [map_mul]
    _ = (h.xi ^ k) (z * (h.xi ^ k)⁻¹ g) := by rw [hzw]
    _ = (h.xi ^ k) z * (h.xi ^ k) ((h.xi ^ k)⁻¹ g) := by rw [map_mul]
    _ = u * g := by rw [hw, hk]

/-- An element with `x ^ 2 = 1` is central. -/
theorem sqOne_mem_center (h : IsSuzuki2Grp P) {x : P} (hx : x ^ 2 = 1) :
    x ∈ Subgroup.center P := by
  rcases eq_or_ne x 1 with rfl | hx1
  · exact Subgroup.one_mem _
  · refine h.invol_mem_center ?_
    have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h2

/-- `Ω₁(P)` is contained in the centre. -/
theorem omega1_le_center (h : IsSuzuki2Grp P) : omega1 P ≤ Subgroup.center P := by
  change Subgroup.closure (sqOne P) ≤ Subgroup.center P
  rw [Subgroup.closure_le]
  exact fun x hx => h.sqOne_mem_center hx

/-- **The elements of `Ω₁(P)` are exactly the elements of order dividing `2`.** -/
theorem mem_omega1 (h : IsSuzuki2Grp P) {x : P} : x ∈ omega1 P ↔ x ^ 2 = 1 := by
  refine ⟨fun hx => ?_, fun hx => Subgroup.subset_closure hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact one_pow 2
  | mul x y _ _ px py =>
      have cx : ∀ a : P, a * x = x * a := Subgroup.mem_center_iff.mp (h.sqOne_mem_center px)
      have hcomm : Commute x y := by
        rw [Commute]
        exact (cx y).symm
      rw [hcomm.mul_pow, px, py, one_mul]
  | inv x _ px => rw [inv_pow, px, inv_one]

/-- `Ω₁(P) = {x | x ^ 2 = 1}` as sets. -/
theorem coe_omega1 (h : IsSuzuki2Grp P) : (omega1 P : Set P) = sqOne P := by
  ext x
  rw [SetLike.mem_coe, h.mem_omega1, mem_sqOne]

/-- `Ω₁(P)` is elementary abelian. -/
theorem omega1_sq_eq_one (h : IsSuzuki2Grp P) {x : P} (hx : x ∈ omega1 P) : x ^ 2 = 1 :=
  h.mem_omega1.mp hx

theorem omega1_comm (h : IsSuzuki2Grp P) {x y : P} (hx : x ∈ omega1 P)
    (hy : y ∈ omega1 P) : x * y = y * x := by
  have cx := h.sqOne_mem_center (h.mem_omega1.mp hx)
  exact (Subgroup.mem_center_iff.mp cx y).symm

/-- `|Ω₁(P)| = |Invol P| + 1`. -/
theorem card_omega1 (h : IsSuzuki2Grp P) : Nat.card (omega1 P) = (Invol P).ncard + 1 := by
  have hcoe : (omega1 P : Set P) = insert 1 (Invol P) := by
    rw [h.coe_omega1, sqOne_eq_Invol_insert_one]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hcoe,
    Set.ncard_insert_of_notMem one_notMem_Invol (Set.toFinite _), Nat.add_comm]

/-- `|Ω₁(P)|` is a power of `2`. -/
theorem exists_card_omega1_eq_two_pow (h : IsSuzuki2Grp P) :
    ∃ n : ℕ, Nat.card (omega1 P) = 2 ^ n :=
  (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup _)

/-- `|Ω₁(P)| = q ≥ 4`. -/
theorem omega1_card_ge_four (h : IsSuzuki2Grp P) : 4 ≤ Nat.card (omega1 P) := by
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  obtain ⟨x, y, hx2, hy2, hxy⟩ := h.manyInvol
  have h1x : (1 : P) ≠ x := by rintro rfl; exact absurd hx2 (by simp)
  have h1y : (1 : P) ≠ y := by rintro rfl; exact absurd hy2 (by simp)
  have hx_sq : x ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hx2]
  have hy_sq : y ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hy2]
  have hxmem : x ∈ omega1 P := Subgroup.subset_closure (mem_sqOne.mpr hx_sq)
  have hymem : y ∈ omega1 P := Subgroup.subset_closure (mem_sqOne.mpr hy_sq)
  have hsub : ({1, x, y} : Set P) ⊆ (omega1 P : Set P) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxmem
    · exact hymem
  have hcard3 : ({1, x, y} : Set P).ncard = 3 := by
    have h1 : (1 : P) ∉ ({x, y} : Set P) := by simp [h1x, h1y]
    have h2 : x ∉ ({y} : Set P) := by simpa using hxy
    rw [Set.ncard_insert_of_notMem h1 (Set.toFinite _),
      Set.ncard_insert_of_notMem h2 (Set.toFinite _), Set.ncard_singleton]
  have h3 : 3 ≤ Nat.card (omega1 P) := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc 3 = ({1, x, y} : Set P).ncard := hcard3.symm
      _ ≤ (omega1 P : Set P).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n <;> (rw [hn] at h3 <;> norm_num at h3)
    · exact hge
  rw [hn]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

end IsSuzuki2Grp

end Work.Higman
