import Mathlib

namespace Work.ORVonNeumann

open OreLocalization

/-- In an Ore localization `R[S⁻¹]` (of the underlying multiplicative structure of a ring `R`),
the zero element is absorbing on the left.  This is not in Mathlib: the monoid localization
`OreLocalization` carries a `Zero` but no `MulZeroClass` instance. -/
lemma oreLocalization_mul_zero {R : Type*} [Ring R] {S : Submonoid R}
    [OreLocalization.OreSet S] (W : R[S⁻¹]) : W * (0 : R[S⁻¹]) = 0 := by
  induction W using OreLocalization.ind with
  | c p t =>
    rw [OreLocalization.zero_def, OreLocalization.oreDiv_mul_oreDiv]
    simp only [mul_zero]
    rw [OreLocalization.oreDiv_eq_iff]
    exact ⟨OreLocalization.oreDenom p 1 * t, 1, by simp [smul_eq_mul], by simp⟩

/-- The numerator map `R → R[S⁻¹]` of an Ore localization is injective at `0`, provided the
elements of `S` are left-regular.  Equivalently: `x /ₒ 1 = 0` forces `x = 0`.

This is the `x /ₒ 1 = 0 /ₒ 1` case of the general criterion `OreLocalization.oreDiv_eq_iff`,
combined with left-regularity of the elements of `S`. -/
lemma numeratorHom_eq_zero_iff {R : Type*} [Ring R] {S : Submonoid R}
    [OreLocalization.OreSet S] (hS : S ≤ nonZeroDivisorsLeft R) (x : R) :
    (OreLocalization.numeratorHom x : R[S⁻¹]) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hx' : x /ₒ (1 : S) = (0 : R) /ₒ (1 : S) := by
      rw [← OreLocalization.zero_def]; exact hx
    rw [OreLocalization.oreDiv_eq_iff] at hx'
    obtain ⟨u, v, huv, hst⟩ := hx'
    simp only [Submonoid.coe_one, mul_one] at hst
    have hvx : v * x = 0 := by simpa [smul_eq_mul] using huv.symm
    rw [← hst] at hvx
    exact (hS u.2) x hvx
  · rintro rfl
    rw [OreLocalization.numeratorHom_apply, OreLocalization.zero_def]

theorem mem_nonZeroDivisors_of_mul_eq {R : Type*} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S] (hS : S ≤ nonZeroDivisors R) {s x r x' : R} (hs : s ∈ S) (hx : x ∈ S) (hx' : x' ∈ S) (h : s * x = r * x') : r ∈ nonZeroDivisors R := by
  have hSleft : S ≤ nonZeroDivisorsLeft R := fun u hu => (hS hu).1
  rw [nonZeroDivisors, Submonoid.mem_inf]
  constructor
  · -- `r` is left-regular: `r * y = 0 → y = 0`.
    -- Pass to the Ore localization, where `r` is a unit because `s * x = r * x'`
    -- exhibits `r` as `s · x · x'⁻¹` with `s, x, x' ∈ S`.
    intro y hy
    have hmul : (OreLocalization.numeratorHom r : R[S⁻¹]) * OreLocalization.numeratorHom y = 0 := by
      rw [← map_mul, hy, OreLocalization.numeratorHom_apply, OreLocalization.zero_def]
    let U : (R[S⁻¹])ˣ := OreLocalization.numeratorUnit ⟨s, hs⟩ * OreLocalization.numeratorUnit ⟨x, hx⟩
        * (OreLocalization.numeratorUnit ⟨x', hx'⟩)⁻¹
    have hU : (U : R[S⁻¹]) = OreLocalization.numeratorHom r := by
      apply IsUnit.mul_right_cancel (OreLocalization.numerator_isUnit ⟨x', hx'⟩)
      have hrel : (OreLocalization.numeratorHom r : R[S⁻¹]) * OreLocalization.numeratorHom x'
          = OreLocalization.numeratorHom s * OreLocalization.numeratorHom x := by
        rw [← map_mul, ← map_mul, h]
      rw [hrel]
      simp only [U, Units.val_mul, OreLocalization.numeratorHom_apply]
      rw [show (x' /ₒ (1 : S) : R[S⁻¹])
            = (↑(OreLocalization.numeratorUnit ⟨x', hx'⟩) : R[S⁻¹]) from rfl]
      simp only [mul_assoc, Units.inv_mul, mul_one]
      rfl
    have hy0 : (OreLocalization.numeratorHom y : R[S⁻¹]) = 0 := by
      have h1 : (U : R[S⁻¹]) * OreLocalization.numeratorHom y = 0 := by rw [hU, hmul]
      calc (OreLocalization.numeratorHom y : R[S⁻¹])
          = (↑U⁻¹ : R[S⁻¹]) * ↑U * OreLocalization.numeratorHom y := by
            rw [Units.inv_mul, one_mul]
        _ = (↑U⁻¹ : R[S⁻¹]) * (↑U * OreLocalization.numeratorHom y) := by rw [mul_assoc]
        _ = (↑U⁻¹ : R[S⁻¹]) * 0 := by rw [h1]
        _ = 0 := oreLocalization_mul_zero (↑U⁻¹ : R[S⁻¹])
    exact (numeratorHom_eq_zero_iff hSleft y).1 hy0
  · -- `r` is right-regular: `y * r = 0 → y = 0`.
    intro y hy
    have hys : y * s = 0 := by
      have h1 : (y * r) * x' = 0 := by rw [hy, zero_mul]
      rw [mul_assoc, ← h] at h1
      rw [← mul_assoc] at h1
      exact (hS hx).2 (y * s) h1
    exact (hS hs).2 y hys

end Work.ORVonNeumann
