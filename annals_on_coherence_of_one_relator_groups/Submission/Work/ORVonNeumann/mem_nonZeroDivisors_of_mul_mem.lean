import Mathlib

namespace Work.ORVonNeumann

/-- If `S` is an Ore set consisting of non-zero-divisors and `a * d ∈ S` for some `d ∈ S`,
then `a` is a non-zero-divisor.

Right-regularity of `a` is immediate from the right-regularity of `a * d`.  For
left-regularity we pass to the Ore localization `R[S⁻¹]`: the fraction of `a * d` becomes a
unit there, hence so does the fraction of `a = (a * d) * d⁻¹`, and the localization map is
injective because `S` consists of left non-zero-divisors. -/
theorem mem_nonZeroDivisors_of_mul_mem {R : Type*} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S] (hS : S ≤ nonZeroDivisors R) {a : R} {d : S} (h : a * (d : R) ∈ S) : a ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    -- the image of `a` in the Ore localization is a unit
    obtain ⟨u, hu⟩ := OreLocalization.numerator_isUnit (⟨a * (d : R), h⟩ : S)
    obtain ⟨w, hw⟩ := OreLocalization.numerator_isUnit d
    have huw : (u : OreLocalization S R) = OreLocalization.numeratorHom a * (w : OreLocalization S R) := by
      rw [hu, map_mul, hw]
    have hunit : IsUnit (OreLocalization.numeratorHom (S := S) a : OreLocalization S R) := by
      have h1 : IsUnit ((u : OreLocalization S R) * ↑(w⁻¹)) :=
        (Units.isUnit_units_mul u (↑(w⁻¹))).mpr (w⁻¹).isUnit
      have h2 : OreLocalization.numeratorHom (S := S) a = (u : OreLocalization S R) * ↑(w⁻¹) := by
        rw [huw, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rwa [← h2] at h1
    have h0 : (OreLocalization.numeratorHom (S := S) a : OreLocalization S R) *
        OreLocalization.numeratorHom x = 0 := by
      rw [← map_mul, hx, OreLocalization.numeratorHom_apply, OreLocalization.zero_oreDiv']
    have hx0 : OreLocalization.numeratorHom (S := S) x = 0 := (IsUnit.mul_right_eq_zero hunit).mp h0
    exact OreLocalization.numeratorHom_inj (hS.trans inf_le_left)
      (by rw [hx0, OreLocalization.numeratorHom_apply, OreLocalization.zero_oreDiv'])
  · intro x hx
    exact (mem_nonZeroDivisors_iff.mp (hS h)).2 x (by rw [← mul_assoc, hx, zero_mul])

end Work.ORVonNeumann
