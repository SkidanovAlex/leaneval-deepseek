import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- Every element of `Mid E` is the square root of the product of the two witnessing elements of
`E`; consequently `Mid E` is contained in the image of `E × E` under `(ρ₁, ρ₂) ↦ √(ρ₁ * ρ₂)`. -/
private lemma mid_subset_sqrt_image (E : Set ℝ) :
    Mid E ⊆ (fun p : ℝ × ℝ => Real.sqrt (p.1 * p.2)) '' (E ×ˢ E) := by
  rintro x ⟨ρ₁, h₁, ρ₂, h₂, hρ₁pos, hlt, -, hx, hxpos⟩
  refine ⟨(ρ₁, ρ₂), Set.mem_prod.mpr ⟨h₁, h₂⟩, ?_⟩
  rw [Real.sqrt_eq_iff_eq_sq (mul_nonneg (le_of_lt hρ₁pos) (le_of_lt (lt_trans hρ₁pos hlt)))
      (le_of_lt hxpos), pow_two]
  exact hx.symm

theorem Mid_finite (E : Set ℝ) (hE : E.Finite) : (Work.WilC4.Mid E).Finite :=
  Set.Finite.subset ((hE.prod hE).image (fun p : ℝ × ℝ => Real.sqrt (p.1 * p.2)))
    (mid_subset_sqrt_image E)

end Work.WilC4
