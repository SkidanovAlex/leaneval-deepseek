import Mathlib
import Submission.Work.EKLC6Core.thin_boundary_ae

namespace Work.EKLC6Route

open MeasureTheory

/-- **A good radius exists in any interval.**

For a monotone `F : ℝ → ℝ` which is bounded above by `M` and nonnegative, and any `a < b`,
there is a point `r ∈ (a,b)` at which the *symmetric increment* `F (r + η) - F (r - η)` grows
at most linearly in `η`, i.e. there is `c ≥ 0` with `F (r + η) - F (r - η) ≤ c η` for **all**
`η > 0`.

This is the "there exists" form of `Work.EKLC6Core.monotone_global_bound_ae`, which states the
property for Lebesgue-almost every `r`.  Since `(a,b)` has positive Lebesgue measure it cannot
be contained in the null set of exceptional radii. -/
theorem exists_good_radius {F : ℝ → ℝ} (hmono : Monotone F) {M a b : ℝ}
    (hM : ∀ s, F s ≤ M) (h0 : ∀ s, 0 ≤ F s) (hab : a < b) :
    ∃ r ∈ Set.Ioo a b, ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ, 0 < η → F (r + η) - F (r - η) ≤ c * η := by
  -- Almost every point of `ℝ` is a "good radius".
  have hae : ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ, 0 < η → F (r + η) - F (r - η) ≤ c * η :=
    Work.EKLC6Core.monotone_global_bound_ae hmono h0 hM
  -- Hence the set of bad radii is null.
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      {r | ¬ (∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ, 0 < η → F (r + η) - F (r - η) ≤ c * η)} = 0 :=
    MeasureTheory.ae_iff.mp hae
  -- Suppose no good radius lies in `(a,b)`.  Then `(a,b)` is contained in the null set of bad
  -- radii, contradicting the positivity of its measure.
  by_contra hcon
  rw [not_exists] at hcon
  have hsub : Set.Ioo a b ⊆
      {r | ¬ (∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ, 0 < η → F (r + η) - F (r - η) ≤ c * η)} := by
    intro r hr hP
    exact hcon r ⟨hr, hP⟩
  have hle : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Ioo a b) ≤ 0 :=
    le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hnull)
  have hpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact absurd hpos (not_lt.mpr hle)

end Work.EKLC6Route
