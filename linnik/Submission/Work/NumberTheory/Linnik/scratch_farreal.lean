import Mathlib
import Submission.Commons.NumberTheory.Linnik.laplace_far_le

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- The published `laplace_far_le`, transported to a **real-valued** `f` (the case used in
Heath-Brown §6).  The smoothness and the second-derivative bound are imposed on the complexified
function `t ↦ ((f t : ℝ) : ℂ)`; this is the only place where the complexification of a real test
function is needed in the §6 lane. -/
theorem laplace_far_le_real {x₀ B M δ L : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hL : 0 < L) {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀,
      ‖iteratedDeriv 2 (fun t : ℝ => ((f t : ℝ) : ℂ)) t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {a η : ℝ} (ha : |a| ≤ M) (hη : δ / 2 * L ≤ |η|) :
    ‖∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((a : ℂ) + (η : ℂ) * Complex.I)) * (t : ℂ))) * ((f t : ℝ) : ℂ)‖
      ≤ ‖((f 0 : ℝ) : ℂ)‖ / (δ / 2 * L)
        + (2 * ‖derivWithin (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Ioi 0) 0‖ + 2 * B * x₀)
            * Real.exp (x₀ * M) / (δ / 2 * L) ^ 2 := by
  refine laplace_far_le hx₀ hB hδ hL ?_ hf2 hBnd ?_ ha hη
  · exact Complex.continuous_ofReal.comp_continuousOn hcont
  · intro t ht
    rw [hvan t ht]
    rfl

end Commons.NumberTheory.Linnik
