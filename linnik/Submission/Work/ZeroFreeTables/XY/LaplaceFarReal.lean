import Mathlib
import Submission.Commons.NumberTheory.Linnik.laplace_far_le
import Submission.Commons.Analysis.Calculus.iteratedDeriv_pow_mul_le_of_bump

/-!
# `LaplaceFarReal` — the Laplace-transform far bound for a *real*-valued test function

Heath-Brown's §6 argument controls the Laplace transform
`∫₀^{x₀} e^{-(a+iη)t} f t dt` of a real test function `f` that is `C²` on `(0,x₀)`,
vanishes for `t ≥ x₀`, and satisfies `‖f''‖ ≤ B` there.  The quantitative bound
(Heath-Brown (6.14)) is

`‖∫₀^{x₀} e^{-(a+iη)t} f t dt‖
    ≤ ‖f 0‖ / (δ/2 · L) + (2‖f'(0⁺)‖ + 2B x₀) e^{x₀ M} / (δ/2 · L)²`

whenever `|a| ≤ M` and `δ/2 · L ≤ |η|`.

The complex-valued version `Commons.NumberTheory.Linnik.laplace_far_le` already holds the
analytic content (its proof rests on the two-sided integration-by-parts estimate
`laplace_bound_two_sided`).  The only work here is to transport the *real* smoothness and
`C²`-bound hypotheses to the complexification `t ↦ ((f t : ℝ) : ℂ)`, which is what
`iteratedDeriv_ofReal` / `norm_iteratedDeriv_ofReal` (from
`Commons.Analysis.Calculus.iteratedDeriv_pow_mul_le_of_bump`) and
`Complex.ofRealCLM.contDiff` provide.
-/

namespace Work.ZeroFreeTables.XY

open MeasureTheory

theorem LaplaceFarReal {x₀ B M δ L : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hδ : 0 < δ) (hL : 0 < L)
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    {a η : ℝ} (ha : |a| ≤ M) (hη : δ / 2 * L ≤ |η|) :
    ‖∫ t in (0:ℝ)..x₀, Complex.exp (-((((a : ℂ) + (η : ℂ) * Complex.I)) * (t : ℂ))) * ((f t : ℝ) : ℂ)‖
      ≤ ‖f 0‖ / (δ / 2 * L) + (2 * ‖derivWithin (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M) / (δ / 2 * L) ^ 2 := by
  -- Continuity of the complexification on `[0, x₀]`.
  have hcont' : ContinuousOn (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Icc 0 x₀) :=
    Complex.continuous_ofReal.comp_continuousOn (hcont.mono Set.Icc_subset_Ici_self)
  -- `C²`-ness transports to the complexification.
  have hf2' : ContDiffOn ℝ 2 (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Ioo 0 x₀) := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn hf2
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  -- The `C²`-bound transports to the complexification.
  have hBnd' : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 (fun t : ℝ => ((f t : ℝ) : ℂ)) t‖ ≤ B := by
    intro t ht
    rw [Commons.Analysis.Calculus.norm_iteratedDeriv_ofReal 2 f t
      (hf2.contDiffAt (Ioo_mem_nhds ht.1 ht.2))]
    exact hBnd t ht
  -- The vanishing hypothesis transports to the complexification.
  have hvan' : ∀ t : ℝ, x₀ ≤ t → (fun t : ℝ => ((f t : ℝ) : ℂ)) t = 0 := by
    intro t ht; simp [hsupp t ht]
  have hmain := Commons.NumberTheory.Linnik.laplace_far_le hx₀ hB hδ hL hcont' hf2' hBnd' hvan' ha hη
  simpa [RCLike.norm_ofReal] using hmain

end Work.ZeroFreeTables.XY
