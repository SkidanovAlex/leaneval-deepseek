import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology in
theorem iteratedFDeriv_two_apply_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x a b : E} (c : ℝ) (hf : DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (fderiv ℝ f) x) :
    (iteratedFDeriv ℝ 2 (fun z => c * f z) x) ![a, b]
      = c * (iteratedFDeriv ℝ 2 f x) ![a, b] := by
  -- The second iterated derivative is the second derivative as a bilinear map.
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  -- Differentiating the scaled function: `fderiv (c • f) = c • fderiv f`.
  have h1 : fderiv ℝ (fun z : E => c * f z) = c • fderiv ℝ f := by
    rw [show (fun z : E => c * f z) = c • f from by ext z; simp [smul_eq_mul]]
    exact fderiv_const_smul_field c
  rw [h1]
  -- Differentiating the scaled derivative again.
  have h2 : fderiv ℝ (c • fderiv ℝ f) = c • fderiv ℝ (fderiv ℝ f) :=
    fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ f) c
  rw [h2]
  simp [smul_eq_mul]

end Commons.Analysis.Calculus.FDeriv