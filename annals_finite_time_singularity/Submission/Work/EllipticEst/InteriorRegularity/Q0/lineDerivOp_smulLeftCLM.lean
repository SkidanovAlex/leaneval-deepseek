/-
The Leibniz rule (product rule) for the directional derivative `∂_m` on tempered distributions:

  `∂_m (g · u) = g · ∂_m u + (∂_m g) · u`,

for a multiplier `g` of temperate growth (hence smooth) and any tempered distribution `u`.

At the level of test functions this is the classical identity
`⟨∂_m (g u), φ⟩ = ⟨u, -∂_m (g φ) + (∂_m g) φ⟩`
together with the *pointwise* Leibniz rule `∂_m (g φ) = g · ∂_m φ + (∂_m g) · φ` for the product
of the smooth function `g` with the Schwartz function `φ`.
-/
import Mathlib.Analysis.Distribution.TemperedDistribution
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.EllipticEst.InteriorRegularity.Q0

open scoped SchwartzMap Topology
open MeasureTheory Set Filter

/-- The pointwise Leibniz rule for the line derivative, for two complex-valued functions that are
differentiable at the point in question. -/
theorem lineDeriv_mul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f k : E → ℂ} {x m : E} (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x) :
    lineDeriv ℝ (fun y => f y * k y) x m = f x * lineDeriv ℝ k x m + lineDeriv ℝ f x m * k x := by
  have hmul : DifferentiableAt ℝ (fun y => f y * k y) x := hf.mul hk
  rw [hf.lineDeriv_eq_fderiv, hk.lineDeriv_eq_fderiv, hmul.lineDeriv_eq_fderiv,
    fderiv_fun_mul hf hk]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The Leibniz rule for the line derivative on Schwartz functions: multiplying by a function of
temperate growth and differentiating is the same as differentiating and then multiplying, plus the
term where the derivative hits the multiplier. -/
theorem schwartz_smulLeftCLM_lineDerivOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} (hg : Function.HasTemperateGrowth g) (m : E)
    (hg' : (fun x : E => lineDeriv ℝ g x m).HasTemperateGrowth) (φ : SchwartzMap E ℂ) :
    LineDeriv.lineDerivOp m ((SchwartzMap.smulLeftCLM ℂ g) φ)
      = (SchwartzMap.smulLeftCLM ℂ g) (LineDeriv.lineDerivOp m φ)
        + (SchwartzMap.smulLeftCLM ℂ (fun x : E => lineDeriv ℝ g x m)) φ := by
  apply SchwartzMap.ext
  intro x
  have hcoe : (⇑((SchwartzMap.smulLeftCLM ℂ g) φ) : E → ℂ) = fun y => g y * φ y := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  rw [add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.smulLeftCLM_apply_apply hg', SchwartzMap.lineDerivOp_apply, hcoe,
    lineDeriv_mul_eq ((hg.1.differentiable (by simp)).differentiableAt) φ.differentiableAt,
    SchwartzMap.lineDerivOp_apply]
  simp only [smul_eq_mul]

theorem lineDerivOp_smulLeftCLM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {g : E → ℂ} (hg : Function.HasTemperateGrowth g) (m : E)
    (hg' : (fun x : E => lineDeriv ℝ g x m).HasTemperateGrowth)
    (u : TemperedDistribution E ℂ) :
    LineDeriv.lineDerivOp m (TemperedDistribution.smulLeftCLM ℂ g u)
      = TemperedDistribution.smulLeftCLM ℂ g (LineDeriv.lineDerivOp m u)
        + TemperedDistribution.smulLeftCLM ℂ (fun x : E => lineDeriv ℝ g x m) u := by
  ext φ
  rw [add_apply, TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.lineDerivOp_apply_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    ← map_add]
  congr 1
  rw [map_neg, schwartz_smulLeftCLM_lineDerivOp hg m hg' φ]
  abel

end Work.EllipticEst.InteriorRegularity.Q0
