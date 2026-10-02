import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The integral of `∂̄` of a compactly supported `C^n` function vanishes (`n ≠ 0`)

For `G : ℂ → ℂ` of class `C^n` with `n ≠ 0` (so in particular `G` is real-differentiable with
continuous Fréchet derivative) and with compact support, the (Lebesgue) integral of the
Wirtinger derivative `∂̄G = ½(∂ₓG + i ∂_yG)` over `ℂ` is zero.

This is the boundary term of Cauchy's theorem in its distributional/`L¹` form.  As in
`Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero` (the `C^∞` case), we use Mathlib's
integration-by-parts for Fréchet derivatives
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) with the test function `1`
(whose derivative vanishes), separately in the two real directions `1` and `I`.  The only
change for general `n ≠ 0` is that the differentiability of `G` and the continuity of
`z ↦ fderiv ℝ G z` are supplied by `ContDiff.differentiable` / `ContDiff.continuous_fderiv`
with the hypothesis `hn : n ≠ 0` rather than for `n = ⊤`.
-/

open MeasureTheory Complex Function

namespace Work.MRMT.Sobolev

/-- Integration by parts against the constant test function `1` shows that the integral of
any directional derivative `v ↦ fderiv ℝ G · v` of a compactly supported `C^n` (`n ≠ 0`)
function `G` is `0`. -/
theorem integral_fderiv_apply_eq_zero_of_contDiff (G : ℂ → ℂ) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n G) (hs : HasCompactSupport G) (v : ℂ) : ∫ z, fderiv ℝ G z v = 0 := by
  have hdiff : Differentiable ℝ G := hc.differentiable hn
  have hcont : Continuous fun z => fderiv ℝ G z v :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hint1 : Integrable (fun z => fderiv ℝ G z v) :=
    hcont.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) v)
  have hintG : Integrable G := hc.continuous.integrable_of_hasCompactSupport hs
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := G) (g := fun _ : ℂ => (1 : ℂ)) (v := v) (by simpa using hint1) (by simp)
    (by simpa using hintG) (fun x _ => hdiff x) (fun x _ => differentiableAt_const 1)
  simpa using h

theorem integral_dzbar_eq_zero_of_contDiff (G : ℂ → ℂ) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n G) (hs : HasCompactSupport G) : ∫ z, Work.MRMT.dzbar G z = 0 := by
  have h1 := integral_fderiv_apply_eq_zero_of_contDiff G hn hc hs 1
  have hI := integral_fderiv_apply_eq_zero_of_contDiff G hn hc hs Complex.I
  have hcont1 : Continuous fun z => fderiv ℝ G z (1 : ℂ) :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hcontI : Continuous fun z => fderiv ℝ G z Complex.I :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hint1 : Integrable (fun z => fderiv ℝ G z (1 : ℂ)) :=
    hcont1.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) (1 : ℂ))
  have hintI : Integrable (fun z => fderiv ℝ G z Complex.I) :=
    hcontI.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) Complex.I)
  have hF : ∫ z, (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I) = 0 := by
    rw [integral_add hint1 (hintI.const_mul Complex.I), integral_const_mul, h1, hI]
    simp
  calc ∫ z, Work.MRMT.dzbar G z
      = ∫ z, (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I) * (2 : ℂ)⁻¹ := by
        simp only [Work.MRMT.dzbar, div_eq_mul_inv]
    _ = (∫ z, (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I)) * (2 : ℂ)⁻¹ :=
        integral_mul_const _ _
    _ = 0 := by rw [hF, zero_mul]

end Work.MRMT.Sobolev
