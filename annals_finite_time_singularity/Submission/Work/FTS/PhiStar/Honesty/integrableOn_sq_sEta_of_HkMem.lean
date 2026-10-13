import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Per-slice honesty of the `η`-weighted slice mass, from `HkMem α 0 F`

For `F` in `H^0` (weighted `L²`-membership, `Work.Spaces.HkMem α 0 F`) and every `z > 0`, the
slice mass `θ ↦ F z θ ^ 2 · sin(2θ)^{-η}` is integrable on `Iθ`.

This is exactly the per-slice integrability that `Honesty/cmode_sq_le_slice` consumes as its
hypothesis `hint`.  The point is the `k = 0` collapse of the `H^k` integrand,

  `HkIntegrand α 0 F z θ = (F z θ * w z / sin(2θ)^{η/2})²`  (`simp`), and on `Iθ` this is
  `w₂ z · F z θ ^ 2 · σ θ`  with `w₂ z = w z ^ 2`, `σ θ = sin(2θ)^{-η}` (`AngSecond.sq_mul_W`),

so on each slice the target integrand is the constant `(w₂ z)^{-1}` times the slice integrand of
`HkMem`, which is integrable by hypothesis.  The case `z = 0` is genuinely unavailable: `w 0 = 0`
and `HkMem` constrains nothing at `z = 0`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

/-- The `k = 0` collapse of the `H^k` integrand: for `k = 0` the sum of squares reduces to the
single `D_z^0`-term `(f · w / sin(2θ)^{η/2})²`. -/
private lemma HkIntegrand_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem integrableOn_sq_sEta_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hw0 : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
    have hwz : Work.Spaces.w z ≠ 0 :=
      div_ne_zero (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0)) (pow_ne_zero 2 hz0)
    simpa [Work.FTS.EllipticEst.AngSecond.w2] using pow_ne_zero 2 hwz
  -- on `Iθ`, the target integrand is `(w₂ z)^{-1}` times the slice integrand of `HkMem`
  have hEq : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.AngSecond.w2 z)⁻¹ * Work.Spaces.HkIntegrand α 0 F z θ
        = (F z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    intro θ hθ
    rw [HkIntegrand_zero α F z θ, Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ]
    field_simp
  exact MeasureTheory.IntegrableOn.congr_fun
    ((hF.1 z (le_of_lt hz)).const_mul ((Work.FTS.EllipticEst.AngSecond.w2 z)⁻¹))
    hEq measurableSet_Icc

end Work.FTS.PhiStar.Honesty
