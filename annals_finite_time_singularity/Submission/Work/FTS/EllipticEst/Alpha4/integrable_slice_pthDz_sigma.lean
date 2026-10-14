import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.InterpTruncDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-! ## The basic objects -/

/-- The half-strip `(0,∞) × (-1, π/2+1)` on which the data are `C^∞`. -/
abbrev strip : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)


/-- The logarithmic cut-off `ζ_k = zc φ k` of the workspace, as a function of `z` alone. -/
abbrev zeta (φ : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := Work.FTS.EllipticEst.Alpha4.zc φ k

/-- The truncated function `ζ_k · G`. -/
def cut (φ : ℝ → ℝ) (k : ℕ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => zeta φ k z * G z θ



/-- The weighted angular slice integral `∫_θ (F z θ)² σ θ`, `σ = sin(2θ)^{-η}`. -/
def inn (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ

/-- The `z`-integrand `w(z)² ∫_θ (F z θ)² σ θ` of the four functionals. -/
def sl (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * inn F z

/-! ## The four functionals as integrals of the slice functions -/







/-! ## Nonnegativity of the slice integrals -/







/-! ## Support and value facts for `ζ_k` -/








theorem smoothOrder_ne_zero : Work.FTS.EllipticEst.smoothOrder ≠ 0 := by
  simp [Work.FTS.EllipticEst.smoothOrder]

theorem one_le_smoothOrder : (1 : WithTop ℕ∞) ≤ Work.FTS.EllipticEst.smoothOrder := by
  simp [Work.FTS.EllipticEst.smoothOrder]








/-! ## The Leibniz rules for `ζ_k · G` -/






end Work.Blocks.InterpTrunc
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

/-! ## Slice integrability of `(D_z^j ∂_θ^i G)² · σ`

The angular weight `thEta θ = sin(2θ)^{-η}` is integrable on the closed angular interval
`Iθ = [0,π/2]`, and the `θ`-slice of `D_z^j ∂_θ^i G` at a *fixed* `z > 0` is continuous
on the compact set `Iθ`, hence the slice is bounded and its square is dominated by a
constant multiple of the integrable weight.

The only technical point is that `θ ↦ (F z θ)² · thEta θ` is not *continuous* on
`Iθ` (the weight blows up at the endpoints), so almost-everywhere strong measurability is
obtained on the co-null open sub-interval `(0,π/2)`. -/


/-- The angular weight `thEta` is continuous on the *open* interval `(0,π/2)`
(where `sin(2θ) > 0`, so the `rpow` branch is continuous). -/
theorem continuousOn_thEta_Ioo :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have h := hsin.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
  simpa only [Work.FTS.EllipticEst.thEta] using h



end Work.FTS.EllipticEst.Alpha4
end
end
