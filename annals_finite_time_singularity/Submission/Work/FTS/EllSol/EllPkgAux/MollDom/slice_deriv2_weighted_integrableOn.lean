import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem slice_deriv2_weighted_integrableOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv (fun s' : ℝ => G w s')) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  obtain ⟨-, -, -, -, -, -, -, hhon⟩ := hT
  -- the angular `∂_θ²`-weight `sin(2θ)^{-η}` carried by the slice at radius `w` is the one
  -- already controlled by `SliceHonestOpen G` (the last conjunct of `TraceClass`), up to the
  -- constant factor `w(w)²` coming from the `z`-weight of `SliceHonestOpen`
  have hc : (0 : ℝ) < (Work.Spaces.w w) ^ 2 := by
    rw [Work.Spaces.w]; positivity
  have h0' := hhon.1 w hw
  have hEq : ∀ θ : ℝ, ((Work.Spaces.w w) ^ 2)⁻¹ *
      (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      = Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    intro θ
    rw [show Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ
        = (Work.Spaces.w w) ^ 2 * (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) from by ring]
    exact inv_mul_cancel_left₀ (ne_of_gt hc) _
  have hfun : (fun θ : ℝ => (deriv (deriv (fun s' : ℝ => G w s')) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      = fun θ : ℝ => ((Work.Spaces.w w) ^ 2)⁻¹ *
        (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    funext θ
    rw [hEq θ]
    rfl
  rw [hfun]
  exact h0'.const_mul _

end Work.FTS.EllSol.EllPkgAux.MollDom
