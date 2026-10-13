import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open MeasureTheory Set Filter
open scoped Real Topology

/-- For `z > 0` the squared radial weight `w(z)²` does not vanish, so that the weighted
summands of the `ℋ^k`-integrand (which carry a factor `w(z)²` relative to the honest
`η`- resp. `γ`-weighted squares) can be un-weighted by multiplying with its inverse. -/
private theorem w_sq_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : (Work.Spaces.w z) ^ 2 ≠ 0 := by
  rw [Work.Spaces.w]
  exact pow_ne_zero 2
    (div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz)))

theorem hkMem_slots (α : ℝ) (k : ℕ) {Φ : ℝ → ℝ → ℝ}
    (hSO : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pth Φ))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) (hα : 0 < α) :
    (∀ i : ℕ, i ≤ k → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ)
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ k → MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) Work.Spaces.Iθ) := by
  have hf : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Φ) := hSO.pth
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := w_sq_ne_zero_of_pos hzpos
  -- un-weighting by the nonvanishing constant `(w z)²`
  have hstrip : ∀ (u : ℝ → ℝ),
      IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 * u θ) Work.Spaces.Iθ →
      IntegrableOn u Work.Spaces.Iθ := by
    intro u hu
    refine MeasureTheory.IntegrableOn.congr_fun (hu.const_mul (((Work.Spaces.w z) ^ 2)⁻¹))
      (fun θ _ => ?_) hmeasIθ
    rw [← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
  constructor
  · intro i hi
    -- `(D_z^i ∂_θΦ · w/sin^{η/2})²` is `θ`-integrable by the open-quadrant `ℋ^k`-membership
    have h1 : IntegrableOn (fun θ => (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableOn_zSummand α k hf hmem i hi hz
    -- which is `w(z)²` times the `η`-weighted square of `D_z^i ∂_θΦ`
    have h2 : IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
      MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ =>
        Work.FTS.EllipticEst.rad_term_eq hθ z (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ))
        hmeasIθ
    simpa only [Work.FTS.EllipticEst.sEta] using
      hstrip (fun θ => (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) h2
  · intro i j hi hij
    -- the mixed summand `(D_z^j D_θ^i ∂_θΦ · Wt)²` is `θ`-integrable as well
    have h1 : IntegrableOn (fun θ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ
        * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableOn_mixedSummand α k hf hmem i j hi hij hz
    -- and it is `w(z)²` times the `γ`-weighted square of the mixed derivative
    have h2 : IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ) ^ 2
          * Work.FTS.EllipticEst.sGam α θ)) Work.Spaces.Iθ :=
      MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => Work.FTS.EllipticEst.mix_term_eq hθ α z
        (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ)) hmeasIθ
    simpa only [Work.FTS.EllipticEst.sGam] using
      hstrip (fun θ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ) ^ 2
        * Work.FTS.EllipticEst.sGam α θ) h2

end Work.FTS.EllSol
