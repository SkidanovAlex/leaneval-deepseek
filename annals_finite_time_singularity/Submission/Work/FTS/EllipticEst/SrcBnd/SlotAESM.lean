import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SrcBnd

open MeasureTheory Set

/-- The radius weight `w z = (1+z)²/z²` is continuous on the open quadrant: it is a rational
function whose denominator does not vanish there. -/
theorem continuousOn_w_fst_Q0 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
    Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- Iterated `∂_θ` preserves `C^∞`-smoothness on the open quadrant. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (n : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n f) := by
  induction n with
  | zero => simpa using hF
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

theorem SlotAESM (n : ℕ) {σ : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hσc : ContinuousOn (fun p : ℝ × ℝ => σ p.2) Work.FTS.EllipticEst.Q0) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- The uncurried integrand of both conjuncts is continuous on the open quadrant.
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_w_fst_Q0.pow 2).mul
      (((smoothOpen_pthIter hf n).continuousOn.pow 2).mul hσc)
  constructor
  · -- Angular slices: for `z > 0` this is a.e. strong measurability of a continuous slice, and
    -- at `z = 0` the whole integrand vanishes because `w 0 = 0`.
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz0 with h0 | hpos
    · subst h0
      have hzero : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 *
          ((Work.Spaces.pthIter n f 0 θ) ^ 2 * σ θ)) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.w]
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ =>
          (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
        hcont hpos
  · -- The `z`-integral of the joint integrand is a.e. strongly measurable for the product
    -- measure `(volume.restrict Iz) ⊗ (volume.restrict Iθ)`, hence a.e. strongly measurable
    -- for the first factor alone (the Bochner integral needs no integrability for this).
    exact (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
      hcont).integral_prod_right'

end Work.FTS.EllipticEst.SrcBnd
