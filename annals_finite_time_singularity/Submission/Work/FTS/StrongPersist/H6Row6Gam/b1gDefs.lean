import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xSliceAgmon5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
/-! ## Definitions of the `b1fiveGamRowDz` integrand and slice functionals -/

/-- The `z`-slice functional of the `γ`-weighted slot `D_zD_θf`. -/
noncomputable def b1gPz (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    * (Work.Spaces.mixed 1 1 f z θ) ^ 2

/-- The integrand of `b1fiveGamRowDz`. -/
noncomputable def b1gF (α : ℝ) (A f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p =>
  Work.FTS.TransportS.leafGam α p.1 p.2
    * Work.Spaces.mixed 5 0 A p.1 p.2
    * Work.Spaces.mixed 1 1 f p.1 p.2
    * Work.Spaces.mixed 5 1 f p.1 p.2

theorem b1gF_apply (α : ℝ) (A f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    b1gF α A f p = Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 5 0 A p.1 p.2
      * Work.Spaces.mixed 1 1 f p.1 p.2
      * Work.Spaces.mixed 5 1 f p.1 p.2 := rfl

theorem b1gPz_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    b1gPz α f z = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 1 1 f z θ) ^ 2 := rfl

/-- Continuity of `σ^{-γ}·|mixed 1 1 f|·|mixed 5 1 f|` on the open quadrant. -/
theorem contOn_sig_abs11 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2|))
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.mixed 1 1 f p.1 p.2|)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (h.mixed 1 1)).abs
  have h2 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.mixed 5 1 f p.1 p.2|)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (h.mixed 5 1)).abs
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
      Work.FTS.EllipticEst.Q0 := by
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    refine h3.rpow_const (fun p hp => Or.inl ?_)
    exact ne_of_gt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_pos_of_Ioo
      ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp).2.1, (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2⟩)
  exact hs.mul (h1.mul h2)

/-! ## Slice integrability of the `b1gF` integrand -/

theorem b1gSliceInt : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f →
    ∀ z : ℝ, 0 < z →
      MeasureTheory.Integrable (fun θ => |b1gF α A f (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro α A f hα0 hα1 hA hf h6A h6f z hz
  have hWint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 1) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hZint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 5) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hg : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
      * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 1 1 f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((hWint.add hZint)).div_const 2).const_mul _
  refine MeasureTheory.Integrable.mono' hg ?_ ?_
  · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => |b1gF α A f p|) ?_ hz
    simp only [b1gF_apply]
    exact ((((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hA.mixed 5 0))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hf.mixed 1 1))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hf.mixed 5 1))).abs
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _
    have hcoefnn : 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
      rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
      refine add_nonneg (mul_nonneg (by positivity)
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
        (mul_nonneg (div_nonneg (by norm_num) (by
            rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.hgam_const]; linarith))
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc
            (fun θ hθ => mul_nonneg
              (Real.rpow_nonneg
                (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _)
              (sq_nonneg _))))
    have hX2 : |Work.Spaces.DzIter 5 A z θ|
        ≤ Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) := by
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
      exact Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xSliceAgmon5 α A hα0 hα1 hA h6A
        z θ hz hθ0 hθ1
    have habsF : |b1gF α A f (z, θ)| = (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      simp only [b1gF_apply, Work.FTS.TransportS.leafGam, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
      ring
    rw [Real.norm_of_nonneg (abs_nonneg _), habsF]
    have hAM : |Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|
        ≤ ((Work.Spaces.mixed 1 1 f z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|Work.Spaces.mixed 1 1 f z θ| - |Work.Spaces.mixed 5 1 f z θ|),
        sq_abs (Work.Spaces.mixed 1 1 f z θ), sq_abs (Work.Spaces.mixed 5 1 f z θ)]
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.DzIter 5 A z θ|
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
            * (((Work.Spaces.mixed 1 1 f z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ) ^ 2)
              / 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hσnn)
            exact mul_le_mul hX2 hAM (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (Real.sqrt_nonneg _)
      _ = (Work.Spaces.w z) ^ 2
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
          * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 f z θ) ^ 2
            + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2) := by
            ring
end

end Work.FTS.StrongPersist.H6Row6
