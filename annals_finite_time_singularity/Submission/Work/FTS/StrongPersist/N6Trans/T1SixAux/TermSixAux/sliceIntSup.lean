import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux

theorem sliceIntSup {α q M : ℝ} (hM : 0 ≤ M)
    {X Y Z h₁ h₂ : ℝ → ℝ → ℝ}
    (hXc : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hYc : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hZc : ContinuousOn (Function.uncurry Z) Work.FTS.EllipticEst.Q0)
    (hm₁ : Work.Spaces.HkMem α 6 h₁) (hm₂ : Work.Spaces.HkMem α 6 h₂)
    (hsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |X z θ| ≤ M)
    (hYd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₁ z θ)
    (hZd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Z z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h₂ z θ) :
    ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.TransportS.SlotT2.canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|) Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · -- `z = 0`: the radial weight vanishes, so the integrand is identically `0`
    subst h0
    rw [show (fun θ : ℝ => Work.FTS.TransportS.SlotT2.canonW q 0 θ * |X 0 θ| * |Y 0 θ| * |Z 0 θ|)
        = fun _ => (0 : ℝ) from by
      funext θ; rw [Work.FTS.TransportS.SlotT2.canonW_zero_z]; ring]
    exact MeasureTheory.integrableOn_zero
  · -- `z > 0`: dominate pointwise (a.e. on `Iθ`) by `M · (HkIntegrand h₁ + HkIntegrand h₂)`
    have hH : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 h₁ z θ
        + Work.Spaces.HkIntegrand α 6 h₂ z θ) Work.Spaces.Iθ :=
      (hm₁.1 z hz).add (hm₂.1 z hz)
    have hdom : MeasureTheory.IntegrableOn (fun θ => M * (Work.Spaces.HkIntegrand α 6 h₁ z θ
        + Work.Spaces.HkIntegrand α 6 h₂ z θ)) Work.Spaces.Iθ := hH.const_mul M
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2
        * |X p.1 p.2| * |Y p.1 p.2| * |Z p.1 p.2|) Work.FTS.EllipticEst.Q0 :=
      (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul hXc.abs).mul hYc.abs).mul hZc.abs
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
    · -- the pointwise bound holds on the *open* angular interval (the endpoints are null,
      -- and there the totalised `rpow` conventions carry no information)
      have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
      rw [hmeas]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hθI : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hc : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
        Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
      have hlhs : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ * |X z θ| * |Y z θ| * |Z z θ| :=
        mul_nonneg (mul_nonneg (mul_nonneg hc (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
      rw [Real.norm_of_nonneg hlhs]
      have hx : |X z θ| ≤ M := hsup z θ hz0 hθ.1 hθ.2
      have hy := hYd z θ hz0 hθ.1 hθ.2
      have hz' := hZd z θ hz0 hθ.1 hθ.2
      have h1 : 0 ≤ Work.Spaces.HkIntegrand α 6 h₁ z θ :=
        Work.Spaces.HkIntegrand_nonneg α 6 h₁ z θ
      have h2 : 0 ≤ Work.Spaces.HkIntegrand α 6 h₂ z θ :=
        Work.Spaces.HkIntegrand_nonneg α 6 h₂ z θ
      -- AM–GM: `2 |Y| |Z| ≤ Y² + Z²`
      have hYZ : 2 * |Y z θ| * |Z z θ| ≤ (Y z θ) ^ 2 + (Z z θ) ^ 2 := by
        have h := sq_nonneg (|Y z θ| - |Z z θ|)
        rw [sub_sq, sq_abs, sq_abs] at h
        linarith [h]
      have hmul1 : 2 * (Work.FTS.TransportS.SlotT2.canonW q z θ * |Y z θ| * |Z z θ|)
          ≤ Work.Spaces.HkIntegrand α 6 h₁ z θ + Work.Spaces.HkIntegrand α 6 h₂ z θ := by
        have h := mul_le_mul_of_nonneg_left hYZ hc
        nlinarith [h, hy, hz']
      have hstep2 : Work.FTS.TransportS.SlotT2.canonW q z θ * |X z θ| * |Y z θ| * |Z z θ|
          ≤ M * (Work.FTS.TransportS.SlotT2.canonW q z θ * |Y z θ| * |Z z θ|) := by
        have habs : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ * |Y z θ| * |Z z θ| :=
          mul_nonneg (mul_nonneg hc (abs_nonneg _)) (abs_nonneg _)
        have h := mul_le_mul_of_nonneg_right hx habs
        nlinarith [h]
      have hstep3 : M * (Work.FTS.TransportS.SlotT2.canonW q z θ * |Y z θ| * |Z z θ|)
          ≤ M * (Work.Spaces.HkIntegrand α 6 h₁ z θ + Work.Spaces.HkIntegrand α 6 h₂ z θ) := by
        nlinarith [hmul1, hM, h1, h2]
      linarith [hstep2, hstep3]

end Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux
