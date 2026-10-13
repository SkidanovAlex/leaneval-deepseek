import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotAmgm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotArith
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.cs_sqrt_int
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `b ≤ 4` case of the mismatch coefficient estimate
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

theorem mh_hard_b_le_four : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (b : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → b ≤ 4 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.mixed b 0 f p.1 p.2
          * Work.Spaces.mixed b 1 f p.1 p.2) pm ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.mixed b 0 f p.1 p.2
            * Work.Spaces.mixed b 1 f p.1 p.2 ∂pm|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨Cpw, hCpwpos, hCpw⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨Real.sqrt (10 * Cpw + 1) + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 b hAsm hA4 hAbdd hA4bnd hfsm hf6 hb4
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have hH : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hC0 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f :=
    mul_nonneg (mul_nonneg (mul_nonneg hCpwpos.le (by norm_num))
      (le_of_lt (Real.rpow_pos_of_pos hα0 _))) hH
  -- #### the `A`-slot
  have hXsl := mixed_slot_le (α := α) 4 hAsm hA4 (i := 1) (j := 0) le_rfl (by norm_num)
  have hX4 : Work.Spaces.HkSq α 4 A = (Work.FTS.Nonlin.Xn α A) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 A)]
  have hXint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hXsl.1
  have hXv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
    have h2 : (Work.FTS.Nonlin.Xn α A) ^ 2 ≤ K4 ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd 2
    have h3 : (∫ p, Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.gam α))
        * Work.Spaces.mixed 0 1 A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
      rw [hX4] at hXsl
      linarith [hXsl.2]
    simpa only [Work.FTS.TransportS.leafGam] using h3
  -- #### the top `f`-slot
  have hZsl := mixed_slot_le (α := α) 6 hfsm hf6 (i := 1) (j := b) le_rfl (by omega)
  have hZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.1
  have hZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 f := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.2
  -- #### the remaining `D_z`-factor, pointwise
  have hGnn : ∀ᵐ p ∂pm, 0 ≤ Work.FTS.TransportS.leafGam α p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ _ hθ0 hθ1 => ?_)
    exact Work.FTS.TransportS.leafGam_nonneg α
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
  have hY2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed b 0 f z θ) ^ 2
        ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f := by
    intro z θ hz hθ0 hθ1
    rw [Work.Spaces.mixed_zero_right]
    have h := hCpw α f b 0 hα0 hα1 hfsm hf6 (by omega) z hz θ ⟨hθ0, hθ1⟩
    have hval : Cpw / (Work.Spaces.gam α - 1) = Cpw * 10 * α ^ (-(1 : ℝ)) := by
      rw [Work.Spaces.gam_sub_one, Real.rpow_neg_one]
      field_simp
    rwa [hval] at h
  -- #### integrability and bound of the middle slot
  have hYZmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact (h1.mul ((hfsm.mixed b 0).continuousOn.pow 2)).mul
      ((hfsm.mixed b 1).continuousOn.pow 2)
  have hYZpt : ∀ᵐ p ∂pm, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2
      ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
        * (Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hG : 0 ≤ Work.FTS.TransportS.leafGam α z θ :=
      Work.FTS.TransportS.leafGam_nonneg α hs.le
    have hY := hY2 z θ hz hθ0 hθ1
    have hZ2 : 0 ≤ (Work.Spaces.mixed b 1 f z θ) ^ 2 := sq_nonneg _
    calc Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b 0 f z θ ^ 2
          * Work.Spaces.mixed b 1 f z θ ^ 2
        = (Work.Spaces.mixed b 1 f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * Work.Spaces.mixed b 0 f z θ ^ 2) := by ring
      _ ≤ (Work.Spaces.mixed b 1 f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hG) hZ2
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b 1 f z θ ^ 2) := by ring
  have hYZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' (hZint.const_mul
      (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) hYZmeas ?_
    filter_upwards [hYZpt, hGnn] with p hp hgn
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg hgn (sq_nonneg _)) (sq_nonneg _))]
    exact hp
  have hYZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm)
      ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
    calc (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
          * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm)
        ≤ ∫ p, (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) ∂pm :=
          MeasureTheory.integral_mono_ae hYZint (hZint.const_mul _) hYZpt
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left hZv hC0
      _ ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
          linarith
  -- #### measurability of the full integrand
  have hFmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2
      * Work.Spaces.mixed b 1 f p.1 p.2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact ((h1.mul (hAsm.mixed 0 1).continuousOn).mul
      (hfsm.mixed b 0).continuousOn).mul (hfsm.mixed b 1).continuousOn
  -- #### weighted Cauchy–Schwarz
  have hApos : 0 < K4 ^ 2 + 1 := by nlinarith [sq_nonneg K4]
  have hBpos : 0 < Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1 := by
    have h1 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
        * Work.Spaces.HkSq α 6 f := mul_nonneg hC0 hH
    linarith
  obtain ⟨hFint, hFbnd⟩ := slotAmgm (G := Work.FTS.TransportS.leafGam α)
    (X := fun z θ => Work.Spaces.mixed 0 1 A z θ)
    (Y := fun z θ => Work.Spaces.mixed b 0 f z θ)
    (Z := fun z θ => Work.Spaces.mixed b 1 f z θ)
    (A := K4 ^ 2 + 1)
    (B := Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1)
    hXint hYZint hXv hYZv hApos hBpos hGnn hFmeas
  exact ⟨hFint, hFbnd.trans (slotArith hα0 hα1 hCpwpos hK0 hK4 hH)⟩

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
