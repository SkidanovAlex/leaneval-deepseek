import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotAmgm
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `a = a₁` case of the mismatch coefficient estimate

`theorem mismatchCaseGe`: the pairing

  `∫ leafGam α · D_z^{b₁}D_θ^{a₁}A · D_z^{b-b₁}D_θ^{a-a₁}f · D_z^bD_θ^af`

with `a = a₁`, `1 ≤ a₁`, `a₁ + b₁ ≤ 2` and `¬(a₁ = 1 ∧ b₁ = 0)` is bounded by
`C α^{-3} (1 + K₀ + K₄)(1 + |f|_{ℋ⁶})`, where the two slots `D_z^{b₁}D_θ^{a₁}A`
(`A` elliptic datum, controlled by `K₀` and `K₄ = Xn α A`) and `D_z^b D_θ^af` are
estimated by the weighted `L²` slots of the norms `ℋ⁴(A)` and `ℋ⁶(f)`, the remaining
`D_z^{b-b₁}f` factor by the pointwise Agmon bound `PwAny6` of the level-six norm, and
the product assembled by weighted Cauchy–Schwarz (`slotAmgm`).

The only auxiliary index fact is `a = a₁` together with `¬(a₁ = 1 ∧ b₁ = 0)`, which
forces `b - b₁ ≤ 4` so that `PwAny6` applies to `D_z^{b-b₁}f`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

/-- The elementary `α`-arithmetic closing the two factors produced by the weighted
Cauchy–Schwarz: `√(K₄²+1) ≤ K₄+1`, `α^{-1} ≤ α^{-6}`, `HkSq² ≤ (1+HkSq)²` and
`1 ≤ α^{-6}(1+HkSq)²` combine into the stated `α^{-3}`-bound. -/
private lemma slotArithBound {α Cpw K0 K4 HkSq : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hCpw : 0 < Cpw) (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hH : 0 ≤ HkSq) :
    Real.sqrt (K4 ^ 2 + 1) * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)) := by
  have h1 : Real.sqrt (K4 ^ 2 + 1) ≤ K4 + 1 := sqrt_sq_add_one_le hK4
  have hE1 : α ^ (-(1 : ℝ)) ≤ α ^ (-(6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hE2 : (1 : ℝ) ≤ α ^ (-(6 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(6 : ℝ)) ≤ 0 by norm_num)
    simpa using h
  have h6nn : 0 ≤ α ^ (-(6 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hrpow : (α ^ (-(3 : ℝ))) ^ 2 = α ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hα0.le]
    norm_num
  have hB2 : (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) ^ 2
      = (10 * Cpw + 1) * α ^ (-(6 : ℝ)) * (1 + HkSq) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hrpow]
  have hE3 : Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1
      ≤ (10 * Cpw + 1) * α ^ (-(6 : ℝ)) * (1 + HkSq) ^ 2 := by
    have hc : (0 : ℝ) ≤ Cpw * 10 := by positivity
    have hHH : HkSq * HkSq ≤ (1 + HkSq) * (1 + HkSq) := by nlinarith
    have hA : α ^ (-(1 : ℝ)) * (HkSq * HkSq)
        ≤ α ^ (-(6 : ℝ)) * ((1 + HkSq) * (1 + HkSq)) :=
      mul_le_mul hE1 hHH (by positivity) h6nn
    have hA' : Cpw * 10 * (α ^ (-(1 : ℝ)) * (HkSq * HkSq))
        ≤ Cpw * 10 * (α ^ (-(6 : ℝ)) * ((1 + HkSq) * (1 + HkSq))) :=
      mul_le_mul_of_nonneg_left hA hc
    have hP1 : (1 : ℝ) ≤ (1 + HkSq) * (1 + HkSq) := by nlinarith
    have hB : (1 : ℝ) ≤ α ^ (-(6 : ℝ)) * ((1 + HkSq) * (1 + HkSq)) := by
      have h := mul_le_mul hE2 hP1 zero_le_one h6nn
      simpa using h
    nlinarith [hA', hB, hc, h6nn, sq_nonneg HkSq]
  have h2 : Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq) := by
    have hB : 0 ≤ Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq) := by positivity
    have hE3' : Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1
        ≤ (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) ^ 2 := by
      rw [hB2]; exact hE3
    have h3 := Real.sqrt_le_sqrt hE3'
    rwa [Real.sqrt_sq hB] at h3
  have h4 : Real.sqrt (K4 ^ 2 + 1) * Real.sqrt (Cpw * 10 * α ^ (-(1 : ℝ)) * HkSq * HkSq + 1)
      ≤ (K4 + 1) * (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) :=
    mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by linarith)
  refine h4.trans ?_
  have hK : K4 + 1 ≤ 1 + K0 + K4 := by linarith
  have hKnn : 0 ≤ 1 + K0 + K4 := by linarith
  have hP : 0 ≤ 1 + HkSq := by linarith
  have hα3 : 0 ≤ α ^ (-(3 : ℝ)) := (Real.rpow_pos_of_pos hα0 _).le
  have hS : Real.sqrt (10 * Cpw + 1) ≤ Real.sqrt (10 * Cpw + 1) + 1 := by
    linarith [Real.sqrt_nonneg (10 * Cpw + 1)]
  calc (K4 + 1) * (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq))
      ≤ (1 + K0 + K4) * (Real.sqrt (10 * Cpw + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) :=
        mul_le_mul_of_nonneg_right hK (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hα3) hP)
    _ ≤ (1 + K0 + K4) * ((Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * (1 + HkSq)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hα3) hP) hKnn
    _ = (Real.sqrt (10 * Cpw + 1) + 1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + HkSq)) := by
        ring

theorem mismatchCaseGe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 →
      a = a₁ → ¬ (a₁ = 1 ∧ b₁ = 0) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨Cpw, hCpwpos, hCpw⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨Real.sqrt (10 * Cpw + 1) + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab haeq hnot
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have h6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hfsm 6 (by norm_num) hf7
  have hH : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hC0 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f :=
    mul_nonneg (mul_nonneg (mul_nonneg hCpwpos.le (by norm_num))
      (le_of_lt (Real.rpow_pos_of_pos hα0 _))) hH
  -- the index reductions: `a = a₁` and `b - b₁ ≤ 4`
  have hsub : a - a₁ = 0 := by omega
  have hc4 : b - b₁ ≤ 4 := by
    have hb1 : b₁ ≤ 1 := by omega
    rcases (show a₁ ≠ 1 ∨ b₁ ≠ 0 from by tauto) with h | h
    · have ha2 : a₁ = 2 := by omega
      omega
    · have hb1' : b₁ = 1 := by omega
      omega
  -- #### the `A`-slot
  have hXsl := mixed_slot_le (α := α) 4 hAsm hA4 (i := a₁) (j := b₁) ha₁ (by omega)
  have hX4 : Work.Spaces.HkSq α 4 A = (Work.FTS.Nonlin.Xn α A) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 A)]
  have hXint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hXsl.1
  have hXv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
    have h2 : (Work.FTS.Nonlin.Xn α A) ^ 2 ≤ K4 ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd 2
    have h3 : (∫ p, Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.gam α))
        * Work.Spaces.mixed b₁ a₁ A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
      rw [hX4] at hXsl
      linarith [hXsl.2]
    simpa only [Work.FTS.TransportS.leafGam] using h3
  -- #### the top `f`-slot
  have hZsl := mixed_slot_le (α := α) 6 hfsm h6 (i := a) (j := b) (by omega) (by omega)
  have hZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.1
  have hZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 f := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.2
  -- #### the remaining `D_z`-factor, pointwise
  have hGnn : ∀ᵐ p ∂pm, 0 ≤ Work.FTS.TransportS.leafGam α p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ _ hθ0 hθ1 => ?_)
    exact Work.FTS.TransportS.leafGam_nonneg α
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
  have hY2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
        ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f := by
    intro z θ hz hθ0 hθ1
    rw [hsub, Work.Spaces.mixed_zero_right]
    have h := hCpw α f (b - b₁) 0 hα0 hα1 hfsm h6 (by omega) z hz θ ⟨hθ0, hθ1⟩
    have hval : Cpw / (Work.Spaces.gam α - 1) = Cpw * 10 * α ^ (-(1 : ℝ)) := by
      rw [Work.Spaces.gam_sub_one]
      rw [Real.rpow_neg_one]
      field_simp
    rwa [hval] at h
  -- #### integrability and bound of the middle slot
  have hYZmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact (h1.mul ((hfsm.mixed (b - b₁) (a - a₁)).continuousOn.pow 2)).mul
      ((hfsm.mixed b a).continuousOn.pow 2)
  have hYZpt : ∀ᵐ p ∂pm, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2
      ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
        * (Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hG : 0 ≤ Work.FTS.TransportS.leafGam α z θ :=
      Work.FTS.TransportS.leafGam_nonneg α hs.le
    have hY := hY2 z θ hz hθ0 hθ1
    have hZ2 : 0 ≤ (Work.Spaces.mixed b a f z θ) ^ 2 := sq_nonneg _
    calc Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed (b - b₁) (a - a₁) f z θ ^ 2
          * Work.Spaces.mixed b a f z θ ^ 2
        = (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * Work.Spaces.mixed (b - b₁) (a - a₁) f z θ ^ 2) := by ring
      _ ≤ (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hG) hZ2
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b a f z θ ^ 2) := by ring
  have hYZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' (hZint.const_mul
      (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) hYZmeas ?_
    filter_upwards [hYZpt, hGnn] with p hp hgn
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg hgn (sq_nonneg _)) (sq_nonneg _))]
    exact hp
  have hYZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
      * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm)
      ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
    calc (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2 ^ 2
          * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm)
        ≤ ∫ p, (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ^ 2) ∂pm :=
          MeasureTheory.integral_mono_ae hYZint (hZint.const_mul _) hYZpt
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ^ 2 ∂pm) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left hZv hC0
      _ ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
          linarith
  -- #### measurability of the full integrand
  have hFmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact ((h1.mul (hAsm.mixed b₁ a₁).continuousOn).mul
      (hfsm.mixed (b - b₁) (a - a₁)).continuousOn).mul (hfsm.mixed b a).continuousOn
  -- #### weighted Cauchy–Schwarz
  have hApos : 0 < K4 ^ 2 + 1 := by nlinarith [sq_nonneg K4]
  have hBpos : 0 < Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1 := by
    have h1 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
        * Work.Spaces.HkSq α 6 f := mul_nonneg hC0 hH
    linarith
  obtain ⟨hFint, hFbnd⟩ := slotAmgm (G := Work.FTS.TransportS.leafGam α)
    (X := fun z θ => Work.Spaces.mixed b₁ a₁ A z θ)
    (Y := fun z θ => Work.Spaces.mixed (b - b₁) (a - a₁) f z θ)
    (Z := fun z θ => Work.Spaces.mixed b a f z θ)
    (A := K4 ^ 2 + 1)
    (B := Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1)
    hXint hYZint hXv hYZv hApos hBpos hGnn hFmeas
  exact ⟨hFint, hFbnd.trans (slotArithBound hα0 hα1 hCpwpos hK0 hK4 hH)⟩

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
