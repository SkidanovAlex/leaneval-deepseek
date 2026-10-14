import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts.sigTruncId
import Submission.Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts.truncRadialIbpSig
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000


/-! ## Smoothness of `w²` and the second logarithmic derivative bound of a cut-off -/

/-- `z ↦ (w z)²` is `C²` on `(0,∞)`. -/
theorem contDiffOn_w_sq_two : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2)
    (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hden : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 (ne_of_gt hz)
  have hdiv : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) :=
    hnum.div hden hne
  have hsq : ContDiffOn ℝ 2 (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := hdiv.pow 2
  refine hsq.congr (fun z _ => ?_)
  rw [Work.Spaces.w]

/-- From the two logarithmic derivative bounds of `χ` one gets `|z²χ''| ≤ C₂ + C₁`. -/
theorem chi_second_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) {C₁ C₂ : ℝ}
    (h1 : ∀ z, |z * deriv χ z| ≤ C₁)
    (h2 : ∀ z, |z * deriv (fun w : ℝ => w * deriv χ w) z| ≤ C₂) :
    ∀ z, |z ^ 2 * deriv (deriv χ) z| ≤ C₂ + C₁ := by
  intro z
  have hd : DifferentiableAt ℝ χ z := (hχ.differentiable (by norm_num)) z
  have hd' : DifferentiableAt ℝ (deriv χ) z := (hχ.differentiable_deriv_two) z
  have hderiv : deriv (fun w : ℝ => w * deriv χ w) z = deriv χ z + z * deriv (deriv χ) z := by
    have h : HasDerivAt (fun w : ℝ => w * deriv χ w)
        (1 * deriv χ z + z * deriv (deriv χ) z) z :=
      (hasDerivAt_id z).mul hd'.hasDerivAt
    simpa using h.deriv
  have hkey : z ^ 2 * deriv (deriv χ) z
      = z * deriv (fun w : ℝ => w * deriv χ w) z - z * deriv χ z := by
    rw [hderiv]; ring
  rw [hkey]
  calc |z * deriv (fun w : ℝ => w * deriv χ w) z - z * deriv χ z|
      ≤ |z * deriv (fun w : ℝ => w * deriv χ w) z| + |z * deriv χ z| := abs_sub _ _
    _ ≤ C₂ + C₁ := add_le_add (h2 z) (h1 z)

/-- **The radial (`z ∂_z u`) slot of the `σ`-weighted first-order energy inequality.** -/
theorem zSlotBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨K, hKpos, hKslice⟩ := sliceBarSigmaUpperAe
  obtain ⟨χ, C₁, C₂, hC₁pos, hC₂pos, hχsm, hχrange, hχleft, hχmid, hχright, hχd1, hχd2,
    hχlim⟩ := Work.FTS.EllipticEst.Mine.zcutFam
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  set D₁ : ℝ := 3 + C₁ with hD₁def
  set D₂ : ℝ := 6 + 4 * C₁ + (C₂ + C₁) with hD₂def
  have hD₁nn : 0 ≤ D₁ := by rw [hD₁def]; linarith
  have hD₂nn : 0 ≤ D₂ := by rw [hD₂def]; linarith
  set Λ : ℝ := (1 / 32) * D₂ + (21 / 32) * D₁ with hΛdef
  have hΛnn : 0 ≤ Λ := by rw [hΛdef]; positivity
  set Λ₀ : ℝ := K + 1 / 2 + Λ with hΛ₀def
  have hΛ₀pos : 0 < Λ₀ := by rw [hΛ₀def]; linarith
  refine ⟨Λ₀, hΛ₀pos, ?_⟩
  intro α u G hAe
  have hα : 0 < α := hAe.hα
  have hα4 : α ≤ 1 / 4 := hAe.hα4
  have hU : Work.Spaces.HkMem α 0 u :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU α u G hAe
  have hgrad : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hAe
  have hRphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Rslice u z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hU).congr_fun (fun z _ => by
      simp only [Rslice_eq_integral]) measurableSet_Ici
  have hZphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Zslice u z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hgrad).congr_fun (fun z _ => by
      simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad]) measurableSet_Ici
  have hGphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Gslice G z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hAe.memG).congr_fun (fun z _ => by
      simp only [Gslice_eq_integral]) measurableSet_Ici
  have hRid : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z)
      = Work.Spaces.HkSq α 0 u := (HkSq_zero_eq_Rslice α u).symm
  have hGid : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Gslice G z)
      = Work.Spaces.HkSq α 0 G := by
    rw [HkSq_zero_eq_phi_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    simp only [Gslice_eq_integral]
  have haesmR : MeasureTheory.AEStronglyMeasurable (fun z => Rslice u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hU).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Rslice_eq_integral]))
  have haesmZ : MeasureTheory.AEStronglyMeasurable (fun z => Zslice u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hgrad).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad]))
  have haesmG : MeasureTheory.AEStronglyMeasurable (fun z => Gslice G z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hAe.memG).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Gslice_eq_integral]))
  have haesmS : MeasureTheory.AEStronglyMeasurable (Sslice G u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Sslice hAe
  have hR0 : ∀ z, 0 ≤ Rslice u z := Rslice_nonneg u
  have hG0 : ∀ z, 0 ≤ Gslice G z := Gslice_nonneg G
  have hSabs : ∀ z, 0 < z → |Sslice G u z| ≤ (1 / 2) * (Gslice G z + Rslice u z) := by
    intro z hz
    rw [abs_le]
    constructor
    · have h1 : (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
          (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) ≤ Sslice G u z := by
        rw [Sslice]
        refine MeasureTheory.integral_mono_ae ?_ (integrableOn_Sslice hAe hz) ?_
        · exact ((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul
            (-(1 / 2))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ := sig_nonneg_Iθ hθ
          have h2 : -(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) ≤ G z θ * u z θ := by
            nlinarith [sq_nonneg (G z θ + u z θ)]
          calc -(1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
              = Work.FTS.EllipticEst.sEta θ
                * (-(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) := by ring
            _ ≤ Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) :=
                mul_le_mul_of_nonneg_left h2 hσ
      have h2 : (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
            (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          = -(1 / 2) * (Gslice G z + Rslice u z) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (integrableOn_Gslice hAe hz) (integrableOn_Rslice hAe hz),
          Gslice, Rslice]
      calc -(1 / 2 * (Gslice G z + Rslice u z))
          = (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
              (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by rw [h2]; ring
        _ ≤ Sslice G u z := h1
    · have h1 : Sslice G u z ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) *
          (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
        rw [Sslice]
        refine MeasureTheory.integral_mono_ae (integrableOn_Sslice hAe hz) ?_ ?_
        · exact ((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul (1 / 2)
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ := sig_nonneg_Iθ hθ
          have h2 : 2 * (G z θ * u z θ) ≤ (G z θ) ^ 2 + (u z θ) ^ 2 := by
            nlinarith [sq_nonneg (G z θ - u z θ)]
          calc Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)
              = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (2 * (G z θ * u z θ))) := by ring
            _ ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ
                  * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ) (by norm_num)
            _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                  + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring
      have h2 : (∫ θ in Work.Spaces.Iθ, (1 / 2) *
            (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          = (1 / 2) * (Gslice G z + Rslice u z) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (integrableOn_Gslice hAe hz) (integrableOn_Rslice hAe hz),
          Gslice, Rslice]
      calc Sslice G u z
          ≤ (∫ θ in Work.Spaces.Iθ, (1 / 2) *
              (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := h1
        _ = (1 / 2) * (Gslice G z + Rslice u z) := h2
  have hcut : ∀ n : ℕ, α ^ 2 * (∫ z in Set.Ioi 0,
        (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
      ≤ Λ₀ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    intro n
    set ω : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * χ n z with hωdef
    have hωm : Measurable ω := measurable_w_sq.mul (hχsm n 2).continuous.measurable
    have hω0 : ∀ z, 0 ≤ ω z := fun z => mul_nonneg (w_sq_nonneg z) (hχrange n z).1
    have hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2 := fun z =>
      mul_le_of_le_one_right (w_sq_nonneg z) (hχrange n z).2
    have hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0) :=
      contDiffOn_w_sq_two.mul (hχsm n 2).contDiffOn
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hb : 1 / ((n : ℝ) + 1) < 2 * ((n : ℝ) + 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ h1]
      nlinarith [h1]
    have hsupp : ∀ z, z ∉ Set.Icc (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)) → ω z = 0 := by
      intro z hz
      rcases lt_or_ge z (1 / ((n : ℝ) + 1)) with h | h
      · have h1 : χ n z = 0 := hχleft n z (le_of_lt h)
        simp only [hωdef, h1, mul_zero]
      · have h2 : 2 * ((n : ℝ) + 1) < z := by
          rcases lt_or_ge (2 * ((n : ℝ) + 1)) z with h2 | h2
          · exact h2
          · exact absurd (Set.mem_Icc.mpr ⟨h, h2⟩) hz
        have h1 : χ n z = 0 := hχright n z (le_of_lt h2)
        simp only [hωdef, h1, mul_zero]
    have hA := Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts.truncRadialIbpSig
      α u hAe.smooth hgrad hAe.memRad2 hU ω hωd ha hb hsupp hω0 hωle
    have hBz : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        -K * Rslice u z ≤ Lslice u z := by
      filter_upwards [hKslice α u G hAe hU] with z hz
      have hC0 : 0 ≤ Cslice u z := Cslice_nonneg u z
      have hηpos : (0 : ℝ) < (1 - Work.Spaces.eta) / 2 := by
        have := Work.Spaces.eta_lt_one; linarith
      have h2 : 0 ≤ ((1 - Work.Spaces.eta) / 2) * Cslice u z := mul_nonneg hηpos.le hC0
      linarith [hz, h2]
    have hRint : MeasureTheory.IntegrableOn (fun z => ω z * Rslice u z) (Set.Ioi 0) :=
      integrableOn_omega_mul hRphi hωm hω0 hωle hR0 haesmR
    have hGint : MeasureTheory.IntegrableOn (fun z => ω z * Gslice G z) (Set.Ioi 0) :=
      integrableOn_omega_mul hGphi hωm hω0 hωle hG0 haesmG
    have hSint : MeasureTheory.IntegrableOn (fun z => ω z * Sslice G u z) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' ((hGint.add hRint).const_mul (1 / 2))
        (hωm.aestronglyMeasurable.mul haesmS) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hω0 z)]
      calc ω z * |Sslice G u z| ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
            mul_le_mul_of_nonneg_left (hSabs z hz) (hω0 z)
        _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
    have hLint : MeasureTheory.IntegrableOn (fun z => ω z * Lslice u z) (Set.Ioi 0) := by
      refine (hA.1.add hSint).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      show ω z * Pslice α u z + ω z * Sslice G u z = ω z * Lslice u z
      rw [Lslice_eq_Pslice_add_Sslice hAe hz]
      ring
    have hPS : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        = (∫ z in Set.Ioi 0, ω z * Lslice u z)
          - (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Lslice u z)
          = (∫ z in Set.Ioi 0, ω z * Pslice α u z)
            + (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
        rw [show (∫ z in Set.Ioi 0, ω z * Lslice u z)
            = ∫ z in Set.Ioi 0, (ω z * Pslice α u z + ω z * Sslice G u z) from by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          show ω z * Lslice u z = ω z * Pslice α u z + ω z * Sslice G u z
          rw [Lslice_eq_Pslice_add_Sslice hAe hz]
          ring]
        exact MeasureTheory.integral_add hA.1 hSint
      linarith [h1]
    have hBL : -(∫ z in Set.Ioi 0, ω z * Lslice u z)
        ≤ K * (∫ z in Set.Ioi 0, ω z * Rslice u z) := by
      have h1 : (∫ z in Set.Ioi 0, (-K) * (ω z * Rslice u z))
          ≤ ∫ z in Set.Ioi 0, ω z * Lslice u z := by
        refine MeasureTheory.integral_mono_ae (hRint.const_mul (-K)) hLint ?_
        filter_upwards [hBz, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz _
        calc (-K) * (ω z * Rslice u z) = ω z * (-K * Rslice u z) := by ring
          _ ≤ ω z * Lslice u z := mul_le_mul_of_nonneg_left hz (hω0 z)
      rw [MeasureTheory.integral_const_mul] at h1
      linarith [h1]
    have hSle_int : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
        ≤ (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
            + (∫ z in Set.Ioi 0, ω z * Rslice u z)) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
          ≤ ∫ z in Set.Ioi 0, (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by
        refine MeasureTheory.integral_mono_ae hSint ((hGint.add hRint).const_mul (1 / 2)) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        calc ω z * Sslice G u z ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
              mul_le_mul_of_nonneg_left (abs_le.mp (hSabs z hz)).2 (hω0 z)
          _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hGint hRint] at h1
      linarith [h1]
    have hcc : ∀ z, 0 < z → |deriv (fun y : ℝ => y * ω y) z|
        ≤ D₁ * (Work.Spaces.w z) ^ 2 := by
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n)
        (chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n))
        (fun z => by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) hC₁nn
        (add_nonneg hC₂nn hC₁nn)).1
      exact h
    have hcc2 : ∀ z, 0 < z →
        |deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z| ≤ D₂ * (Work.Spaces.w z) ^ 2 := by
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n)
        (chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n))
        (fun z => by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) hC₁nn
        (add_nonneg hC₂nn hC₁nn)).2
      exact h
    have hsm1 : MeasureTheory.AEStronglyMeasurable (deriv (fun y : ℝ => y * ω y))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      ((contDiffOn_id.mul hωd).continuousOn_deriv_of_isOpen isOpen_Ioi
        (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hsm2' : MeasureTheory.AEStronglyMeasurable
        (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      ((((contDiffOn_id.pow 2).mul hωd).deriv_of_isOpen (m := 1) isOpen_Ioi
        (by norm_num)).continuousOn_deriv_of_isOpen isOpen_Ioi
        (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hT1bd : |∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z|
        ≤ D₁ * Work.Spaces.HkSq α 0 u := by
      have h := (integrableOn_coef_mul_le hRphi hD₁nn hcc hR0 hsm1 haesmR).2
      rw [hRid] at h
      exact h
    have hT2bd : |∫ z in Set.Ioi 0, deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z|
        ≤ D₂ * Work.Spaces.HkSq α 0 u := by
      have h := (integrableOn_coef_mul_le hRphi hD₂nn hcc2 hR0 hsm2' haesmR).2
      rw [hRid] at h
      exact h
    have hid : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        = -α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
          + (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
              deriv (fun y : ℝ => y * ω y) z * Rslice u z) := by
      have h := hA.2
      simp only [Rslice, Zslice, Pslice] at h ⊢
      exact h
    have hZnn : 0 ≤ ∫ z in Set.Ioi 0, ω z * Zslice u z := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _
      exact mul_nonneg (hω0 z) (Zslice_nonneg u z)
    have hRωle : (∫ z in Set.Ioi 0, ω z * Rslice u z) ≤ Work.Spaces.HkSq α 0 u := by
      calc (∫ z in Set.Ioi 0, ω z * Rslice u z)
          ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z :=
            integral_omega_mul_le hRphi hωm hω0 hωle hR0 haesmR
        _ = Work.Spaces.HkSq α 0 u := hRid
    have hGωle : (∫ z in Set.Ioi 0, ω z * Gslice G z) ≤ Work.Spaces.HkSq α 0 G := by
      calc (∫ z in Set.Ioi 0, ω z * Gslice G z)
          ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Gslice G z :=
            integral_omega_mul_le hGphi hωm hω0 hωle hG0 haesmG
        _ = Work.Spaces.HkSq α 0 G := hGid
    have hα2 : α ^ 2 / 2 ≤ 1 / 32 := by nlinarith [hα, hα4]
    have hα5 : α * (5 + α) / 2 ≤ 21 / 32 := by
      have h5 : α * (5 + α) ≤ 21 / 16 := by nlinarith [hα, hα4]
      linarith
    have hSbound : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
        ≤ (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h3 := add_le_add hGωle hRωle
      linarith [hSle_int, h3]
    have hPbound : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        ≤ Λ * Work.Spaces.HkSq α 0 u := by
      have hA1 : (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          ≤ (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hT2bd) (by positivity)
      have hA3 : -((α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun y : ℝ => y * ω y) z * Rslice u z))
          ≤ (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u) := by
        have h2 : -(∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z)
            ≤ D₁ * Work.Spaces.HkSq α 0 u := (neg_le_abs _).trans hT1bd
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ α * (5 + α) / 2)
        linarith [h3]
      have h1 : (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u)
          ≤ ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u := by
        have h := mul_le_mul_of_nonneg_right hα2
          (mul_nonneg hD₂nn (Work.Spaces.HkSq_nonneg α 0 u))
        linarith [h]
      have h2 : (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u)
          ≤ ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by
        have h := mul_le_mul_of_nonneg_right hα5
          (mul_nonneg hD₁nn (Work.Spaces.HkSq_nonneg α 0 u))
        linarith [h]
      have h3 : Λ * Work.Spaces.HkSq α 0 u
          = ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u
            + ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by
        rw [hΛdef]; ring
      have h6 : 0 ≤ α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z) :=
        mul_nonneg (sq_nonneg α) hZnn
      linarith [hid, hA1, hA3, h1, h2, h3, h6]
    have hLbound : (∫ z in Set.Ioi 0, ω z * Lslice u z)
        ≤ Λ * Work.Spaces.HkSq α 0 u
          + (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Lslice u z)
          = (∫ z in Set.Ioi 0, ω z * Pslice α u z)
            + (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
        linarith [hPS]
      linarith [h1, hPbound, hSbound]
    have hkey : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
        ≤ K * (∫ z in Set.Ioi 0, ω z * Rslice u z)
          + (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
              + (∫ z in Set.Ioi 0, ω z * Rslice u z))
          + (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u)
          + (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u) := by
      have hA1 : (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          ≤ (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hT2bd) (by positivity)
      have hA3 : -((α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun y : ℝ => y * ω y) z * Rslice u z))
          ≤ (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u) := by
        have h2 : -(∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z)
            ≤ D₁ * Work.Spaces.HkSq α 0 u := (neg_le_abs _).trans hT1bd
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ α * (5 + α) / 2)
        linarith [h3]
      linarith [hid, hPS, hBL, hSle_int, hA1, hA3]
    have hstep : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
        ≤ Λ₀ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h1 : K * (∫ z in Set.Ioi 0, ω z * Rslice u z)
          ≤ K * Work.Spaces.HkSq α 0 u := mul_le_mul_of_nonneg_left hRωle hKpos.le
      have h2 : (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
            + (∫ z in Set.Ioi 0, ω z * Rslice u z))
          ≤ (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
        have h3 := add_le_add hGωle hRωle
        linarith
      have h3 : (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u)
          ≤ ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u := by
        have h := mul_le_mul_of_nonneg_right hα2
          (mul_nonneg hD₂nn (Work.Spaces.HkSq_nonneg α 0 u))
        linarith [h]
      have h4 : (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u)
          ≤ ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by
        have h := mul_le_mul_of_nonneg_right hα5
          (mul_nonneg hD₁nn (Work.Spaces.HkSq_nonneg α 0 u))
        linarith [h]
      have h5 : Λ₀ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
          = (K + 1 / 2 + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
        rw [hΛ₀def]
      have h6 : Λ * Work.Spaces.HkSq α 0 u
          = ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u
            + ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by
        rw [hΛdef]; ring
      have hG0' : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
      have hU0' : 0 ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
      nlinarith [hkey, h1, h2, h3, h4, h5, h6, hKpos.le, hΛnn, hG0', hU0']
    linarith [hstep]
  have hlim : α ^ 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Zslice u z)
      ≤ Λ₀ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    have hφZ : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Zslice u z) (Set.Ioi 0) :=
      hZphi.mono_set Set.Ioi_subset_Ici_self
    have hconv : Filter.Tendsto
        (fun n => ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
        Filter.atTop (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Zslice u z)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun z => |(Work.Spaces.w z) ^ 2 * Zslice u z|)
        (F := fun n z => (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z) ?_ hφZ.abs ?_ ?_
      · intro n
        exact (measurable_w_sq.mul (hχsm n 2).continuous.measurable).aestronglyMeasurable.mul
          haesmZ
      · intro n
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |(Work.Spaces.w z) ^ 2| * |χ n z| ≤ |(Work.Spaces.w z) ^ 2| := by
          rw [abs_of_nonneg (w_sq_nonneg z)]
          calc (Work.Spaces.w z) ^ 2 * |χ n z| ≤ (Work.Spaces.w z) ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left
                  (by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) (w_sq_nonneg z)
            _ = (Work.Spaces.w z) ^ 2 := mul_one _
        calc |(Work.Spaces.w z) ^ 2| * |χ n z| * |Zslice u z|
            ≤ |(Work.Spaces.w z) ^ 2| * |Zslice u z| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = |(Work.Spaces.w z) ^ 2 * Zslice u z| := (abs_mul _ _).symm
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        have h1 : Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1) := hχlim z hz
        have h2 : (fun n : ℕ => (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
            = fun n : ℕ => ((Work.Spaces.w z) ^ 2 * Zslice u z) * χ n z := by
          funext n; ring
        rw [h2]
        simpa using h1.const_mul ((Work.Spaces.w z) ^ 2 * Zslice u z)
    have h2 := le_of_tendsto' (hconv.const_mul (α ^ 2)) (fun n => hcut n)
    have h3 : α ^ 2 * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Zslice u z)
        = α ^ 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Zslice u z) := by
      rw [setIntegral_Ioi_eq_Iz]
    rw [h3] at h2
    exact h2
  change α ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)
      ≤ Λ₀ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
  rw [HkSq_grad_eq_Zslice]
  exact hlim

/-- **The `u / cos θ` slot of the `σ`-weighted first-order energy inequality.** -/
theorem cSlotBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨K, hKpos, hKslice⟩ := sliceBarSigmaUpperAe
  obtain ⟨χ, C₁, C₂, hC₁pos, hC₂pos, hχsm, hχrange, hχleft, hχmid, hχright, hχd1, hχd2,
    hχlim⟩ := Work.FTS.EllipticEst.Mine.zcutFam
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  set D₁ : ℝ := 3 + C₁ with hD₁def
  set D₂ : ℝ := 6 + 4 * C₁ + (C₂ + C₁) with hD₂def
  have hD₁nn : 0 ≤ D₁ := by rw [hD₁def]; linarith
  have hD₂nn : 0 ≤ D₂ := by rw [hD₂def]; linarith
  set Lam : ℝ := (1 / 32) * D₂ + (21 / 32) * D₁ with hLamdef
  have hLamnn : 0 ≤ Lam := by rw [hLamdef]; positivity
  set B0 : ℝ := K + Lam + 1 / 2 with hB0def
  have hB0pos : 0 < B0 := by rw [hB0def]; linarith
  have hηpos : (0 : ℝ) < 1 - Work.Spaces.eta := by
    have := Work.Spaces.eta_lt_one; linarith
  refine ⟨(2 / (1 - Work.Spaces.eta)) * B0, by positivity, ?_⟩
  intro α u G hAe
  have hα : 0 < α := hAe.hα
  have hα4 : α ≤ 1 / 4 := hAe.hα4
  have hU : Work.Spaces.HkMem α 0 u :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU α u G hAe
  have hgrad : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hAe
  have hRphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Rslice u z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hU).congr_fun (fun z _ => by
      simp only [Rslice_eq_integral]) measurableSet_Ici
  have hGphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Gslice G z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hAe.memG).congr_fun (fun z _ => by
      simp only [Gslice_eq_integral]) measurableSet_Ici
  have hRid : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z)
      = Work.Spaces.HkSq α 0 u := (HkSq_zero_eq_Rslice α u).symm
  have hGid : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Gslice G z)
      = Work.Spaces.HkSq α 0 G := by
    rw [HkSq_zero_eq_phi_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    simp only [Gslice_eq_integral]
  have haesmR : MeasureTheory.AEStronglyMeasurable (fun z => Rslice u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hU).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Rslice_eq_integral]))
  have haesmG : MeasureTheory.AEStronglyMeasurable (fun z => Gslice G z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hAe.memG).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Gslice_eq_integral]))
  have haesmS : MeasureTheory.AEStronglyMeasurable (Sslice G u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Sslice hAe
  have haesmC : MeasureTheory.AEStronglyMeasurable (Cslice u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Cslice hAe
  have hR0 : ∀ z, 0 ≤ Rslice u z := Rslice_nonneg u
  have hG0 : ∀ z, 0 ≤ Gslice G z := Gslice_nonneg G
  have hZphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Zslice u z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hgrad).congr_fun (fun z _ => by
      simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad]) measurableSet_Ici
  have haesmZ : MeasureTheory.AEStronglyMeasurable (fun z => Zslice u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hgrad).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad]))
  have hCcae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ((1 - Work.Spaces.eta) / 2) * Cslice u z ≤ Lslice u z + K * Rslice u z :=
    hKslice α u G hAe hU
  have hSabs : ∀ z, 0 < z → |Sslice G u z| ≤ (1 / 2) * (Gslice G z + Rslice u z) := by
    intro z hz
    rw [abs_le]
    constructor
    · have h1 : (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
          (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) ≤ Sslice G u z := by
        rw [Sslice]
        refine MeasureTheory.integral_mono_ae ?_ (integrableOn_Sslice hAe hz) ?_
        · exact ((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul
            (-(1 / 2))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ := sig_nonneg_Iθ hθ
          have h2 : -(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) ≤ G z θ * u z θ := by
            nlinarith [sq_nonneg (G z θ + u z θ)]
          calc -(1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
              = Work.FTS.EllipticEst.sEta θ
                * (-(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) := by ring
            _ ≤ Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) :=
                mul_le_mul_of_nonneg_left h2 hσ
      have h2 : (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
            (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          = -(1 / 2) * (Gslice G z + Rslice u z) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (integrableOn_Gslice hAe hz) (integrableOn_Rslice hAe hz),
          Gslice, Rslice]
      calc -(1 / 2 * (Gslice G z + Rslice u z))
          = (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
              (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by rw [h2]; ring
        _ ≤ Sslice G u z := h1
    · have h1 : Sslice G u z ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) *
          (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
        rw [Sslice]
        refine MeasureTheory.integral_mono_ae (integrableOn_Sslice hAe hz) ?_ ?_
        · exact ((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul (1 / 2)
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ := sig_nonneg_Iθ hθ
          have h2 : 2 * (G z θ * u z θ) ≤ (G z θ) ^ 2 + (u z θ) ^ 2 := by
            nlinarith [sq_nonneg (G z θ - u z θ)]
          calc Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)
              = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (2 * (G z θ * u z θ))) := by ring
            _ ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ
                  * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ) (by norm_num)
            _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                  + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring
      have h2 : (∫ θ in Work.Spaces.Iθ, (1 / 2) *
            (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          = (1 / 2) * (Gslice G z + Rslice u z) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (integrableOn_Gslice hAe hz) (integrableOn_Rslice hAe hz),
          Gslice, Rslice]
      calc Sslice G u z
          ≤ (∫ θ in Work.Spaces.Iθ, (1 / 2) *
              (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := h1
        _ = (1 / 2) * (Gslice G z + Rslice u z) := h2
  have hcut : ∀ n : ℕ, (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * χ n z * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
      ≤ ENNReal.ofReal (B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) := by
    intro n
    set ω : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * χ n z with hωdef
    have hωm : Measurable ω := measurable_w_sq.mul (hχsm n 2).continuous.measurable
    have hω0 : ∀ z, 0 ≤ ω z := fun z => mul_nonneg (w_sq_nonneg z) (hχrange n z).1
    have hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2 := fun z =>
      mul_le_of_le_one_right (w_sq_nonneg z) (hχrange n z).2
    have hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0) :=
      contDiffOn_w_sq_two.mul (hχsm n 2).contDiffOn
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hb : 1 / ((n : ℝ) + 1) < 2 * ((n : ℝ) + 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ h1]
      nlinarith [h1]
    have hsupp : ∀ z, z ∉ Set.Icc (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)) → ω z = 0 := by
      intro z hz
      rcases lt_or_ge z (1 / ((n : ℝ) + 1)) with h | h
      · have h1 : χ n z = 0 := hχleft n z (le_of_lt h)
        simp only [hωdef, h1, mul_zero]
      · have h2 : 2 * ((n : ℝ) + 1) < z := by
          rcases lt_or_ge (2 * ((n : ℝ) + 1)) z with h2 | h2
          · exact h2
          · exact absurd (Set.mem_Icc.mpr ⟨h, h2⟩) hz
        have h1 : χ n z = 0 := hχright n z (le_of_lt h2)
        simp only [hωdef, h1, mul_zero]
    have hA := Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts.truncRadialIbpSig
      α u hAe.smooth hgrad hAe.memRad2 hU ω hωd ha hb hsupp hω0 hωle
    have hCcω : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ((1 - Work.Spaces.eta) / 2) * (ω z * Cslice u z)
          ≤ ω z * (Lslice u z + K * Rslice u z) := by
      filter_upwards [hCcae] with z hz
      calc ((1 - Work.Spaces.eta) / 2) * (ω z * Cslice u z)
          = ω z * (((1 - Work.Spaces.eta) / 2) * Cslice u z) := by ring
        _ ≤ ω z * (Lslice u z + K * Rslice u z) :=
            mul_le_mul_of_nonneg_left hz (hω0 z)
    have hRint : MeasureTheory.IntegrableOn (fun z => ω z * Rslice u z) (Set.Ioi 0) :=
      integrableOn_omega_mul hRphi hωm hω0 hωle hR0 haesmR
    have hGint : MeasureTheory.IntegrableOn (fun z => ω z * Gslice G z) (Set.Ioi 0) :=
      integrableOn_omega_mul hGphi hωm hω0 hωle hG0 haesmG
    have hZint : MeasureTheory.IntegrableOn (fun z => ω z * Zslice u z) (Set.Ioi 0) :=
      integrableOn_omega_mul hZphi hωm hω0 hωle (Zslice_nonneg u) haesmZ
    have hSint : MeasureTheory.IntegrableOn (fun z => ω z * Sslice G u z) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' ((hGint.add hRint).const_mul (1 / 2))
        (hωm.aestronglyMeasurable.mul haesmS) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hω0 z)]
      calc ω z * |Sslice G u z| ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
            mul_le_mul_of_nonneg_left (hSabs z hz) (hω0 z)
        _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
    have hLint : MeasureTheory.IntegrableOn (fun z => ω z * Lslice u z) (Set.Ioi 0) := by
      refine (hA.1.add hSint).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      show ω z * Pslice α u z + ω z * Sslice G u z = ω z * Lslice u z
      rw [Lslice_eq_Pslice_add_Sslice hAe hz]
      ring
    have hcc : ∀ z, 0 < z → |deriv (fun y : ℝ => y * ω y) z|
        ≤ D₁ * (Work.Spaces.w z) ^ 2 := by
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n)
        (chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n))
        (fun z => by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) hC₁nn
        (add_nonneg hC₂nn hC₁nn)).1
      exact h
    have hcc2 : ∀ z, 0 < z →
        |deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z| ≤ D₂ * (Work.Spaces.w z) ^ 2 := by
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n)
        (chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n))
        (fun z => by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) hC₁nn
        (add_nonneg hC₂nn hC₁nn)).2
      exact h
    have hsm1 : MeasureTheory.AEStronglyMeasurable (deriv (fun y : ℝ => y * ω y))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      ((contDiffOn_id.mul hωd).continuousOn_deriv_of_isOpen isOpen_Ioi
        (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hsm2' : MeasureTheory.AEStronglyMeasurable
        (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      ((((contDiffOn_id.pow 2).mul hωd).deriv_of_isOpen (m := 1) isOpen_Ioi
        (by norm_num)).continuousOn_deriv_of_isOpen isOpen_Ioi
        (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hT1bd : |∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z|
        ≤ D₁ * Work.Spaces.HkSq α 0 u := by
      have h := (integrableOn_coef_mul_le hRphi hD₁nn hcc hR0 hsm1 haesmR).2
      rw [hRid] at h
      exact h
    have hT2bd : |∫ z in Set.Ioi 0, deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z|
        ≤ D₂ * Work.Spaces.HkSq α 0 u := by
      have h := (integrableOn_coef_mul_le hRphi hD₂nn hcc2 hR0 hsm2' haesmR).2
      rw [hRid] at h
      exact h
    have hid : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        = -α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
          + (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
              deriv (fun y : ℝ => y * ω y) z * Rslice u z) := by
      have h := hA.2
      simp only [Rslice, Zslice, Pslice] at h ⊢
      exact h
    have hZnn : 0 ≤ ∫ z in Set.Ioi 0, ω z * Zslice u z := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _
      exact mul_nonneg (hω0 z) (Zslice_nonneg u z)
    have hRωle : (∫ z in Set.Ioi 0, ω z * Rslice u z) ≤ Work.Spaces.HkSq α 0 u := by
      calc (∫ z in Set.Ioi 0, ω z * Rslice u z)
          ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z :=
            integral_omega_mul_le hRphi hωm hω0 hωle hR0 haesmR
        _ = Work.Spaces.HkSq α 0 u := hRid
    have hGωle : (∫ z in Set.Ioi 0, ω z * Gslice G z) ≤ Work.Spaces.HkSq α 0 G := by
      calc (∫ z in Set.Ioi 0, ω z * Gslice G z)
          ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Gslice G z :=
            integral_omega_mul_le hGphi hωm hω0 hωle hG0 haesmG
        _ = Work.Spaces.HkSq α 0 G := hGid
    have hα2 : α ^ 2 / 2 ≤ 1 / 32 := by nlinarith [hα, hα4]
    have hα5 : α * (5 + α) / 2 ≤ 21 / 32 := by
      have h5 : α * (5 + α) ≤ 21 / 16 := by nlinarith [hα, hα4]
      linarith
    have hSbound : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
        ≤ (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
          ≤ (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
              + (∫ z in Set.Ioi 0, ω z * Rslice u z)) := by
        have h2 : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
            ≤ ∫ z in Set.Ioi 0, (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by
          refine MeasureTheory.integral_mono_ae hSint ((hGint.add hRint).const_mul (1 / 2)) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
          calc ω z * Sslice G u z ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
                mul_le_mul_of_nonneg_left (abs_le.mp (hSabs z hz)).2 (hω0 z)
            _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hGint hRint] at h2
        linarith [h2]
      have h3 := add_le_add hGωle hRωle
      linarith [h1, h3]
    have hPbound : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        ≤ Lam * Work.Spaces.HkSq α 0 u := by
      have hA1 : (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          ≤ (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hT2bd) (by positivity)
      have hA3 : -((α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun y : ℝ => y * ω y) z * Rslice u z))
          ≤ (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u) := by
        have h2 : -(∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z)
            ≤ D₁ * Work.Spaces.HkSq α 0 u := (neg_le_abs _).trans hT1bd
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ α * (5 + α) / 2)
        linarith [h3]
      have h1 : (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u)
          ≤ ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u := by
        have h := mul_le_mul_of_nonneg_right hα2
          (mul_nonneg hD₂nn (Work.Spaces.HkSq_nonneg α 0 u))
        linarith [h]
      have h2 : (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u)
          ≤ ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by
        have h := mul_le_mul_of_nonneg_right hα5
          (mul_nonneg hD₁nn (Work.Spaces.HkSq_nonneg α 0 u))
        linarith [h]
      have h3 : Lam * Work.Spaces.HkSq α 0 u
          = ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u
            + ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by
        rw [hLamdef]; ring
      have h6 : 0 ≤ α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z) :=
        mul_nonneg (sq_nonneg α) hZnn
      linarith [hid, hA1, hA3, h1, h2, h3, h6]
    have hLbound : (∫ z in Set.Ioi 0, ω z * Lslice u z)
        ≤ Lam * Work.Spaces.HkSq α 0 u
          + (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Lslice u z)
          = (∫ z in Set.Ioi 0, ω z * Pslice α u z)
            + (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
        have h2 : (∫ z in Set.Ioi 0, ω z * Lslice u z)
            = (∫ z in Set.Ioi 0, ω z * Pslice α u z)
              + (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
          rw [show (∫ z in Set.Ioi 0, ω z * Lslice u z)
              = ∫ z in Set.Ioi 0, (ω z * Pslice α u z + ω z * Sslice G u z) from by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
            show ω z * Lslice u z = ω z * Pslice α u z + ω z * Sslice G u z
            rw [Lslice_eq_Pslice_add_Sslice hAe hz]
            ring]
          exact MeasureTheory.integral_add hA.1 hSint
        exact h2
      linarith [h1, hPbound, hSbound]
    have hRLbound : (∫ z in Set.Ioi 0, ω z * (Lslice u z + K * Rslice u z))
        ≤ B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h13 : (∫ z in Set.Ioi 0, ω z * (Lslice u z + K * Rslice u z))
          = (∫ z in Set.Ioi 0, ω z * Lslice u z)
            + K * (∫ z in Set.Ioi 0, ω z * Rslice u z) := by
        rw [show (∫ z in Set.Ioi 0, ω z * (Lslice u z + K * Rslice u z))
            = ∫ z in Set.Ioi 0, (ω z * Lslice u z + K * (ω z * Rslice u z)) from
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
        rw [MeasureTheory.integral_add hLint (hRint.const_mul K),
          MeasureTheory.integral_const_mul]
      have h7 : K * (∫ z in Set.Ioi 0, ω z * Rslice u z) ≤ K * Work.Spaces.HkSq α 0 u :=
        mul_le_mul_of_nonneg_left hRωle hKpos.le
      have h10 : (∫ z in Set.Ioi 0, ω z * (Lslice u z + K * Rslice u z))
          ≤ Lam * Work.Spaces.HkSq α 0 u
            + (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
            + K * Work.Spaces.HkSq α 0 u := by
        rw [h13]
        linarith [h7, hLbound]
      have h9 : 0 ≤ (K + Lam) * Work.Spaces.HkSq α 0 G :=
        mul_nonneg (add_nonneg hKpos.le hLamnn) (Work.Spaces.HkSq_nonneg α 0 G)
      have h11 : Lam * Work.Spaces.HkSq α 0 u
            + (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
            + K * Work.Spaces.HkSq α 0 u
          ≤ B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
        rw [hB0def]
        nlinarith [h9]
      linarith [h10, h11]
    have hRHSint : MeasureTheory.IntegrableOn
        (fun z => ω z * (Lslice u z + K * Rslice u z)) (Set.Ioi 0) := by
      refine (hLint.add (hRint.const_mul K)).congr
        (Filter.Eventually.of_forall (fun z => ?_))
      show ω z * Lslice u z + K * (ω z * Rslice u z) = ω z * (Lslice u z + K * Rslice u z)
      ring
    have hRHSnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun z => ω z * (Lslice u z + K * Rslice u z)) := by
      filter_upwards [hCcω] with z hz
      have h9 : 0 ≤ ((1 - Work.Spaces.eta) / 2) * (ω z * Cslice u z) :=
        mul_nonneg (by linarith) (mul_nonneg (hω0 z) (Cslice_nonneg u z))
      exact le_trans h9 hz
    calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
          (ω z * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
        ≤ ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (ω z
            * (Lslice u z + K * Rslice u z)) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hCcω] with z hz
          refine ENNReal.ofReal_le_ofReal ?_
          calc ω z * ((1 - Work.Spaces.eta) / 2) * Cslice u z
              = ((1 - Work.Spaces.eta) / 2) * (ω z * Cslice u z) := by ring
            _ ≤ ω z * (Lslice u z + K * Rslice u z) := hz
      _ = ENNReal.ofReal (∫ z in Set.Ioi 0, ω z * (Lslice u z + K * Rslice u z)) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hRHSint hRHSnn).symm
      _ ≤ ENNReal.ofReal (B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) :=
          ENNReal.ofReal_le_ofReal hRLbound
  -- Fatou in `n`
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.atTop.liminf (fun n : ℕ => ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * χ n z * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2)
            * Cslice u z) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have h1 : Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1) := hχlim z hz
    have h2 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * χ n z * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
        Filter.atTop (nhds (ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z))) := by
      have h4 : Filter.Tendsto (fun n : ℕ => ((Work.Spaces.w z) ^ 2
            * ((1 - Work.Spaces.eta) / 2) * Cslice u z) * χ n z) Filter.atTop
          (nhds (((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z)
            * 1)) :=
        h1.const_mul ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z)
      have h6 : ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z) * 1
          = (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z := by ring
      rw [h6] at h4
      refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (Filter.Tendsto.congr' ?_ h4)
      exact Filter.Eventually.of_forall (fun n => by ring)
    exact h2.liminf_eq
  have hlimb : Filter.atTop.liminf (fun n : ℕ => ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * χ n z * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
      ≤ ENNReal.ofReal (B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently
      (Filter.Eventually.of_forall hcut))
  have hFatou : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
      ≤ ENNReal.ofReal (B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) := by
    have hf := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (u := Filter.atTop)
      (f := fun n z => ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * χ n z * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
      (fun n => ENNReal.measurable_ofReal.comp_aemeasurable
        (((measurable_w_sq.mul
          (hχsm n 2).continuous.measurable).mul_const _).aemeasurable.mul
          haesmC.aemeasurable))
    calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
        = ∫⁻ z in Set.Ioi 0, Filter.atTop.liminf (fun n : ℕ => ENNReal.ofReal
            ((Work.Spaces.w z) ^ 2 * χ n z * ((1 - Work.Spaces.eta) / 2)
              * Cslice u z)) := (MeasureTheory.lintegral_congr_ae hpt).symm
      _ ≤ _ := hf
      _ ≤ _ := hlimb
  -- from Fatou: integrability and the bound for `∫ φ Cslice`
  have hφ1int : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z)
      (Set.Ioi 0) := by
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun z => (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z) :=
      Filter.Eventually.of_forall fun z =>
        mul_nonneg (mul_nonneg (w_sq_nonneg z) (by linarith)) (Cslice_nonneg u z)
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z => (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      ((measurable_w_sq.mul_const _).aestronglyMeasurable).mul haesmC
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm hnn).mp
      (ne_top_of_le_ne_top (by simp) hFatou)
  have hφint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Cslice u z) (Set.Ioi 0) := by
    have hc : MeasureTheory.IntegrableOn
        (fun z => (1 / ((1 - Work.Spaces.eta) / 2))
          * ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z))
        (Set.Ioi 0) := hφ1int.const_mul _
    refine hc.congr (Filter.Eventually.of_forall (fun z => ?_))
    show (1 / ((1 - Work.Spaces.eta) / 2))
          * ((Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z)
        = (Work.Spaces.w z) ^ 2 * Cslice u z
    have hne : ((1 - Work.Spaces.eta) / 2) ≠ 0 := by linarith
    field_simp
    try ring
  have hφCle : ((1 - Work.Spaces.eta) / 2)
      * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Cslice u z)
      ≤ B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    have h1 : ENNReal.ofReal (∫ z in Set.Ioi 0,
        (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2) * Cslice u z)
        ≤ ENNReal.ofReal (B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφ1int (by
        filter_upwards with z
        exact mul_nonneg (mul_nonneg (w_sq_nonneg z) (by linarith)) (Cslice_nonneg u z))]
      exact hFatou
    have h2 : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2)
          * Cslice u z) ≤ B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB0pos.le
        (add_nonneg (Work.Spaces.HkSq_nonneg α 0 G) (Work.Spaces.HkSq_nonneg α 0 u)))).mp h1
    have h3 : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / 2)
          * Cslice u z)
        = ((1 - Work.Spaces.eta) / 2)
          * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Cslice u z) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
    rw [h3] at h2
    exact h2
  -- conclusion
  have h1 : Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Cslice u z := by
    rw [HkSq_zero_eq_phi_mul]
    rfl
  have h2 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Cslice u z)
      ≤ (2 / (1 - Work.Spaces.eta)) * B0
        * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    have h3 := hφCle
    have h4 : ((1 - Work.Spaces.eta) / 2)
        * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Cslice u z)
        = (1 / 2) * ((1 - Work.Spaces.eta)
            * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Cslice u z)) := by ring
    rw [h4] at h3
    have h5 : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Cslice u z)
        ≤ (2 / (1 - Work.Spaces.eta)) * B0
          * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h6 : (1 - Work.Spaces.eta)
            * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Cslice u z)
          ≤ 2 * (B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) := by
        linarith [h3]
      have h7 : (2 / (1 - Work.Spaces.eta)) * B0
            * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
          = (2 * (B0 * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)))
            / (1 - Work.Spaces.eta) := by ring
      rw [h7, le_div_iff₀ hηpos]
      linarith [h6]
    have h8 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Cslice u z)
        = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Cslice u z :=
      (setIntegral_Ioi_eq_Iz (fun z => (Work.Spaces.w z) ^ 2 * Cslice u z)).symm
    rw [h8]
    exact h5
  rw [h1]
  exact h2


end Work.FTS.EllipticEst.AeS1
