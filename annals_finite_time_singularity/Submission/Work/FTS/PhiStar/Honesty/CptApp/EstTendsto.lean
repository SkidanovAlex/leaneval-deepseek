/-
# `exists_cptQ_approx` — the `z`-integration and the convergence of the `ℋᵏ`-norm

This module turns the per-`z` bound `EstMain.theta_lintegral_le` into a bound on the full
`ℋᵏ`-square of the error,

  `HkSq α k (err n F) ≤ C · (T_n + (2/n)^{2+η} · HkSq α k F)`,

with `T_n` the tail of the `ℋᵏ`-energy of `F` over the shrinking region `Ω_n`; since both terms
tend to `0` (`tendsto_lintegral_Omega` and `(2/n)^{2+η} → 0`), so does `HkSq α k (err n F)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstMain
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.tendsto_lintegral_Omega
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Joint a.e. strong measurability of the `ℋᵏ`-integrand -/

theorem aestronglyMeasurable_uncurry_HkIntegrand {α : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α k)

/-- The inner `θ`-integral of the `ℋᵏ`-integrand is a.e. strongly measurable in `z`. -/
theorem aemeasurable_integral_HkIntegrand {α : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
      (volume.restrict Work.Spaces.Iz) :=
  (aestronglyMeasurable_uncurry_HkIntegrand (α := α) (k := k) hsm).integral_prod_right'.aemeasurable

/-- The `Ω_n`-part of the `ℋᵏ`-integrand is jointly a.e. strongly measurable. -/
theorem aestronglyMeasurable_uncurry_omegaPart {α : ℝ} {k : ℕ} (n : ℕ) {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (omegaPart α k n G p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hbase : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aestronglyMeasurable_uncurry_HkIntegrand (α := α) (k := k) hsm).aemeasurable |>.aestronglyMeasurable
  have hind : AEStronglyMeasurable
      ((Omega n).indicator fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    hbase.indicator (Omega_measurable n)
  refine hind.congr ?_
  filter_upwards with p
  unfold omegaPart
  by_cases h : p ∈ Omega n <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- The `z`-a.e. measurability of the `Ω_n`-integral. -/
theorem aemeasurable_lintegral_omegaPart {α : ℝ} {k : ℕ} (n : ℕ) {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (omegaPart α k n G z θ)) (volume.restrict Work.Spaces.Iz) :=
  AEMeasurable.lintegral_prod_right'
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (f := fun p : ℝ × ℝ => ENNReal.ofReal (omegaPart α k n G p.1 p.2))
    (aestronglyMeasurable_uncurry_omegaPart (α := α) (k := k) n hsm).aemeasurable

/-! ## The bound on the `ℋᵏ`-square of the error -/

theorem HkSq_err_le (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.PhiStar.ThetaTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    {Cm RPb : ℝ} (hCm : 0 ≤ Cm) (hRPb : 0 ≤ RPb)
    (hmom : ∀ n : ℕ, 2 ≤ n →
      (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * ∑ m ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2))
        ≤ ENNReal.ofReal (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
    (hmem : ∀ n : ℕ, 3 ≤ n → Work.Spaces.HkMem α k (err n F))
    (hRP : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ)) ≤ ENNReal.ofReal RPb) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      Work.Spaces.HkSq α k (err n F)
        ≤ C * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
            + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
  obtain ⟨Ccrux, hCcruxpos, hcrux⟩ := theta_lintegral_le k α hα hα1
  have hCcrux : 0 ≤ Ccrux := hCcruxpos.le
  set κ : ℝ := Cm * (RPb + 1) with hκdef
  have hκ : 0 ≤ κ := by
    rw [hκdef]
    exact mul_nonneg hCm (by linarith)
  refine ⟨Ccrux * (1 + κ), by positivity, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hsmE : Work.FTS.EllipticEst.SmoothOpen (err n F) := EstAux.smoothOpen_err hsm hn1
  set E : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (err n F) z θ with hE
  set P : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (omegaPart α k n F z θ) with hP
  set Q : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
      * ∑ m ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2) with hQ
  set RP : ℝ≥0∞ := ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ) with hRPdef
  have hRPne : RP ≠ ⊤ := by
    rw [hRPdef]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRP
  set Tn : ℝ := (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal with hTn
  set Λn : ℝ := (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F with hΛn
  -- ## (1) the `θ`-slice identity
  have hslice : ∀ z ∈ Work.Spaces.Iz, ENNReal.ofReal (E z)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ) := by
    intro z hz
    rw [hE]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n hn).1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)
  -- ## (2) the estimate `EstMain.theta_lintegral_le` at each `z`
  have hstep : ∀ z ∈ Work.Spaces.Iz, ENNReal.ofReal (E z)
      ≤ ENNReal.ofReal Ccrux * (P z + Q z * RP) := by
    intro z hz
    rw [hslice z hz]
    exact hcrux n F hn hsm htr z hz
  -- ## (3) integrate over `z`
  have hPmeas : AEMeasurable P (volume.restrict Work.Spaces.Iz) := by
    rw [hP]
    exact aemeasurable_lintegral_omegaPart (α := α) (k := k) n hsm
  have hAfin : (∫⁻ z in Work.Spaces.Iz, P z) < ⊤ := by
    calc (∫⁻ z in Work.Spaces.Iz, P z)
        ≤ ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
          refine lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => lintegral_ofReal_omegaPart_le hF hz))
      _ = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
            (Filter.Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hlin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z))
      ≤ ENNReal.ofReal Ccrux
        * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP) := by
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z))
        ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal Ccrux * (P z + Q z * RP) :=
          lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hstep)
      _ = ENNReal.ofReal Ccrux
            * (∫⁻ z in Work.Spaces.Iz, (P z + Q z * RP)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal Ccrux
            * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z * RP)) := by
          rw [lintegral_add_left' hPmeas]
      _ = ENNReal.ofReal Ccrux
            * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP) := by
          rw [lintegral_mul_const' RP Q hRPne]
  -- ## (4) the two `z`-integrals
  have hPint : (∫⁻ z in Work.Spaces.Iz, P z)
      = ∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2) := by
    have hprod : (volume : Measure (ℝ × ℝ)).restrict Work.Spaces.Dom
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
      rw [Work.Spaces.Dom]
      exact (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := volume)
        Work.Spaces.Iz Work.Spaces.Iθ).symm
    have h1 : (∫⁻ z in Work.Spaces.Iz, P z)
        = ∫⁻ p, ENNReal.ofReal (omegaPart α k n F p.1 p.2) ∂(volume.restrict Work.Spaces.Dom) := by
      rw [hP, hprod]
      exact (MeasureTheory.lintegral_lintegral (μ := volume.restrict Work.Spaces.Iz)
        (ν := volume.restrict Work.Spaces.Iθ)
        (f := fun z θ : ℝ => ENNReal.ofReal (omegaPart α k n F z θ))
        (aestronglyMeasurable_uncurry_omegaPart (α := α) (k := k) n hsm).aemeasurable)
    have h2 : (∫⁻ p, ENNReal.ofReal (omegaPart α k n F p.1 p.2)
          ∂(volume.restrict Work.Spaces.Dom))
        = ∫⁻ p, (Omega n).indicator
            (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)) p
          ∂(volume.restrict Work.Spaces.Dom) := by
      refine lintegral_congr fun p => ?_
      unfold omegaPart
      by_cases h : p ∈ Omega n <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [h1, h2, lintegral_indicator (Omega_measurable n)]
    congr 1
    rw [Measure.restrict_restrict (Omega_measurable n), Set.inter_comm]
  have hQint : (∫⁻ z in Work.Spaces.Iz, Q z)
      ≤ ENNReal.ofReal (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
    have hI : (volume.restrict (Set.Ioi (0 : ℝ))) = volume.restrict Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.restrict_Ioi_eq_restrict_Ici
    rw [← hI, hQ]
    exact hmom n hn2
  -- ## (5) convert to real numbers
  have hHkSq : Work.Spaces.HkSq α k (err n F)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z)).toReal := by
    rw [hE, Work.Spaces.HkSq]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)
      (aemeasurable_integral_HkIntegrand (α := α) (k := k) hsmE).aestronglyMeasurable
  have hTn0 : 0 ≤ Tn := by rw [hTn]; exact ENNReal.toReal_nonneg
  have hΛ0 : 0 ≤ Λn := by
    rw [hΛn]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Work.Spaces.HkSq_nonneg α k F)
  rw [hHkSq, hTn, hΛn]
  have hmid1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z)).toReal
      ≤ Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
              * (RPb)) := by
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z)).toReal
        ≤ (ENNReal.ofReal Ccrux
            * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP)).toReal :=
          ENNReal.toReal_mono (by
            refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ne_of_lt (ENNReal.add_lt_top.mpr ⟨hAfin, ?_⟩))
            exact ENNReal.mul_lt_top (lt_of_le_of_lt hQint ENNReal.ofReal_lt_top)
              (lt_top_iff_ne_top.mpr hRPne))
            hlin
      _ = Ccrux * (((∫⁻ z in Work.Spaces.Iz, P z)
            + (∫⁻ z in Work.Spaces.Iz, Q z) * RP).toReal) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCcrux]
      _ ≤ Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
            + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
              * (RPb)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCcrux
          have hQb : (∫⁻ z in Work.Spaces.Iz, Q z).toReal
              ≤ Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
            refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hQint) ?_
            rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hCm
              (Real.rpow_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg n)) _))
              (Work.Spaces.HkSq_nonneg α k F))]
          have hRPb' : RP.toReal ≤ RPb := by
            refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hRP) ?_
            rw [ENNReal.toReal_ofReal hRPb]
          have hnn : 0 ≤ Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F :=
            mul_nonneg (mul_nonneg hCm (Real.rpow_nonneg
              (div_nonneg (by norm_num) (Nat.cast_nonneg n)) _))
              (Work.Spaces.HkSq_nonneg α k F)
          calc ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP).toReal
              ≤ (∫⁻ z in Work.Spaces.Iz, P z).toReal
                + ((∫⁻ z in Work.Spaces.Iz, Q z) * RP).toReal := ENNReal.toReal_add_le
            _ = (∫⁻ z in Work.Spaces.Iz, P z).toReal
                + (∫⁻ z in Work.Spaces.Iz, Q z).toReal * RP.toReal := by
                rw [ENNReal.toReal_mul]
            _ = (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (∫⁻ z in Work.Spaces.Iz, Q z).toReal * RP.toReal := by rw [hPint]
            _ ≤ (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
                  * (RPb) := by
                refine add_le_add le_rfl ?_
                calc (∫⁻ z in Work.Spaces.Iz, Q z).toReal * RP.toReal
                    ≤ (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
                      * RP.toReal := mul_le_mul_of_nonneg_right hQb ENNReal.toReal_nonneg
                  _ ≤ (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
                      * (RPb) := mul_le_mul_of_nonneg_left hRPb' hnn
  have h2 : 0 ≤ (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg n)) _)
      (Work.Spaces.HkSq_nonneg α k F)
  have hCκ : Cm * RPb ≤ κ := by
    rw [hκdef]
    nlinarith [mul_nonneg hCm hRPb]
  have haux : Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
          * (RPb))
      ≤ Ccrux * (1 + κ) * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
    have hTn1 : (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        ≤ (1 + κ) * (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal := by
      rw [add_mul, one_mul]
      exact le_add_of_nonneg_right (mul_nonneg hκ (ENNReal.toReal_nonneg))
    have hΛ1 : κ * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
        ≤ (1 + κ) * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
      rw [add_mul, one_mul]
      exact le_add_of_nonneg_left h2
    calc Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
          * (RPb))
        = Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + (Cm * (RPb)) * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * Work.Spaces.HkSq α k F)) := by ring
      _ ≤ Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + κ * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCcrux
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hCκ h2)
      _ ≤ Ccrux * (1 + κ) * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
          calc Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
              + κ * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
              ≤ Ccrux * ((1 + κ) * (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (1 + κ) * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)) :=
                mul_le_mul_of_nonneg_left (add_le_add hTn1 hΛ1) hCcrux
            _ = Ccrux * (1 + κ) * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by ring
  exact le_trans hmid1 haux

/-! ## The convergence of the `ℋᵏ`-norm of the error -/

theorem tendsto_HkSq_err (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.PhiStar.ThetaTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    {Cm RPb : ℝ} (hCm : 0 ≤ Cm) (hRPb : 0 ≤ RPb)
    (hmom : ∀ n : ℕ, 2 ≤ n →
      (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * ∑ m ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2))
        ≤ ENNReal.ofReal (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
    (hmem : ∀ n : ℕ, 3 ≤ n → Work.Spaces.HkMem α k (err n F))
    (hRP : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ)) ≤ ENNReal.ofReal RPb) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α k (err n F)) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hbnd⟩ := HkSq_err_le k α hα hα1 hsm hF htr hFs hCm hRPb hmom hmem hRP
  have hTn : Filter.Tendsto (fun n : ℕ => (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal)
      Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp (tendsto_lintegral_Omega hF)
  have hΛ : Filter.Tendsto (fun n : ℕ =>
      (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hcont : ContinuousAt (fun x : ℝ => x ^ (2 + Work.Spaces.eta)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr (by rw [Work.Spaces.eta]; norm_num))
    have h0 : (0 : ℝ) ^ (2 + Work.Spaces.eta) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    simpa [h0] using (hcont.tendsto.comp hbase).mul tendsto_const_nhds
  have hlim : Filter.Tendsto (fun n : ℕ => C * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
      + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
      Filter.atTop (nhds (C * (0 + 0))) :=
    Filter.Tendsto.const_mul C (hTn.add hΛ)
  rw [add_zero, mul_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with n
    exact Work.Spaces.HkSq_nonneg α k (err n F)
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact hbnd n hn

end Work.FTS.PhiStar.Honesty.CptApp
