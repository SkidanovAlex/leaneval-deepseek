import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Psi0Est.exists_ZClass
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.level0_psiTrunc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- **The level-`0` honest estimate for the modal truncations.**

With `Ψ_N = psiTrunc α F N` and `a_m = acoeff α m F`, `c_m = cmode m F`,

  `∫⁻_z ∫⁻_θ ofReal (Ψ_N² w² σ) ≤ ofReal (9(∫θ σ)·(Σ_{m≤N}((m+1)/μ_m)²)·HkSq α 0 F)`.

The hypotheses are: the source in the honest class (`hsm`, `hmem`), the two slice
integrability conditions `hint`/`hintσ`, the integrability of `a_m² w²` for `m ≤ N`, and the
per-mode bounds `hper`. -/
theorem lintegral_psiTrunc_le (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ)
    (hint_a : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2) Iz)
    {μ : ℕ → ℝ} (hμ : ∀ m, 0 < μ m)
    (hper : ∀ m, m ≤ N → μ m *
        Real.sqrt (∫ z in Iz, (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)
      ≤ Real.sqrt (∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)) :
    (∫⁻ z in Iz, ∫⁻ θ in Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * Work.Spaces.HkSq α 0 F) := by
  -- the mode-sum bound
  have h1 : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.acoeff α m F z
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Iz,
                  (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2) :=
    lintegral_modeSum_le (fun m z => Work.FTS.PhiStar.Series.acoeff α m F z) N hint_a
  -- the ℓ²-Cauchy–Schwarz step with the per-mode bounds
  have h2 : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
        * Real.sqrt (∫ z in Iz,
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2
      ≤ (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * (∑ m ∈ Finset.range (N + 1),
              ∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) :=
    modeSum_arith (N := N)
      (a := fun m z => Work.FTS.PhiStar.Series.acoeff α m F z)
      (c := fun m z => Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
        * Work.FTS.PhiStar.Series.cmode m F z) hμ hper
  -- Bessel, integrated in `z`
  have h3 : (∑ m ∈ Finset.range (N + 1), ∫ z in Iz,
        (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)
      ≤ Work.Spaces.HkSq α 0 F := by
    have hsq : ∀ m ∈ Finset.range (N + 1), (∫ z in Iz,
          (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)
        = Work.EllipticEst.ModalSolution.eNorm m
          * ∫ z in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2 := by
      intro m _
      have hpt : ∀ z : ℝ, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2
          = Work.EllipticEst.ModalSolution.eNorm m
            * ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) := by
        intro z
        rw [mul_pow, Real.sq_sqrt (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))]
        ring
      calc (∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)
          = ∫ z in Iz, Work.EllipticEst.ModalSolution.eNorm m
              * ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) :=
            MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => hpt z)
        _ = Work.EllipticEst.ModalSolution.eNorm m
              * ∫ z in Iz, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2 :=
            MeasureTheory.integral_const_mul _ _
        _ = Work.EllipticEst.ModalSolution.eNorm m
              * ∫ z in Set.Ioi (0 : ℝ),
                  (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2 := by
            congr 1
            exact MeasureTheory.integral_Ici_eq_integral_Ioi
              (μ := MeasureTheory.volume) (x := (0 : ℝ))
    rw [Finset.sum_congr rfl hsq]
    exact sum_eNorm_cmode_sq_le_HkSq α F N hsm hmem hint hintσ
  -- the arithmetic
  have hK0 : 0 ≤ 9 * (∫ θ in Iθ, sEta θ) := by
    have h : 0 ≤ ∫ θ in Iθ, sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
    linarith
  have hS0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2 :=
    Finset.sum_nonneg (fun m _ => sq_nonneg _)
  have hAll : 9 * (∫ θ in Iθ, sEta θ)
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
            * Real.sqrt (∫ z in Iz,
                (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2
      ≤ 9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * Work.Spaces.HkSq α 0 F :=
    calc 9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Iz,
                  (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2
        ≤ 9 * (∫ θ in Iθ, sEta θ)
            * ((∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
              * (∑ m ∈ Finset.range (N + 1), ∫ z in Iz,
                  (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                    * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hK0
      _ = (9 * (∫ θ in Iθ, sEta θ)
              * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2))
            * (∑ m ∈ Finset.range (N + 1), ∫ z in Iz,
                (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                  * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) := by ring
      _ ≤ (9 * (∫ θ in Iθ, sEta θ)
              * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2))
            * Work.Spaces.HkSq α 0 F := mul_le_mul_of_nonneg_left h3 (mul_nonneg hK0 hS0)
      _ = 9 * (∫ θ in Iθ, sEta θ)
            * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
            * Work.Spaces.HkSq α 0 F := by ring
  exact le_trans h1 (ENNReal.ofReal_le_ofReal hAll)

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.besselZ_plain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.hcoef_psiSeries =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- The radial weight is at least `1` on the open half-line: `(1+t)²/z² ≥ 1`. -/
private lemma one_le_w {t : ℝ} (ht : 0 < t) : 1 ≤ Work.Spaces.w t := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- `z ^ (-1/2) = 1/√z` for `z > 0`. -/
private lemma rpow_neg_half_eq {z : ℝ} (hz : 0 < z) : z ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt z := by
  simp [Real.rpow_neg (le_of_lt hz), Real.sqrt_eq_rpow]

/-- The elementary arithmetic of the modal bound: the factor `(m+1)/(4m+5) ≤ 1/4` converts the
Green bound `√(∫c²)·z^(-1/2)/(α(4m+5)√m)` into `√(∫c²)/(4α√z√m)`. -/
private lemma modal_arith {α u z : ℝ} (hα : 0 < α) (hz : 0 < z) (hu : 0 ≤ u)
    {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * (u * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt m))
      ≤ u / (4 * α * Real.sqrt z * Real.sqrt m) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos (by linarith)
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos_of_pos hz
  have hstep : ((m : ℝ) + 1) * (u * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt m))
      = (((m : ℝ) + 1) / (4 * (m : ℝ) + 5)) * (u / (α * Real.sqrt m * Real.sqrt z)) := by
    rw [rpow_neg_half_eq hz]
    field_simp
  rw [hstep]
  have h2 : ((m : ℝ) + 1) / (4 * (m : ℝ) + 5) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
    linarith
  have h3 : 0 ≤ u / (α * Real.sqrt m * Real.sqrt z) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_right h2 h3) ?_
  rw [one_div]
  field_simp
  linarith

/-! ## The theorem -/

theorem hcoef_psiSeries {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F) :
    ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|) := by
  intro z hz
  -- ## the slice integrability facts required by the integrated Bessel inequality
  have hintc : ∀ t ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ : ℝ => (F t θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    fun t ht => integrableOn_sq_cos_of_HkMem hF ht
  have hints : ∀ t ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ : ℝ => (F t θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    fun t ht => integrableOn_sq_sEta_of_HkMem hF ht
  -- ## the mode energy of a fixed mode is a nonnegative integral
  have hAnn : ∀ m : ℕ, 0 ≤ ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 := by
    intro m
    refine integral_nonneg_of_ae ?_
    filter_upwards with t
    exact sq_nonneg _
  -- ## per-mode integrability of the weighted and unweighted squares of the mode coefficients
  have hWint : ∀ m : ℕ, IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    fun m => (Work.FTS.ClassCHon.Hcoef.cmode_L2_bound hsm hF m).1
  have hCint : ∀ m : ℕ, IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 0) := by
    intro m
    refine (hWint m).mono' ((Work.EllipticEst.ModalSolution.aesm_cmode hsm m).pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw2 : 1 ≤ (Work.Spaces.w t) ^ 2 := by
      have := one_le_w ht
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
        = (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
      _ = (Work.FTS.PhiStar.Series.cmode m F t * Work.Spaces.w t) ^ 2 := by ring
  have hWint' : ∀ m : ℕ, IntegrableOn
      (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0) := fun m =>
    (hWint m).congr_fun (fun t _ => by ring) measurableSet_Ioi
  -- ## the integrated Bessel inequality, with the two weights compared
  have hMaster : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m *
          (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
      ≤ Work.Spaces.HkSq α 0 F := by
    intro N
    refine le_trans (Finset.sum_le_sum ?_)
      (Work.FTS.ClassC.sum_eNorm_cmode_sq_le_HkSq α F N hsm hF hintc hints)
    intro m _
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))
    refine setIntegral_mono_on (hCint m) (hWint' m) measurableSet_Ioi ?_
    intro t ht
    have hw2 : 1 ≤ (Work.Spaces.w t) ^ 2 := by
      have := one_le_w ht
      nlinarith
    calc (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
        = (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
  -- ## `HkSq α 0 F` is nonnegative
  have hHkSq_nn : 0 ≤ Work.Spaces.HkSq α 0 F := by
    refine integral_nonneg_of_ae ?_
    filter_upwards with t
    refine integral_nonneg_of_ae ?_
    filter_upwards with θ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α F t θ]
    exact sq_nonneg _
  -- ## summability of the `eNorm`-weighted mode energy
  have hSumE : Summable (fun m : ℕ => Work.EllipticEst.ModalSolution.eNorm m *
      (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) := by
    refine summable_of_sum_range_le
      (f := fun m : ℕ => Work.EllipticEst.ModalSolution.eNorm m *
        (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2))
      (c := Work.Spaces.HkSq α 0 F) (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos n)) (hAnn n)
    · rcases n with _ | k
      · rw [Finset.range_zero, Finset.sum_empty]
        exact hHkSq_nn
      · simpa using hMaster k
  -- ## shift to `m = n + 1`, so that `1 ≤ m` throughout
  set En : ℕ → ℝ := fun n => Work.EllipticEst.ModalSolution.eNorm (n + 1) with hEndef
  set U : ℕ → ℝ := fun n =>
    Real.sqrt (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode (n + 1) F t) ^ 2) with hUdef
  have hUn : ∀ n : ℕ, U n = Real.sqrt (∫ t in Set.Ioi 0,
      (Work.FTS.PhiStar.Series.cmode (n + 1) F t) ^ 2) := fun n => congrFun hUdef n
  have hEn : ∀ n : ℕ, En n = Work.EllipticEst.ModalSolution.eNorm (n + 1) :=
    fun n => congrFun hEndef n
  have hUnn : ∀ n : ℕ, 0 ≤ U n := by
    intro n
    rw [hUn n]
    exact Real.sqrt_nonneg _
  have hEpos : ∀ n : ℕ, 0 < En n := by
    intro n
    rw [hEn n]
    exact Work.EllipticEst.ModalSolution.eNorm_pos (n + 1)
  have hEge : ∀ n : ℕ, (n : ℝ) + 1 ≤ En n := by
    intro n
    have h := (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds (n + 1)).2
    rw [hEn n]
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hUsq : ∀ n : ℕ, (U n) ^ 2 = ∫ t in Set.Ioi 0,
      (Work.FTS.PhiStar.Series.cmode (n + 1) F t) ^ 2 := by
    intro n
    rw [hUn n]
    exact Real.sq_sqrt (hAnn (n + 1))
  -- ## the shifted `eNorm`-weighted energy is summable
  have hAsum : Summable (fun n : ℕ => En n * (U n) ^ 2) := by
    refine ((summable_nat_add_iff (f := fun m : ℕ => Work.EllipticEst.ModalSolution.eNorm m *
      (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) 1).mpr hSumE).congr
      (fun n => ?_)
    rw [hEn n, hUsq n]
  -- ## the `1/(m·eNorm m)`-weighted sum is summable
  have hBsum : Summable (fun n : ℕ =>
      (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1))) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).mpr h0
      simpa only [Nat.cast_add, Nat.cast_one] using h1
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
    · positivity
    · have hEnn : 0 < En n := hEpos n
      have hs : Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)
          = Real.sqrt (En n * ((n : ℝ) + 1)) :=
        (Real.sqrt_mul (le_of_lt hEnn) _).symm
      have hsq : (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)) ^ 2
          = En n * ((n : ℝ) + 1) := by
        rw [hs, Real.sq_sqrt (by positivity)]
      have hle : ((n : ℝ) + 1) ^ 2 ≤ En n * ((n : ℝ) + 1) := by
        nlinarith [hEge n]
      rw [div_pow, one_pow, hsq]
      exact one_div_le_one_div_of_le (by positivity) hle
  -- ## the two factors whose product is `U n/√(n+1)`
  have ha2 : Summable (fun n : ℕ => (Real.sqrt (En n) * U n) ^ 2) := by
    refine hAsum.congr (fun n => ?_)
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEpos n)), hUsq n]
  have hAB : Summable (fun n : ℕ => (1 / 2) * (Real.sqrt (En n) * U n) ^ 2
      + (1 / 2) * (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1))) ^ 2) :=
    (ha2.mul_left (1 / 2)).add (hBsum.mul_left (1 / 2))
  -- ## Cauchy–Schwarz over the modes
  have hCSsum : Summable (fun n : ℕ => U n / Real.sqrt ((n : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hAB
    · positivity
    · have hEnpos : 0 < Real.sqrt (En n) := Real.sqrt_pos_of_pos (hEpos n)
      have hid : (Real.sqrt (En n) * U n) * (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)))
          = U n / Real.sqrt ((n : ℝ) + 1) := by
        rw [mul_one_div, mul_div_mul_left _ _ (ne_of_gt hEnpos)]
      rw [← hid]
      have hAM := two_mul_le_add_sq (Real.sqrt (En n) * U n)
        (1 / (Real.sqrt (En n) * Real.sqrt ((n : ℝ) + 1)))
      linarith
  -- ## the modal bound for the shifted family
  have hkey : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α (n + 1) F z|) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => (1 / (4 * α * Real.sqrt z)) * (U n / Real.sqrt ((n : ℝ) + 1)))
      (hCSsum.mul_left (1 / (4 * α * Real.sqrt z))) (fun n => ?_)
    have hgreen := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα (by linarith) (n + 1)
      (Nat.le_add_left 1 n)
      (c := fun t => Work.FTS.PhiStar.Series.cmode (n + 1) F t) (hCint (n + 1)) hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : |Work.FTS.PhiStar.Series.acoeff α (n + 1) F z| ≤ U n * z ^ (-(1 / 2) : ℝ)
        / (α * (4 * (((n + 1 : ℕ) : ℝ)) + 5) * Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
      have hg := hgreen
      rw [← hUn n] at hg
      simpa only [Work.FTS.PhiStar.Series.acoeff] using hg
    calc ((((n + 1 : ℕ) : ℝ)) + 1) * |Work.FTS.PhiStar.Series.acoeff α (n + 1) F z|
        ≤ ((((n + 1 : ℕ) : ℝ)) + 1) * (U n * z ^ (-(1 / 2) : ℝ)
            / (α * (4 * (((n + 1 : ℕ) : ℝ)) + 5)
              * Real.sqrt (((n + 1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ U n / (4 * α * Real.sqrt z * Real.sqrt (((n + 1 : ℕ) : ℝ))) :=
          modal_arith hα hz (hUnn n) (Nat.le_add_left 1 n)
      _ = (1 / (4 * α * Real.sqrt z)) * (U n / Real.sqrt ((n : ℝ) + 1)) := by
          push_cast
          ring
  exact (summable_nat_add_iff (f := fun m : ℕ =>
    ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|) 1).mp hkey

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.DiagSlices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

set_option linter.unusedVariables false





end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-`n` data of the corrected induction.**  `cs` is the Cauchy–Schwarz bound
consumed at level `n`; `coer` is the coercivity of the clean operator `Lhat` at level `n`,
stated on `RegQo α (n+1)` because the pairing `IP (Lhat f) f` sees the slots of `Lhat f`,
one order deeper than those of `f`. -/
structure CoerData2O (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQo α n f → RegQo α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `Lhat` at level `n` -/
  coer : ∀ f : Fn, RegQo α (n + 1) f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.FTS.CoercivityFix.Lhat f) f

/-- **The regularity ports the step needs.**  Every field says how `RegQo`-membership
descends when a derivative is taken, or that a slot of the operator/defect is at level `n`
when the argument is at level `n+1` or `n+2`; the last field records the one-sided
comparison of the `ℋⁿ`-norm with the `ℋ^{n+1}`-norm. -/
structure StepReg2O (α : ℝ) (n : ℕ) : Prop where
  /-- `RegQo α (n+2) f → RegQo α n f` -/
  mono1 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α n f
  /-- `RegQo α (n+2) f → RegQo α (n+1) f` -/
  mono2 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α (n + 1) f
  /-- `D_θ` drops the level by one -/
  dth1 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α (n + 1) (Work.Spaces.Dth f)
  /-- `D_z` drops the level by one -/
  dz1 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α (n + 1) (Work.Spaces.Dz f)
  /-- `D_θ` drops the level by two -/
  dth2 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α n (Work.Spaces.Dth f)
  /-- `D_z` drops the level by two -/
  dz2 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α n (Work.Spaces.Dz f)
  /-- `Lhat (D_z f)` is at level `n` when `f` is at level `n+2` -/
  ldz : ∀ f : Fn, RegQo α (n + 2) f →
    RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
  /-- the defect `Ê₂ f` is at level `n` when `f` is at level `n+1` -/
  e2r : ∀ f : Fn, RegQo α (n + 1) f → RegQo α n (Work.FTS.CoercivityFix.E2hat f)
  /-- one-sided comparison of the `ℋⁿ`-norms of the three slots with `|f|_{n+1}` -/
  normSub : ∀ f : Fn, RegQo α (n + 2) f →
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f

/-- **The algebraic inputs of the step, membership-free for the congruence.**  The
congruence of the concrete inner product in its *first* argument on the open quadrant needs
**no** regularity hypothesis (derivatives are local and the quadrant is co-null: see
`StepAssembly/H1IP_congr_qd`), and the two commutator identities are pointwise statements
on the open quadrant. -/
structure Comm2O (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, on the level-`n` class -/
  add : ∀ f₁ f₂ g : Fn, RegQo α n f₁ → RegQo α n f₂ → RegQo α n g →
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `D_θ` commutes with `Lhat` exactly -/
  dthC : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
  /-- the `D_z` commutator of `Lhat` is the explicit defect `Ê₂` -/
  dzC : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ


/-! ## The open-class data of the *transfer* induction -/

/-- **The level-`n` data of the transfer induction**: the Cauchy–Schwarz bound of `IP` at
level `n` (on `RegQo α n`), together with the coercivity of the paper's operator `𝓛_Γ^T`
at level `n` on the thin class `CoerAdmO`. -/
structure CoerDataTO (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQo α n f → RegQo α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `𝓛_Γ^T` at level `n`, on the one-condition class `CoerAdmO` -/
  coer : ∀ f : Fn, CoerAdmO α f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.Coercivity.LGammaT α f) f

/-- **The one-sided norm comparison of the coercivity step on the open class** — the open-class
analogue of `Assembly.hnormD_all`, with the constant `1` (so that it serves as the `hnormD`
hypothesis of `StepCoerO.step_coer_O` and `step2_data_ge_O`). -/
theorem hnormD_all_O (α : ℝ) (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) := by
  intro f hf
  rw [one_mul]
  exact Work.FTS.StrongPersist.HkSq_succ_le_SO (α := α) hα n hn
    (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hf.1 (n + 1)) hf.2.1


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.dz_four_RegQo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The one-sided norm comparison of the three slots, in the open class -/

/-- **The open-class `normSub`**: for `f` of class `SmoothOpen` and `HkMem α (n+1)`, the
level-`n` norms of the three slots `f`, `D_θ f`, `D_z f` are dominated by the level-`(n+1)`
norm of `f`.  This is `Assembly.V_bounds.normSub_Q` with the `D_z`-half taken from the
finite-order open-quadrant estimate `Transfer.HkSq_Dz_le_Q0Sm` (the two other halves are
smoothness-free). -/
theorem dzFour_normSub_SO (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (n + 1) f →
      Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
        ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
        ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  intro f hsm hmem
  exact ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hmem,
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hmem,
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hsm (n + 1)) hmem⟩

/-! ## Clairaut on the open quadrant -/

/-- `D_z` and `D_θ` commute at every point of the open quadrant, for a function which is
`C^∞` there: the derivatives are local and the point is interior to `Q0`, so that
`C²`-Schwarz applies.  (Only the *open* quadrant is needed, which is exactly the domain of
`SmoothOpen`; the frozen `Assembly.Dth_Dz_comm_mem` used `SmoothQuad` and had to treat the
boundary points `z = 0`, `sin 2θ = 0` separately.) -/
theorem dzFour_Dth_Dz_comm_Qd {v : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen v) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Spaces.Dz v) z θ = Work.Spaces.Dz (Work.Spaces.Dth v) z θ := by
  intro z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hzθ.2
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry v) (z, θ) :=
    (hs.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  exact (Work.Spaces.Dz_Dth_comm hcd).symm

/-! ## One step of the `D_z`-clause recursion, on the open class -/

/-- **One step of the `D_z`-clause recursion, on the open class** — the `RegQo` analogue of
`Assembly.dz_step`.  If the *first slot* pairing `⟨IP (D_z v), v⟩` is bounded by
`D·|v|²_{ℋ^{n+1}}` on `RegQo α (n+2)`, then the corresponding pairing of `HkIPStep c₁ c₂ IP` is
bounded by `3·D·max 1 (max c₁ c₂)` times the level-`(n+2)` norm on `RegQo α (n+3)`.

The only structural inputs are the open-class derivative ports (`regQo_dth_dz`), the open-class
one-sided norm comparison (`dzFour_normSub_SO`) and the pointwise commutation
`D_θ(D_z v) = D_z(D_θ v)` on the open quadrant (`dzFour_Dth_Dz_comm_Qd`), used through the
membership-free congruence of `IP` in its first argument. -/
theorem dzFour_dz_step_SO {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ D : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D)
    (hcongr : ∀ f f' g : Fn,
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g)
    (h : ∀ v : Fn, RegQo α (n + 2) v →
      |IP (Work.Spaces.Dz v) v| ≤ D * Work.Spaces.HkSq α (n + 1) v) :
    ∀ v : Fn, RegQo α (n + 3) v →
      |Work.Coercivity.HkIPStep c₁ c₂ IP (Work.Spaces.Dz v) v|
        ≤ (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by
  intro v hv
  have hv2 : RegQo α (n + 2) v := regQo_mono (by omega) hv
  have hdth : RegQo α (n + 2) (Work.Spaces.Dth v) := (regQo_dth_dz hα (n := n + 2) hv).1
  have hdz : RegQo α (n + 2) (Work.Spaces.Dz v) := (regQo_dth_dz hα (n := n + 2) hv).2
  have h0 := h v hv2
  have h1 := h (Work.Spaces.Dth v) hdth
  have h2 := h (Work.Spaces.Dz v) hdz
  -- the commutation, transported to the congruence class of `IP`
  have hcomm := dzFour_Dth_Dz_comm_Qd hv2.1
  have hcg := hcongr (Work.Spaces.Dth (Work.Spaces.Dz v))
    (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v) hcomm
  obtain ⟨hs0, hs1, hs2⟩ := dzFour_normSub_SO α hα (n + 1) v hv2.1 hv2.2.1
  have hB : 0 ≤ Work.Spaces.HkSq α (n + 2) v := Work.Spaces.HkSq_nonneg α (n + 2) v
  have e0 : |IP (Work.Spaces.Dz v) v| ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h0 (mul_le_mul_of_nonneg_left hs0 hD.le)
  have e1 : |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
      ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h1 (mul_le_mul_of_nonneg_left hs1 hD.le)
  have e2 : |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ D * Work.Spaces.HkSq α (n + 2) v :=
    le_trans h2 (mul_le_mul_of_nonneg_left hs2 hD.le)
  rw [Work.Coercivity.HkIPStep, hcg]
  have htri : |IP (Work.Spaces.Dz v) v
        + c₁ * IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)| :=
    Work.FTS.CoercivityFix.Assembly.abs_lin3_coef c₁ c₂ hc₁ hc₂ _ _ _
  refine le_trans htri ?_
  have hm1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hcomb : |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by
    have hc1 : c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        ≤ c₁ * (D * Work.Spaces.HkSq α (n + 2) v) := mul_le_mul_of_nonneg_left e1 hc₁.le
    have hc2 : c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
        ≤ c₂ * (D * Work.Spaces.HkSq α (n + 2) v) := mul_le_mul_of_nonneg_left e2 hc₂.le
    have hsum : |IP (Work.Spaces.Dz v) v|
        + c₁ * |IP (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v)|
        + c₂ * |IP (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
        ≤ D * Work.Spaces.HkSq α (n + 2) v
          + c₁ * (D * Work.Spaces.HkSq α (n + 2) v)
          + c₂ * (D * Work.Spaces.HkSq α (n + 2) v) := by
      linarith [e0, hc1, hc2]
    refine le_trans hsum ?_
    have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by linarith [hm1, hm2, hm3]
    have hDH : 0 ≤ D * Work.Spaces.HkSq α (n + 2) v := mul_nonneg hD.le hB
    calc D * Work.Spaces.HkSq α (n + 2) v
          + c₁ * (D * Work.Spaces.HkSq α (n + 2) v)
          + c₂ * (D * Work.Spaces.HkSq α (n + 2) v)
        = (1 + c₁ + c₂) * (D * Work.Spaces.HkSq α (n + 2) v) := by ring
      _ ≤ (3 * max 1 (max c₁ c₂)) * (D * Work.Spaces.HkSq α (n + 2) v) :=
          mul_le_mul_of_nonneg_right hcoef hDH
      _ = (3 * D * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 2) v := by ring
  exact hcomb

/-! ## The base estimate of the `D_z`-clause, on the open class -/

/-- **The base estimate of the `D_z`-clause on the open class.**  On `RegQo α 2` the pairing
of the first slot of `H1IP` with `D_z v` against `v` is dominated by the level-`1` norm of
`v`: the `z`-integration by parts `Coer1SO.wip_Dz_self_le_SO` converts each of the four
pairings into a square of a level-`1` slot.  This is `Assembly.H1IP_Dz_le_one` with the
smoothness weakened from `SmoothQuad` to `SmoothOpen`: the integrability certificates come
from `Coer1SO.IP2O_of` and the `z`-IBP packages from `Coer1SO.zibpO_of`. -/
theorem dzFour_H1IP_Dz_le_one_SO (α : ℝ) (hα : 0 < α) {v : Fn} (hv : RegQo α 2 v) :
    |Work.Coercivity.H1IP α (Work.Spaces.Dz v) v| ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 1 v := by
  obtain ⟨hs, hm, hb⟩ := hv
  have hp := Work.FTS.CoercivityFix.Coer1SO.IP2O_of α hα hs hm
  have hmem1 : Work.Spaces.HkMem α 1 v :=
    Work.FTS.OpenPkg.HkMem_mono_open hs 1 (by norm_num) hm
  have hηnn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
    fun θ hθ => Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hγnn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ :=
    fun θ hθ => Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hcomm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dth (Work.Spaces.Dz v) z θ = Work.Spaces.Dz (Work.Spaces.Dth v) z θ :=
    hp.dzDthComm.mono (fun _ hz => hz.mono (fun _ hθ => hθ.symm))
  -- the identifications of the boundary traces of the three functions
  have hm0 : Work.Spaces.mixed 0 0 v = v := by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
  have hmDz : Work.Spaces.mixed 1 0 v = Work.Spaces.Dz v := by
    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero]
  have hmDth : Work.Spaces.mixed 0 1 v = Work.Spaces.Dth v := by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero]
  -- the three `z`-integration-by-parts packages
  have hzibp_v : Work.FTS.CoercivityFix.Coer1SO.ZIBPO v :=
    Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs
      (fun θ hθ => by simpa only [hm0] using ((hb 0 0 (by norm_num)).1 θ hθ).1)
      (fun θ hθ => by simpa only [hm0] using ((hb 0 0 (by norm_num)).1 θ hθ).2)
      (hp.sqDzOne_zero.congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
          rcases p with ⟨z, θ⟩
          simp only [Function.uncurry_apply_pair]
          ring)))
      hp.intL_f_one
  have hzibp_Dz : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dz
      (fun θ hθ => by simpa only [hmDz] using ((hb 0 1 (by norm_num)).1 θ hθ).1)
      (fun θ hθ => by simpa only [hmDz] using ((hb 0 1 (by norm_num)).1 θ hθ).2)
      (hp.sqDzOne_one.congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
          rcases p with ⟨z, θ⟩
          simp only [Function.uncurry_apply_pair]
          ring)))
      hp.intL_Dz_one
  have hzibp_Dth : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dth v) :=
    Work.FTS.CoercivityFix.Coer1SO.zibpO_of hs.Dth
      (fun θ hθ => by simpa only [hmDth] using ((hb 1 0 (by norm_num)).1 θ hθ).1)
      (fun θ hθ => by simpa only [hmDth] using ((hb 1 0 (by norm_num)).1 θ hθ).2)
      (hp.sqDthOne.congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
          rcases p with ⟨z, θ⟩
          simp only [Function.uncurry_apply_pair]
          ring)))
      hp.intL_Dth_one
  -- the four pairings, in the `Rho`-normalisation
  have b1 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_Dz hηnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 hp.sqDzEta_one)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_Dz_eta
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have b2 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_v hηnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 hp.sqDzEta_zero)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_f_eta
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have hb3 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_v
      (σ := fun _ => (1 : ℝ)) (fun θ _ => zero_le_one)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.sqDzOne_zero
        (fun z θ => by ring))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_f_one
        (fun z θ => by ring))
  have b4 := Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO hzibp_Dth hγnn
      (Work.FTS.CoercivityFix.Coer1.to_h1 hp.sqDthGam)
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hp.intL_Dth_gam
        (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring))
  have b3 : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
        (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) v v := by
    rw [← Work.FTS.CoercivityFix.Assembly.wip_weight_congr
          (ρ := fun z θ => Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)
          (ρ' := fun z _ => Work.Spaces.w z ^ 2)
          (A := Work.Spaces.Dz v) (B := v) (fun z θ => by simp),
      ← Work.FTS.CoercivityFix.Assembly.wip_weight_congr
          (ρ := fun z θ => Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)
          (ρ' := fun z _ => Work.Spaces.w z ^ 2)
          (A := v) (B := v) (fun z θ => by simp)]
    exact hb3
  have hb4 : |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth v) (Work.Spaces.Dth v) := by
    have hEq : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)
        = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dz (Work.Spaces.Dth v)) (Work.Spaces.Dth v) :=
      Work.FTS.CoercivityFix.Assembly.wip_congr_ae'
        (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (g₁ := Work.Spaces.Dth (Work.Spaces.Dz v))
        (g₁' := Work.Spaces.Dz (Work.Spaces.Dth v)) (g₂ := Work.Spaces.Dth v) hcomm
    rw [hEq]
    exact b4
  have h1 : |Work.Coercivity.wip (fun z θ =>
        Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v)|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v) := by
    rw [Work.FTS.CoercivityFix.Assembly.wip_Rho_eq Work.Spaces.eta
        (Work.Spaces.Dz (Work.Spaces.Dz v)) (Work.Spaces.Dz v),
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta (Work.Spaces.Dz v)]
    exact b1
  have h2 : |Work.Coercivity.wip (fun z θ =>
        Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v := by
    rw [Work.FTS.CoercivityFix.Assembly.wip_Rho_eq Work.Spaces.eta (Work.Spaces.Dz v) v,
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta v]
    exact b2
  have h3 : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz v) v|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.EnOne v := by
    rw [← Work.FTS.CoercivityFix.Coer1.wip_one_self v]
    exact b3
  have h4 : |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v)|
      ≤ (5 / 2) * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α)
          (Work.Spaces.Dth v) := by
    rw [Work.FTS.CoercivityFix.Assembly.wip_Rho_eq (Work.Spaces.gam α)
        (Work.Spaces.Dth (Work.Spaces.Dz v)) (Work.Spaces.Dth v),
      ← Work.FTS.CoercivityFix.Coer1.wip_Rho_self (Work.Spaces.gam α) (Work.Spaces.Dth v)]
    exact hb4
  -- the `ℋ¹`-norm in terms of the three `En`-energies
  have hshape : Work.Spaces.HkSq α 1 v
      = Work.Coercivity.EfEta v + Work.Coercivity.EDz v + Work.Coercivity.EDth α v :=
    Work.FTS.StrongPersist.HkSq_one_eq_SO α hs hmem1
  have hnorm : Work.Spaces.HkSq α 1 v
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v
        + Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v)
        + Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth v) := by
    rw [hshape, Work.FTS.CoercivityFix.Coer1.EDz_eq_En v,
      Work.FTS.CoercivityFix.Coer1.EfEta_eq_En v, Work.FTS.CoercivityFix.Coer1.EDth_eq_En α v]
  have hE3le : Work.FTS.CoercivityFix.Coer1.EnOne v
      ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v :=
    Work.FTS.CoercivityFix.Coer1T.EnOne_le_En_eta (u := v) hp.sqDzOne_zero
      (Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.eta) hp.sqDzEta_zero)
  have hAnn1 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz v) :=
    Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have hAnn2 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta v :=
    Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have hAnn3 : 0 ≤ Work.FTS.CoercivityFix.Coer1.EnOne v :=
    Work.FTS.CoercivityFix.Coer1.EnOne_nonneg _
  have hAnn4 : 0 ≤ Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α)
      (Work.Spaces.Dth v) := Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  rw [Work.Coercivity.H1IP, hnorm]
  refine le_trans (Work.FTS.CoercivityFix.Assembly.abs_lin4_coef ((10 : ℝ)) ((10 : ℝ) ^ 10)
    ((10 : ℝ) ^ 17) ((10 : ℝ) ^ 21) (by norm_num) (by positivity) (by positivity)
    (by positivity) _ _ _ _) ?_
  nlinarith [h1, h2, h3, h4, hE3le, hAnn1, hAnn2, hAnn3, hAnn4]

/-! ## The `D_z`-clause of the level-four coercivity on the open class -/

theorem dz_four_RegQo {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Cdz : ℝ, 0 < Cdz ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 f →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.Spaces.Dz f) f| ≤ Cdz * Work.Spaces.HkSq α 4 f := by
  set E₁ : ℝ := 3 * (10 : ℝ) ^ 22 * max 1 (max c₁ c₂) with hE₁
  set E₂ : ℝ := 3 * E₁ * max 1 (max c₁' c₂') with hE₂
  set E₃ : ℝ := 3 * E₂ * max 1 (max c₁'' c₂'') with hE₃
  have hm₁ : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm₂ : (1 : ℝ) ≤ max 1 (max c₁' c₂') := le_max_left _ _
  have hm₃ : (1 : ℝ) ≤ max 1 (max c₁'' c₂'') := le_max_left _ _
  have hE₁pos : 0 < E₁ := by rw [hE₁]; nlinarith [hm₁]
  have hE₂pos : 0 < E₂ := by rw [hE₂]; nlinarith [hE₁pos, hm₂]
  have hE₃pos : 0 < E₃ := by rw [hE₃]; nlinarith [hE₂pos, hm₃]
  refine ⟨E₃, hE₃pos, ?_⟩
  intro α hα f hf
  have hlin : -(1 / 10 : ℝ) ≤ α := by linarith
  have v1 := dzFour_dz_step_SO (IP := Work.Coercivity.H1IP α) (n := 0) hα h₁ h₂
    (by norm_num : (0 : ℝ) < 10 ^ 22) (Work.FTS.IPGen.Comm2o_zero α).congr
    (fun v hv => dzFour_H1IP_Dz_le_one_SO α hα hv)
  have v2 := dzFour_dz_step_SO (IP := Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α) (n := 1)
    hα h₁' h₂' hE₁pos
    (Work.FTS.IPGen.Comm2o_one α hlin).congr
    (by intro v hv; rw [hE₁]; exact v1 v hv)
  have v3 := dzFour_dz_step_SO
    (IP := Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α) (n := 2)
    hα h₁'' h₂'' hE₂pos
    (Work.FTS.IPGen.Comm2o_two α hlin).congr
    (by intro v hv; rw [hE₂]; exact v2 v hv)
  have hv3 := v3 f hf
  simp only [Work.FTS.CoercivityFix.Assembly.IP4, Work.FTS.CoercivityFix.Assembly.IP3,
    Work.FTS.CoercivityFix.Assembly.IP2, hE₃] at hv3 ⊢
  simpa using hv3

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem fk_hkMem : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK f z) := by
  intro α _ f hsm hmem
  -- the angular moment is the radial function `u := Qang f 0`
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang f 0 z with hudef
  -- ## the a.e. identity `D_z^i (Qang f 0) = Qang f i` on `Iz`, `i ≤ 6`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 7,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang f i z := by
    filter_upwards [QangAe6 hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 7))]
  -- ## the per-slot integrability
  have hInt : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => (QangSq6Full (α := α) hsm hmem i hi).1.congr (htransfer i hi)
  have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  -- ## the angular weight is integrable
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  -- ## membership in `ℋ⁶`
  have hHkMem : Work.Spaces.HkMem α 6 (fun z θ => u z) := by
    constructor
    · intro z _
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 7) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun
          (f := fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 7,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## `FK f` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK f z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  rw [hfun]
  exact hHkMem

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsA2JetBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- NOTE (proof infrastructure): the statement below uses the notation `π` for `Real.pi`, so the
-- locale `Real` has to be opened.  (Without it the file does not even elaborate.)
open scoped Real

namespace Work.FTS.StrongPersist.L3Rhs

-- `VfsA2JetBound`: the `dthU`-jets `1 ≤ i ≤ 3` of the second angular factor
-- `VfsA2 α = -α·c₂(θ)·Γ(θ)/c(α)` of the separated part of `Vfs α` are dominated by `α·B` times
-- the jets `0 ≤ m ≤ 4` of `Γ/c = VfsGc α`.  (The factor `α` on the right is genuinely present:
-- it is the single `α` of `VfsA2`.)
-- Intended namespace `Work.FTS.StrongPersist.L3Rhs`
-- (file `Submission/Work/FTS/StrongPersist/L3Rhs/VfsA2JetBound.lean`).
-- The hypothesis `hc2` is the pointwise bound on the `dthU`-jets of `c₂` (supplied by
-- `Work.FTS.StrongPersist.L3Rhs.VfsTriglJetBounds`).
-- Route: on `U = Set.Ioo 0 (π/2)`, using
-- `Work.FTS.PhiStar.Psi0Est.dthU_iter_const_mul_eqOn` (to pull out `-α`) and
-- `Work.FTS.PhiStar.Psi0Est.dthU_iter_mul_eqOn`:
-- `dthU^[i](VfsA2 α) θ = -α Σ_{j≤i} C(i,j)·dthU^[j](c₂) θ·dthU^[i-j](VfsGc α) θ`; each term is
-- at most `C(i,j)·B·|dthU^[i-j](VfsGc α) θ|`, the last one (`i-j = 0`) being `|VfsGc α θ|`, and
-- `Σ_j C(i,j) ≤ 8` for `i ≤ 3`, so `C = 8` works.  `VfsGc α = Γ/c` is `C^∞` on `U`
-- (`Work.FTS.PhiStar.Psi0Defs.contDiffOn_Gam` + `ContDiffOn.div_const`, or
-- `Work.FTS.CoercivityFix.Transfer.Gam_contDiffOn_infty`), `c₂` is `C^∞` everywhere.
theorem VfsA2JetBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℝ), 0 < B →
        (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B) →
        ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ|
            ≤ C * B * α
              * (|Work.FTS.StrongPersist.L3Rhs.VfsGc α θ|
                + ∑ m ∈ Finset.Icc 1 4,
                    |Work.Spaces.dthU^[m] (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ|) := by
  refine ⟨8, by norm_num, ?_⟩
  intro B hB hc2 α hα hα1 i hi1 hi3 θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- ## Smoothness of the two angular factors on `U = (0, π/2)`
  have hc2sm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) Work.Construction.c2m
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    have h : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2) := by fun_prop
    refine h.contDiffOn.congr (fun t _ => ?_)
    rw [Work.Construction.c2m_eq]
  have hgcsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (VfsGc α)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.FTS.PhiStar.contDiffOn_Gam α).div_const _
  have hprodsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Construction.c2m * VfsGc α) (Set.Ioo (0 : ℝ) (π / 2)) := hc2sm.mul hgcsm
  -- ## The inner bound: every jet of order `≤ 3` of `VfsGc α` is dominated by `inner`
  set inner : ℝ := |VfsGc α θ|
      + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ| with hinner
  have hinner_nonneg : 0 ≤ inner := by
    rw [hinner]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun m _ => abs_nonneg _))
  have hgc_le : ∀ m : ℕ, m ≤ 3 → |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ inner := by
    intro m hm3
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [hinner]
      simp only [Function.iterate_zero, id_eq]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => abs_nonneg _))
    · have hmem : m ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hmpos, by omega⟩
      rw [hinner]
      exact le_trans
        (Finset.single_le_sum (s := Finset.Icc 1 4)
          (f := fun x => |Work.Spaces.dthU^[x] (VfsGc α) θ|)
          (fun x _ => abs_nonneg _) hmem)
        (le_add_of_nonneg_left (abs_nonneg _))
  -- ## The Leibniz expansion of the jets of `VfsA2 α = -α · (c₂ · VfsGc α)`
  have hfe : VfsA2 α = fun t : ℝ => -α * ((Work.Construction.c2m * VfsGc α) t) := by
    funext t; rw [VfsA2, Pi.mul_apply]; ring
  have hexp : Work.Spaces.dthU^[i] (VfsA2 α) θ
      = -α * ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) *
          (Work.Spaces.dthU^[a] Work.Construction.c2m θ
            * Work.Spaces.dthU^[i - a] (VfsGc α) θ) := by
    rw [hfe]
    rw [show Work.Spaces.dthU^[i]
          (fun t : ℝ => -α * ((Work.Construction.c2m * VfsGc α) t)) θ
        = -α * Work.Spaces.dthU^[i] (Work.Construction.c2m * VfsGc α) θ from by
      simpa using Work.FTS.PhiStar.Psi0Est.dthU_iter_const_mul_eqOn hU (-α) hprodsm i hθ]
    congr 1
    simpa using Work.FTS.PhiStar.Psi0Est.dthU_iter_mul_eqOn hU hc2sm hgcsm i hθ
  rw [hexp]
  set S : ℝ := ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) *
      (Work.Spaces.dthU^[a] Work.Construction.c2m θ
        * Work.Spaces.dthU^[i - a] (VfsGc α) θ) with hSdef
  -- ## Termwise bound of the binomial sum
  have hterm : ∀ a ∈ Finset.range (i + 1),
      |((i.choose a : ℕ) : ℝ) *
        (Work.Spaces.dthU^[a] Work.Construction.c2m θ
          * Work.Spaces.dthU^[i - a] (VfsGc α) θ)|
        ≤ ((i.choose a : ℕ) : ℝ) * (B * inner) := by
    intro a ha
    have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hchoose : (0 : ℝ) ≤ ((i.choose a : ℕ) : ℝ) := by positivity
    have hc2a : |Work.Spaces.dthU^[a] Work.Construction.c2m θ| ≤ B :=
      hc2 a (by omega) θ hθI
    have hgca : |Work.Spaces.dthU^[i - a] (VfsGc α) θ| ≤ inner := hgc_le (i - a) (by omega)
    have hprod : |Work.Spaces.dthU^[a] Work.Construction.c2m θ|
        * |Work.Spaces.dthU^[i - a] (VfsGc α) θ| ≤ B * inner :=
      mul_le_mul hc2a hgca (abs_nonneg _) (le_of_lt hB)
    rw [abs_mul, abs_of_nonneg hchoose, abs_mul]
    exact mul_le_mul_of_nonneg_left hprod hchoose
  have hS : |S| ≤ ∑ a ∈ Finset.range (i + 1),
      ((i.choose a : ℕ) : ℝ) * (B * inner) := by
    rw [hSdef]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hsum_eq : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) * (B * inner))
      = (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) * (B * inner) := by
    rw [Finset.sum_mul]
  -- ## The binomial sum is at most `2 ^ i ≤ 8`
  have hbin : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) ≤ 8 := by
    have hN : (∑ a ∈ Finset.range (i + 1), i.choose a) ≤ 8 := by
      have h2 : (∑ a ∈ Finset.range (i + 1), i.choose a) = 2 ^ i := Nat.sum_range_choose i
      rw [h2]
      calc 2 ^ i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hi3
        _ = 8 := by norm_num
    exact_mod_cast hN
  -- ## Assembly
  calc |-α * S| = α * |S| := by rw [abs_mul, abs_neg, abs_of_pos hα]
    _ ≤ α * (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) * (B * inner)) :=
        mul_le_mul_of_nonneg_left hS hα.le
    _ = α * ((∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) * (B * inner)) := by
        rw [hsum_eq]
    _ ≤ α * (8 * (B * inner)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbin (by positivity)) hα.le
    _ = 8 * B * α * inner := by ring

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux.gamJetMass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux

set_option autoImplicit false

/-! ## 1. `VfsGc` as a constant multiple of `Γ`, and the jet bound -/

/-- `VfsGc α = Γ/c = (c α)⁻¹ · Γ`, so its `dthU`-iterates are the `dthU`-iterates of `Γ`
scaled by `(c α)⁻¹`. -/
lemma dthU_iter_VfsGc_eq (α : ℝ) (i : ℕ) (θ : ℝ) :
    Work.Spaces.dthU^[i] (VfsGc α) θ
      = (Work.Spaces.c α)⁻¹ * Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ := by
  have h : VfsGc α = fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t := by
    funext t
    rw [VfsGc, div_eq_inv_mul]
  rw [h, Work.Spaces.dthU_iter_const_mul]

/-- **Quantitative jet bound.**  For `1 ≤ i ≤ 4` and `θ ∈ Iθ`,
`|dthU^[i] (Γ/c)| ≤ α · 10⁵ · (Γ/c)`.  The factor `α` is what makes the subsequent
`γ`-mass estimate uniform in `α`. -/
lemma abs_dthU_iter_VfsGc_le (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] (VfsGc α) θ| ≤ α * 100000 * VfsGc α θ := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i hi1 α hα 100000
    (fun θ' _ => Work.FTS.LocData.Tfun_abs_le (i - 1) (by omega) α hα hα1 θ')
  have hb : |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ α * 100000 * Work.Spaces.Gam α θ := hkey θ hθ
  rw [dthU_iter_VfsGc_eq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hcpos.le), VfsGc,
    div_eq_mul_inv]
  calc (Work.Spaces.c α)⁻¹
        * |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * 100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hcpos.le)
    _ = α * 100000 * (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹) := by ring

/-- On `Iθ`, `(Γ/c)² ≤ 100 Γ²` for `0 < α ≤ 1`. -/
lemma VfsGc_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (VfsGc α θ) ^ 2 ≤ 100 * Work.Spaces.Gam α θ ^ 2 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    linarith
  have h2 : ((Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hcpos.le) hinv 2
    nlinarith [h]
  rw [VfsGc, div_eq_mul_inv, mul_pow]
  calc Work.Spaces.Gam α θ ^ 2 * (Work.Spaces.c α)⁻¹ ^ 2
      ≤ Work.Spaces.Gam α θ ^ 2 * 100 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = 100 * Work.Spaces.Gam α θ ^ 2 := by ring

/-! ## 2. The pointwise domination by `α²·10¹²·sin(2θ)^{17α/30-1}` -/

/-- **Pointwise domination of the jet mass.**  For `1 ≤ i ≤ 4`, `0 < α ≤ 1` and `θ ∈ Iθ`,

`(dthU^[i] (Γ/c) θ)² sin(2θ)^{-γ(α)} ≤ α² · 10¹² · sin(2θ)^{17α/30-1}`,

where `17α/30 - 1 = 2α/3 - γ(α) ∈ (-1, 0]`. -/
lemma gamJet_pt_le (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hXg : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hX0 _
  have hXp : 0 ≤ (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := Real.rpow_nonneg hX0 _
  have hjet := abs_dthU_iter_VfsGc_le i hi1 hi4 α hα hα1 hθ
  have hD2 : (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
      ≤ (α * 100000) ^ 2 * (VfsGc α θ) ^ 2 := by
    rw [← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) hjet 2
    rwa [mul_pow] at h
  have hcx := VfsGc_sq_le α hα hα1 hθ
  have hgs := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
  have hstep1 : (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (VfsGc α θ) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hD2 hXg
  have hstep2 : ((α * 100000) ^ 2 * (VfsGc α θ) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcx (by positivity)) hXg
  have hstep4 : (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
    mul_le_mul_of_nonneg_left hgs (by positivity)
  have hbc : (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)) ≤ α ^ 2 * 10 ^ 12 := by
    have h2 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
    calc (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3))
        ≤ (α * 100000) ^ 2 * 100 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = α ^ 2 * 10 ^ 12 := by ring
  calc (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (VfsGc α θ) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep1
    _ ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep2
    _ = (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := hstep4
    _ = ((α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by ring
    _ ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) :=
        mul_le_mul_of_nonneg_right hbc hXp

/-! ## 3. Measurability -/

/-- `dthU^[m] g` is measurable whenever `g` is: `dthU` multiplies `deriv` by `sin(2·)`, and
`measurable_deriv` is unconditional. -/
lemma measurable_dthU_iter (g : ℝ → ℝ) (hg : Measurable g) (m : ℕ) :
    Measurable (Work.Spaces.dthU^[m] g) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id))).mul
        (measurable_deriv _)

/-- The integrand of `gamJetMass` is Borel measurable. -/
lemma measurable_gamJet (i : ℕ) (α : ℝ) :
    Measurable (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  have hg : Measurable (VfsGc α) := by
    have hfun : VfsGc α = fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α := by
      funext θ
      rw [VfsGc]
    rw [hfun]
    simp only [Work.Spaces.Gam]
    fun_prop
  have hJet : Measurable (Work.Spaces.dthU^[i] (VfsGc α)) := measurable_dthU_iter _ hg i
  have h1 : Measurable (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2) :=
    hJet.pow_const (2 : ℕ)
  have h2 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
    exact hsin.pow_const _
  exact h1.mul h2

/-! ## 4. The target -/

theorem gamJetMass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- The dominating function `α²·10¹²·sin(2θ)^{17α/30-1}` is integrable.
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ := hIntS.const_mul _
  -- Pointwise domination on `Iθ`.
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact gamJet_pt_le i hi1 hi4 α hα hα1 hθ
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) :=
    (measurable_gamJet i α).aestronglyMeasurable
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    hdom.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf hdom hpt
  calc ∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ,
          α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hmono
    _ = α ^ 2 * 10 ^ 12
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ α ^ 2 * 10 ^ 12 * (3000 / (17 * α)) :=
        mul_le_mul_of_nonneg_left hBdS' (by positivity)
    _ = 10 ^ 12 * 3000 * α / 17 := by field_simp
    _ ≤ 10 ^ 15 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17)]
        nlinarith [hα1]

end Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadSlotBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

/-
Intended namespace: `Work.FTS.StrongPersist.L3Rhs`.
The weighted slot bound for the radial product `z ↦ L₁₂(f)(z) · B(z)` (with `B` an arbitrary
radial factor that is `C⁴` on `(0,∞)` with `Zop`-jets of order `≤ 3` bounded by `24000`):
`∑_{q ≤ 3} (D_z^q (L₁₂ f · B))² w²` is integrable on `Iz` and its integral is bounded by
`C · HkSq α 4 f`.
Route: the Leibniz expansion `DzIter q (fun z _ => L₁₂ f z * B z) z 0
= Σ_{b ≤ q} C(q,b) · (Zop^[b] (L₁₂ f) z) · (Zop^[q-b] B z)` (all `z > 0`), which is
`Work.FTS.FinalClock.DzIter_mul_of_contDiffOn` with the multiplier `fun z => L₁₂ f z` (`C⁴`
on `(0,∞)` by `UopHk.contDiffOn_L12_k` at `k = 4`) and the second factor `fun z => B z`;
then `(D_z^q (L₁₂ f · B) z)² w z ² ≤ C · Σ_{b ≤ 3} (Zop^[b] (L₁₂ f) z)² w z ²`, and each
slot is integrable with integral `≤ C' · HkSq α 4 f` by
`Work.FTS.StrongPersist.L3Aux.L12f_slot_le` (needs `SmoothOpen f`, `HkMem α 4 f`,
`L12 f 0 = 0`, `α ≤ 1`, and slot order `≤ 4`).  `Work.Spaces.Zop_slice` identifies
`Zop^[b] (fun z => φ z)` with `DzIter b (fun z _ => φ z) · 0`.
-/
theorem VfsRadSlotBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (B : ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 → ContDiffOn ℝ 4 B (Set.Ioi (0 : ℝ)) →
    (∀ b ≤ 3, ∀ z ∈ Work.Spaces.Iz, |Work.Spaces.Zop^[b] B z| ≤ 24000) →
    MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Aux.L12f_slot_le
  refine ⟨1024 * 24000 ^ 2 * (4 * C₁) + 1, by positivity, ?_⟩
  intro α f B hα hα1 hsm hmem h0 hB4 hBbound
  have hL4 : ContDiffOn ℝ 4 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem (by norm_num)
  have hLq : ∀ q : ℕ, q ≤ 4 →
      ContDiffOn ℝ (q : ℕ∞) (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
    fun q hq => hL4.of_le (by simp [hq])
  have hBq : ∀ q : ℕ, q ≤ 4 → ContDiffOn ℝ (q : ℕ∞) B (Set.Ioi (0 : ℝ)) :=
    fun q hq => hB4.of_le (by simp [hq])
  have hslot := hC₁ α hα hα1 f hsm hmem h0
  -- ## the Leibniz expansion
  have hexp : ∀ q ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.Zop^[q - b] B z) := by
    intro q hq z hz
    have h1 : Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.DzIter (q - b) (fun z _ => B z) z 0) :=
      Work.FTS.FinalClock.DzIter_mul_of_contDiffOn q (fun z => Work.Construction.L12 f z)
        (fun z _ => B z) isOpen_Ioi (hLq q (by omega)) (hBq q (by omega)) z hz
    rw [h1]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [congrFun (Work.Spaces.Zop_slice (q - b) (fun z _ => B z) 0) z]
  -- ## the pointwise Cauchy–Schwarz bound
  have hpt : ∀ (X Y : ℕ → ℝ) (z : ℝ), z ∈ Set.Ioi (0 : ℝ) → (∀ j ≤ 3, |Y j| ≤ 24000) →
      (∀ q ≤ 3, Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (X b * Y (q - b))) →
      (∑ q ∈ Finset.range 4,
          (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ 1024 * 24000 ^ 2
            * ∑ b ∈ Finset.range 4, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro X Y z _ hY hex
    have hsq : ∀ q ≤ 3,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          ≤ 256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
      intro q hq
      rw [hex q hq]
      exact Work.FTS.StrongPersist.L3Rhs.VfsRadAux.sum_sq_binom_le q hq X Y hY
    have hsum : (∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2)
        ≤ 1024 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
      calc (∑ q ∈ Finset.range 4,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2)
          ≤ ∑ _q ∈ Finset.range 4,
              (256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2) :=
            Finset.sum_le_sum (fun q hq => hsq q (by rw [Finset.mem_range] at hq; omega))
        _ = 4 * (256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = 1024 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by ring
    calc (∑ q ∈ Finset.range 4,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = (∑ q ∈ Finset.range 4,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2)
              * (Work.Spaces.w z) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (1024 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2) * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
      _ = 1024 * 24000 ^ 2
            * ∑ b ∈ Finset.range 4, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          rw [← Finset.sum_mul]; ring
  -- ## abbreviations
  let X : ℕ → ℝ → ℝ := fun b z => Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
  let Y : ℕ → ℝ → ℝ := fun j z => Work.Spaces.Zop^[j] B z
  let G : ℝ → ℝ := fun z => ∑ b ∈ Finset.range 4, (X b z) ^ 2 * (Work.Spaces.w z) ^ 2
  let A : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 4,
      (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2
  have hAnn : ∀ z, 0 ≤ A z := fun z =>
    Finset.sum_nonneg (fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hApt : ∀ z ∈ Set.Ioi (0 : ℝ), A z ≤ 1024 * 24000 ^ 2 * G z := by
    intro z hz
    exact hpt (fun b => X b z) (fun j => Y j z) z hz
      (fun j hj => hBbound j hj z (Set.mem_Ici.mpr (le_of_lt hz)))
      (fun q hq => hexp q hq z hz)
  -- ## integrability of the majorant
  have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum (Finset.range 4)
      (f := fun b z => (X b z) ^ 2 * (Work.Spaces.w z) ^ 2) (fun b hb => ?_)
    have hb4 : b ≤ 4 := by rw [Finset.mem_range] at hb; omega
    refine MeasureTheory.IntegrableOn.congr_fun (hslot b hb4).1 (fun z _ => ?_) measurableSet_Ici
    show (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
    rw [← congrFun (Work.Spaces.Zop_slice b (fun z _ => Work.Construction.L12 f z) 0) z]
  -- ## the value of the majorant integral
  have hGval : (∫ z in Work.Spaces.Iz, G z) ≤ 4 * (C₁ * Work.Spaces.HkSq α 4 f) := by
    have hfun : G = fun z => ∑ b ∈ Finset.range 4,
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
      funext z
      show (∑ b ∈ Finset.range 4,
            (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
          = ∑ b ∈ Finset.range 4,
              (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
                * (Work.Spaces.w z) ^ 2
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← congrFun (Work.Spaces.Zop_slice b (fun z _ => Work.Construction.L12 f z) 0) z]
    rw [hfun]
    calc (∫ z in Work.Spaces.Iz, ∑ b ∈ Finset.range 4,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = ∑ b ∈ Finset.range 4,
            (∫ z in Work.Spaces.Iz,
              (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
                * (Work.Spaces.w z) ^ 2) :=
          MeasureTheory.integral_finsetSum (Finset.range 4)
            (fun b hb => (hslot b (by rw [Finset.mem_range] at hb; omega)).1)
      _ ≤ ∑ _b ∈ Finset.range 4, (C₁ * Work.Spaces.HkSq α 4 f) :=
          Finset.sum_le_sum (fun b hb =>
            (hslot b (by rw [Finset.mem_range] at hb; omega)).2)
      _ = 4 * (C₁ * Work.Spaces.HkSq α 4 f) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  -- ## the a.e. statements
  have hIzcongr : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
  have hae_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      A z ≤ 1024 * 24000 ^ 2 * G z := by
    rw [hIzcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hApt z hz)
  have hae_norm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖A z‖ ≤ 1024 * 24000 ^ 2 * G z := by
    rw [hIzcongr]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnn z)]
    exact hApt z hz
  have hAesm : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum hL4 hB4
  have hAint : MeasureTheory.IntegrableOn A Work.Spaces.Iz :=
    MeasureTheory.Integrable.mono' (hGint.const_mul (1024 * 24000 ^ 2)) hAesm hae_norm
  have hAle : (∫ z in Work.Spaces.Iz, A z)
      ≤ 1024 * 24000 ^ 2 * (∫ z in Work.Spaces.Iz, G z) := by
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (g := fun z => 1024 * 24000 ^ 2 * G z)
      (Filter.Eventually.of_forall hAnn) (hGint.const_mul (1024 * 24000 ^ 2)) hae_le
    rwa [MeasureTheory.integral_const_mul] at hmono
  refine ⟨hAint, ?_⟩
  have hS := Work.Spaces.HkSq_nonneg α 4 f
  calc (∫ z in Work.Spaces.Iz, A z)
      ≤ 1024 * 24000 ^ 2 * (∫ z in Work.Spaces.Iz, G z) := hAle
    _ ≤ 1024 * 24000 ^ 2 * (4 * (C₁ * Work.Spaces.HkSq α 4 f)) :=
        mul_le_mul_of_nonneg_left hGval (by positivity)
    _ = (1024 * 24000 ^ 2 * (4 * C₁)) * Work.Spaces.HkSq α 4 f := by ring
    _ ≤ (1024 * 24000 ^ 2 * (4 * C₁) + 1) * Work.Spaces.HkSq α 4 f := by nlinarith [hS]

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Rows.Rl1Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **`FK(F_* + f) = FK(F_*) + FK(f)` for `z > 0`**, from `SmoothOpen f` and `HkMem α 4 f`
alone: both θ-slices are integrable on `Iθ` (`Work.Stability.integrableOn_slice_Fstar` and
`GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`), so the Bochner integral splits
(`Work.FTS.GalFields.RHS.FK_add_of_slices`). -/
theorem FKaddOpen {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z →
      Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK f z :=
  fun z hz =>
    Work.FTS.GalFields.RHS.FK_add_of_slices (a := Work.Construction.Fstar α) (b := f)
      (ne_of_gt hz) (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hso hmem hz)

/-- `√(C_A/(γ-1)) = √(10·C_A)·α^{-1/2}`, since `γ - 1 = α/10`. -/
theorem sqrt_div_gam' {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) = Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hγ : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have h10 : (0 : ℝ) ≤ 10 * CA := by linarith
  have hsq : (Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ))) ^ 2 = CA / (Work.Spaces.gam α - 1) := by
    rw [mul_pow, Real.sq_sqrt h10, ← Real.rpow_two, ← Real.rpow_mul hα.le,
      show -(1 / 2 : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one, hγ]
    field_simp
  rw [← hsq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα.le _))]




/-- `√α·X ≤ Env α f`, `X = |f|_{ℋ⁴}`. -/
theorem sqrt_mul_le_Env {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt α * Work.FTS.Nonlin.Xn α f ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  rw [Work.FTS.NonlinRows.Rl1.Env]
  linarith


end Work.FTS_MuLamOK.Rows
end
