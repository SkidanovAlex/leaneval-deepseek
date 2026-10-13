/-
# `FTS/ClassCHon/hkMem_zero_psiSeries_of_source`

**The level-`0` honesty and energy bound of the modal solution `Ψ = psiSeries α F` for a source
of the node's class** (no compact-support hypothesis):

  `HkMem α 0 (psiSeries α F) ∧ ∃ C > 0, HkSq α 0 (psiSeries α F) ≤ C · HkSq α 0 F`.

## Route

The two `HkMem` conjuncts are produced by

* `Work.FTS.ClassC.lintegral_psiTrunc_le` (per-mode energy + `ℓ²`-Cauchy–Schwarz + Bessel),
  giving the truncation bound `∫⁻_z ∫⁻_θ ofReal (Ψ_N² w² σ) ≤ ofReal (72 (∫θ σ) HkSq α 0 F)`
  uniformly in `N` — its inputs `hint`, `hintσ` are the slice integrabilities of `HkMem α 0 F`,
  and `hint_a`, `hper` are the two per-mode facts supplied by the sibling
  `perMode_data_of_source`;
* Fatou in the truncation parameter (`CmpSupp.lintegral_psiSeries_le_Iz`), using the pointwise
  convergence `psiTrunc → psiSeries` (`PhiStar.Honesty.psiTrunc_tendsto_psiSeries`, whose `L²`
  input `∫∫_{Q0} F² < ∞` is `PhiStar.integrableOn_sq_Q0_of_HkMem`);
* the capstone `ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone`, which turns the `∫⁻`-bound
  plus the three measurabilities (`meas_bundle_open`) and the weighted `ℓ¹`-summability of the
  radial coefficients (`hcoef_source_general`) into `HkMem α 0 Ψ`;
* `CmpSupp.hkSq_le_of_lintegral` converts the `∫⁻`-bound into the honest energy inequality.

The other inputs to `hF : HkMem α 7 F` are the smoothness descent
(`EllipticEst.TT.HkMem_descend_open`) and the single-slot extraction
(`EllipticEst.Cores.HkMem_zero_of_DzIter_slot`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone
import Submission.Work.FTS.ClassC.level0_psiTrunc
import Submission.Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable
import Submission.Work.FTS.PhiStar.Honesty.cmode_isLittleO_at_zero
import Submission.Work.FTS.ClassCHon.CmpSupp.lintegral_psiSeries_le_Iz
import Submission.Work.FTS.ClassCHon.CmpSupp.hkSq_le_of_lintegral
import Submission.Work.FTS.ClassCHon.CmpSupp.meas_bundle
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.ClassC.level0_psiSeries_concrete
import Submission.Work.FTS.ClassC.modeSum_muSeq_sum_le
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.Cores.HonSlot
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassCHon.meas_bundle_open
import Submission.Work.FTS.ClassCHon.aemeasurable_acoeff_of_source
import Submission.Work.FTS.ClassCHon.perMode_data_of_source
import Submission.Work.FTS.ClassCHon.hcoef_source_general

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "psiSeries" => Work.FTS.PhiStar.Series.psiSeries
local notation "psiTrunc" => Work.FTS.PhiStar.Series.psiTrunc
local notation "acoeff" => Work.FTS.PhiStar.Series.acoeff
local notation "cmode" => Work.FTS.PhiStar.Series.cmode
local notation "eNorm" => Work.EllipticEst.ModalSolution.eNorm

/-- `sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sEta θ :=
  Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hθ) _

/-- **The level-`0` honesty and energy bound of `psiSeries α F`, from the two per-mode facts,
the slice integrabilities, the coefficient summability and the three measurabilities.**

This is the whole analytic content of `hkMem_zero_psiSeries_of_source`; the wrapping theorem
below supplies its hypotheses from the source-side lemmas of the area. -/
theorem hkMem_zero_psiSeries_aux {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ)
    (hint_a : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun z => (acoeff α m F z) ^ 2 * (w z) ^ 2) Iz)
    (hper : ∀ m : ℕ, Work.FTS.ClassC.muSeq α m *
        Real.sqrt (∫ z in Iz, (acoeff α m F z) ^ 2 * (w z) ^ 2)
      ≤ Real.sqrt (∫ z in Iz,
          (Real.sqrt (eNorm m) * cmode m F z) ^ 2 * (w z) ^ 2))
    (hmeasT : ∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal ((psiTrunc α F N z θ) ^ 2 * (w z) ^ 2 * sEta θ))
      (MeasureTheory.volume.restrict Iz))
    (hslmeas : ∀ z ∈ Iz, AEMeasurable (fun θ : ℝ =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      (MeasureTheory.volume.restrict Iθ))
    (hmeasS : AEMeasurable (fun z : ℝ => ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |acoeff α m F z|)) :
    Work.Spaces.HkMem α 0 (psiSeries α F) ∧
      ∃ C : ℝ, 0 < C ∧ Work.Spaces.HkSq α 0 (psiSeries α F)
        ≤ C * Work.Spaces.HkSq α 0 F := by
  have hα1 : α ≤ 1 := by linarith
  -- ## the pointwise convergence of the truncations
  have hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.PhiStar.integrableOn_sq_Q0_of_HkMem hF0 hsm
  have hconv : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => psiTrunc α F N z θ) Filter.atTop
        (nhds (psiSeries α F z θ)) := fun z hz θ hθ =>
    Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries hα hα1 hmom hsm hL2 hz hθ
  -- ## nonnegativity of the source energy and of the angular mass
  have hHkSqF : 0 ≤ Work.Spaces.HkSq α 0 F := by
    rw [Work.Spaces.HkSq]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  have hσnn : 0 ≤ ∫ θ in Iθ, sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => sEta_nonneg_Iθ hθ)
  set e : ℝ := 72 * (∫ θ in Iθ, sEta θ) with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  set C₀ : ℝ := e * Work.Spaces.HkSq α 0 F with hC₀
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀]; exact mul_nonneg he0 hHkSqF
  -- ## the truncated `lintegral` bound, uniformly in `N`
  have hbd : ∀ N : ℕ, (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal ((psiTrunc α F N z θ) ^ 2 * (w z) ^ 2 * sEta θ))
        ≤ ENNReal.ofReal C₀ := by
    intro N
    have h1 := Work.FTS.ClassC.lintegral_psiTrunc_le α F N hsm hF0 hint hintσ
      (fun m _ => hint_a m) (μ := fun m => Work.FTS.ClassC.muSeq α m)
      (fun m => Work.FTS.ClassC.muSeq_pos hα hα4 m) (fun m _ => hper m)
    have h2 := Work.FTS.ClassC.modeSum_muSeq_sum_le α hα hα4 N
    have hK0 : 0 ≤ 9 * (∫ θ in Iθ, sEta θ) := by linarith
    have hS0 : 0 ≤ ∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have h3 : 9 * (∫ θ in Iθ, sEta θ) *
          (∑ m ∈ Finset.range (N + 1),
            (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2)
          * Work.Spaces.HkSq α 0 F ≤ C₀ := by
      rw [hC₀, he]
      have h8 : (∑ m ∈ Finset.range (N + 1),
            (((m : ℝ) + 1) / Work.FTS.ClassC.muSeq α m) ^ 2) ≤ 8 := h2
      nlinarith [hHkSqF, hσnn, hK0, hS0, h8]
    exact h1.trans (ENNReal.ofReal_le_ofReal h3)
  -- ## Fatou in the truncation parameter
  have hfinExpl : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal ((psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ))
        ≤ ENNReal.ofReal C₀ :=
    Work.FTS.ClassCHon.CmpSupp.lintegral_psiSeries_le_Iz hC₀nn hconv hmeasT hbd
  -- ## transfer to the `HkIntegrand` form used by the capstone
  have hz_eq : ∀ z : ℝ, (∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      = (∫⁻ θ in Iθ,
        ENNReal.ofReal ((psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ)) := by
    intro z
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq' hθ]
    rw [show w z ^ 2 * ((psiSeries α F z θ) ^ 2 * sEta θ)
        = (psiSeries α F z θ) ^ 2 * (w z) ^ 2 * sEta θ from by ring]
  have hfinIz : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal C₀ := by
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hz_eq)]
    exact hfinExpl
  have hfin : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal C₀ := by
    rw [MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact hfinIz
  -- ## the honesty of the series, and the energy bound
  have hmemΨ : Work.Spaces.HkMem α 0 (psiSeries α F) :=
    Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone hC₀nn hslmeas hfin hmeasS hcoef
  refine ⟨hmemΨ, ⟨e + 1, by linarith, ?_⟩⟩
  have hC₁ : 0 ≤ (e + 1) * Work.Spaces.HkSq α 0 F :=
    mul_nonneg (by linarith) hHkSqF
  have hfin₁ : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (psiSeries α F) z θ))
      ≤ ENNReal.ofReal ((e + 1) * Work.Spaces.HkSq α 0 F) := by
    refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hHkSqF]
  exact Work.FTS.ClassCHon.CmpSupp.hkSq_le_of_lintegral hC₁ hmemΨ hfin₁

theorem hkMem_zero_psiSeries_of_source {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α 1 F)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    Work.Spaces.HkMem α 0 (Work.FTS.PhiStar.Series.psiSeries α F) ∧
      ∃ C : ℝ, 0 < C ∧ Work.Spaces.HkSq α 0 (Work.FTS.PhiStar.Series.psiSeries α F)
        ≤ C * Work.Spaces.HkSq α 0 F := by
  -- ## descent in the order, and the extraction of the `z ∂_z F` slot
  have hsmForall : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hsm
  have hF0 : Work.Spaces.HkMem α 0 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 1) (by norm_num) hsmForall hF
  have hF1 : Work.Spaces.HkMem α 1 F := hF
  have hDz : Work.Spaces.HkMem α 0 (Work.Spaces.Dz F) :=
    Work.FTS.EllipticEst.Cores.HkMem_zero_of_DzIter_slot (k := 1) (i := 1) le_rfl hsm hF1
  -- ## the angular slice integrabilities of the source
  have hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hF0 hz
  have hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ :=
    fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem hF0 hz
  -- ## the two per-mode facts and the three measurabilities
  obtain ⟨hint_a, hper⟩ :=
    Work.FTS.ClassCHon.perMode_data_of_source hα hα4 hsm hF0 hF1 hmom
  obtain ⟨hmeasT, hslmeas, hmeasS⟩ :=
    Work.FTS.ClassCHon.meas_bundle_open
      (Work.FTS.ClassCHon.aemeasurable_acoeff_of_source hα hα4 hsm hF0 hF1)
  -- ## the weighted `ℓ¹`-summability of the radial coefficients
  exact hkMem_zero_psiSeries_aux hα hα4 hsm hF0 hmom hint hintσ hint_a hper hmeasT hslmeas
    hmeasS (Work.FTS.ClassCHon.hcoef_source_general hα hα4 hsm hF0 hF1 hDz hmom)

end Work.FTS.ClassCHon
