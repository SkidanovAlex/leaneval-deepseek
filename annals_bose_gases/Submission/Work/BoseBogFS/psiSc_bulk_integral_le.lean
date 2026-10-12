import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBogFS.bulkAnnulusScalar
import Submission.Work.BoseBogFS.bulkETTLe
import Submission.Work.BoseBogFS.bulkPointwise
import Submission.Work.BoseBogFS.bulkRadialAnnulus
import Submission.Work.BoseBogFS.bulkTauLogRow
import Submission.Work.BoseBogFS.bulk_beta_arith
import Submission.Work.BoseBogFS.honestFsCutoffRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseBogFS.psiSc_bulk_integral_le` — the bulk integral row of the `I₁` comparison

The integral of the bulk comparison error `psiSc − fsI1Integrand` over the annulus
`{4c₁ < ‖t‖ ≤ T}` is bounded by an absolute constant times FS's error `lhyEps`.

The assembly is

* `bulkRow_pointwise`: on the annulus the error is at most the radial majorant
  `bulkRadial δ η B A c₁ ε_T T ‖t‖` with `δ = bogDelta R ℓ chiTC`,
  `η = bogEta v R ρ`, `B = bogBb R ℓ chiTC`, `A = 8π + ηT`;
* `bulk_radial_eq` (polar coordinates): the annulus integral of the majorant is
  `4π∫_{4c₁}^{T} r²G(r)dr`;
* `bulkAnnulusScalar` (proved in `bulkAnnulusScalar`): that one-dimensional integral is at
  most `δT³/3 + ηT⁴/2 + (B+ηT)(δT+ηT²) + A²(36c₁(log T − log 4c₁) + 12ε_T T)`;
* the `β`-block is FS's `ΔT³ + ηT⁴` row of `bulk_beta_arith` (hypothesis `hbeta`),
  the `36c₁ log` block is `bulkTauLogRow` and the `ε_T T` block is `bulkETTLe`.
-/

noncomputable section

theorem psiSc_bulk_integral_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ},
      0 < R → 0 < _root_.BoseGases.a v → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      Work.BoseBogFS.Core v R μ ρ →
      Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
        (_root_.BoseGases.a v) R ρ μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      Work.BoseBogFS.chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2 →
      R / Work.BoseFixR.ell v μ ≤ Work.BoseBogFS.chiTR1 →
      Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
          * (Work.BoseBogFS.bogT v R μ) ^ 3
        + Work.BoseBogFS.bogEta v R ρ * (Work.BoseBogFS.bogT v R μ) ^ 4
        ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
      MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBogFS.psiSc v h ρ μ t) →
      MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t) →
      (∫ t in {t : EuclideanSpace ℝ (Fin 3) | 4 * Work.BoseBogFS.bogC1 v ρ μ < ‖t‖ ∧
            ‖t‖ ≤ Work.BoseBogFS.bogT v R μ},
         (Work.BoseBogFS.psiSc v h ρ μ t -
          Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t))
        ≤ C * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  refine ⟨10 ^ 15, by norm_num, ?_⟩
  intro v h R ρ μ hR hav hv hvrad hv_supp hcore hreg hrl hcond hRle hbeta hInt1 hInt2
  -- ## abbreviations
  set c1 := bogC1 v ρ μ with hc1def
  set c2 := bogC2 v ρ μ with hc2def
  set T := bogT v R μ with hTdef
  set δ := bogDelta R (Work.BoseFixR.ell v μ) chiTC with hδdef
  set η := bogEta v R ρ with hηdef
  set B := bogBb R (Work.BoseFixR.ell v μ) chiTC with hBdef
  set eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTdef
  set E := Work.BoseB6.lhyEps (_root_.BoseGases.a v) R eT
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ with hEdef
  set A := 8 * Real.pi + η * T with hAdef
  -- ## the parameter facts of FS's regime
  have hρ0 : 0 < ρ := hcore.hρ0
  have hη0 : 0 ≤ η := by rw [hηdef]; exact hcore.hη0
  have hT0 : 0 < T := by rw [hTdef]; exact hcore.hTpos
  have heT0 : 0 ≤ eT := hreg.hε0
  have heT1 : eT ≤ 1 / 2 := hreg.hε1
  have hδ0 : 0 ≤ δ := by
    rw [hδdef, bogDelta]
    exact mul_nonneg (mul_nonneg (by positivity) chiTC_nonneg) (sq_nonneg _)
  have hc1pos : 0 < c1 := by
    rw [hreg.hc1val]
    have hKs : 0 < ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ :=
      inv_pos.mpr (mul_pos hreg.hKl hreg.hs)
    have hμρ : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hreg.hμ hρ0)
    exact mul_pos (mul_pos (by norm_num) hKs) hμρ
  have hc2pos : 0 < c2 := by
    rw [hreg.hc2val]
    have hKs : 0 < ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ :=
      inv_pos.mpr (mul_pos (mul_pos hreg.hKl hreg.hd) hreg.hs)
    have hμρ : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hreg.hμ hρ0)
    exact mul_pos (mul_pos (by norm_num) hKs) hμρ
  have hℓpos : 0 < Work.BoseFixR.ell v μ := by
    rw [hcore.hℓ]
    exact mul_pos hreg.hKl (Real.rpow_pos_of_pos (mul_pos hreg.hμ hav) _)
  have hE0 : 0 ≤ E := by
    rw [hEdef, hcore.hEeq]
    exact hcore.hE0
  have hA0 : 0 ≤ A := by rw [hAdef]; nlinarith [Real.pi_pos, hη0, hT0.le]
  have hBval : B = 8 * Real.pi + δ := by rw [hBdef, hδdef, bogBb, bogDelta]; ring
  have hAB : A ≤ B + η * T := by rw [hAdef, hBval]; linarith [hδ0]
  -- ## the uniform `β`-rows
  have hβc : ∀ t : E3, |betaSc v h ρ μ t - (8 * Real.pi + η * ‖t‖)| ≤ δ + 2 * η * ‖t‖ := by
    intro t
    have h1 := betaSc_close (v := v) (h := h) (R := R) (C := chiTC) (r₁ := chiTR1)
      (ρ := ρ) (μ := μ) hR hv hvrad hv_supp chiTC_nonneg chiTR1_pos hℓpos chiT_bound
      hRle hcond hρ0 hav hrl t
    rw [hδdef, hηdef]
    exact h1
  have hβu : ∀ t : E3, betaSc v h ρ μ t ≤ B + η * ‖t‖ := by
    intro t
    have h1 := betaSc_le (v := v) (h := h) (R := R) (C := chiTC) (r₁ := chiTR1)
      (ρ := ρ) (μ := μ) hR hv hvrad hv_supp chiTC_nonneg chiTR1_pos hℓpos chiT_bound
      hRle hcond hρ0 hav hrl t
    rw [hBdef, hηdef]
    exact h1
  have hηT : η * T ≤ 1 := by
    have hh := hreg.hηT
    rw [bogKernel_eta, bogKernel_T, max_eq_right hη0, max_eq_right hT0.le] at hh
    rw [hηdef, hTdef]
    exact hh
  have hbnn : ∀ t : E3, ‖t‖ ≤ T → 0 ≤ betaSc v h ρ μ t := by
    intro t ht
    refine betaSc_nonneg_of_small (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ)
      hR hv hvrad hv_supp hav hρ0 hrl hℓpos ?_
    have hRsqrt : R * Real.sqrt (ρ * _root_.BoseGases.a v) * T
        = η * T / (16 * Real.pi) := by
      rw [hηdef, bogEta]
      field_simp
    have h1 : R * Real.sqrt (ρ * _root_.BoseGases.a v) * ‖t‖
        ≤ R * Real.sqrt (ρ * _root_.BoseGases.a v) * T :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    rw [hRsqrt] at h1
    have h2 : η * T / (16 * Real.pi) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * Real.pi)]
      nlinarith [hηT, Real.pi_gt_three]
    linarith [h1, h2]
  -- ## the degenerate case
  by_cases hcase : T ≤ 4 * c1
  · have hemp : {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T} = ∅ := by
      ext t
      constructor
      · intro ht
        exact absurd ht (by rintro ⟨h1, h2⟩; linarith)
      · intro ht
        exact absurd ht (Set.notMem_empty t)
    rw [hemp, MeasureTheory.setIntegral_empty]
    exact mul_nonneg (by norm_num) hE0
  -- ## the bulk case
  · have hle : 4 * c1 ≤ T := (not_le.mp hcase).le
    have hpoint : ∀ t ∈ {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T},
        (psiSc v h ρ μ t - Work.BoseB6Est.fsI1Integrand (bogKernel v R ρ μ) eT c1 c2 t)
          ≤ bulkRadial δ η B A c1 eT T ‖t‖ := by
      intro t ht
      have h1 := bulkRow_pointwise (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ) (t := t)
        hR hv hvrad hav hρ0 heT0 heT1 hc1pos hc2pos (hbnn t ht.2) (hβc t) (hβu t)
        (le_of_lt ht.1) ht.2
      rw [← hδdef, ← hηdef, ← hTdef, ← hBdef, ← hc1def, ← hc2def, ← heTdef, ← hAdef] at h1
      exact h1
    -- integrability of the majorant
    have hSmeas : MeasurableSet {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T} := by measurability
    have hfin : (volume : Measure E3) {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T} < ⊤ := by
      refine lt_of_le_of_lt (measure_mono ?_)
        (isCompact_closedBall (0 : E3) T).measure_lt_top
      intro t ht
      simpa [Metric.mem_closedBall, dist_zero_right] using ht.2
    have hmeasG : Measurable (fun t : E3 => bulkRadial δ η B A c1 eT T ‖t‖) := by
      simp only [bulkRadial]
      measurability
    have hK0 : 0 ≤ B + η * T + A := by
      have hB0 : 0 ≤ B := by
        rw [hBdef, bogBb]
        have hcc : 0 ≤ chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 :=
          mul_nonneg chiTC_nonneg (sq_nonneg _)
        nlinarith [Real.pi_pos, hcc]
      linarith [hA0, hB0, hη0, hT0.le]
    have hMg : ∀ t ∈ {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T},
        ‖bulkRadial δ η B A c1 eT T ‖t‖‖
          ≤ (δ + 2 * η * T) * (1 + (B + η * T + A) / (2 * (4 * c1) ^ 2))
            + A ^ 2 * (36 * c1 / (4 * c1) ^ 3 + 12 * eT / (4 * c1) ^ 2) := by
      intro t ht
      have hGnn : 0 ≤ bulkRadial δ η B A c1 eT T ‖t‖ := by
        rw [bulkRadial]
        have h1 : 0 ≤ (δ + 2 * η * ‖t‖) * (1 + (B + η * T + A) / (2 * ‖t‖ ^ 2)) := by
          apply mul_nonneg
          · have h2η : 0 ≤ 2 * η * ‖t‖ :=
              mul_nonneg (mul_nonneg (by norm_num) hη0) (norm_nonneg t)
            linarith [hδ0]
          · have hq : 0 ≤ (B + η * T + A) / (2 * ‖t‖ ^ 2) := div_nonneg hK0 (by positivity)
            linarith
        have h2 : 0 ≤ A ^ 2 * (36 * c1 / ‖t‖ ^ 3 + 12 * eT / ‖t‖ ^ 2) := by
          apply mul_nonneg (sq_nonneg A)
          apply add_nonneg
          · exact div_nonneg (by linarith [hc1pos.le]) (by positivity)
          · exact div_nonneg (by linarith [heT0]) (by positivity)
        linarith [h1, h2]
      rw [Real.norm_of_nonneg hGnn, bulkRadial]
      have hd2 : (4 * c1) ^ 2 ≤ ‖t‖ ^ 2 := pow_le_pow_left₀ (by linarith) (le_of_lt ht.1) 2
      have hd3 : (4 * c1) ^ 3 ≤ ‖t‖ ^ 3 := pow_le_pow_left₀ (by linarith) (le_of_lt ht.1) 3
      have h1 : (δ + 2 * η * ‖t‖) * (1 + (B + η * T + A) / (2 * ‖t‖ ^ 2))
          ≤ (δ + 2 * η * T) * (1 + (B + η * T + A) / (2 * (4 * c1) ^ 2)) := by
        apply mul_le_mul
        · have h2η : 2 * η * ‖t‖ ≤ 2 * η * T :=
            mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (by norm_num) hη0)
          linarith
        · apply add_le_add le_rfl
          exact div_le_div_of_nonneg_left hK0 (by positivity) (by linarith [hd2])
        · have hq : 0 ≤ (B + η * T + A) / (2 * ‖t‖ ^ 2) := div_nonneg hK0 (by positivity)
          linarith
        · have h2η : 0 ≤ 2 * η * T := mul_nonneg (mul_nonneg (by norm_num) hη0) hT0.le
          linarith [hδ0]
      have h2 : A ^ 2 * (36 * c1 / ‖t‖ ^ 3 + 12 * eT / ‖t‖ ^ 2)
          ≤ A ^ 2 * (36 * c1 / (4 * c1) ^ 3 + 12 * eT / (4 * c1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
        apply add_le_add
        · exact div_le_div_of_nonneg_left (by linarith [hc1pos.le]) (by positivity)
            (by linarith [hd3])
        · exact div_le_div_of_nonneg_left (by linarith [heT0]) (by positivity)
            (by linarith [hd2])
      linarith [h1, h2]
    have hIg : IntegrableOn (fun t : E3 => bulkRadial δ η B A c1 eT T ‖t‖)
        {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T} := by
      refine IntegrableOn.of_bound hfin hmeasG.aestronglyMeasurable
        ((δ + 2 * η * T) * (1 + (B + η * T + A) / (2 * (4 * c1) ^ 2))
          + A ^ 2 * (36 * c1 / (4 * c1) ^ 3 + 12 * eT / (4 * c1) ^ 2)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with t ht
      exact hMg t ht
    have hIf : IntegrableOn (fun t : E3 => psiSc v h ρ μ t
        - Work.BoseB6Est.fsI1Integrand (bogKernel v R ρ μ) eT c1 c2 t)
        {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T} := by
      exact (hInt1.sub hInt2).integrableOn
    have hmono : (∫ t in {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T},
          (psiSc v h ρ μ t - Work.BoseB6Est.fsI1Integrand (bogKernel v R ρ μ) eT c1 c2 t))
        ≤ ∫ t in {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T}, bulkRadial δ η B A c1 eT T ‖t‖ :=
      MeasureTheory.setIntegral_mono_on hIf hIg hSmeas hpoint
    have hrad : (∫ t in {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T}, bulkRadial δ η B A c1 eT T ‖t‖)
        = 4 * Real.pi * (∫ r in Set.Ioc (4 * c1) T, r ^ 2 * bulkRadial δ η B A c1 eT T r) :=
      bulk_radial_eq (fun r => bulkRadial δ η B A c1 eT T r) (by linarith) hle
    -- ## the scalar evaluation
    have hscalar : (∫ r in Set.Ioc (4 * c1) T,
          r ^ 2 * ((δ + 2 * η * r) * (1 + (B + η * T + A) / (2 * r ^ 2))
            + A ^ 2 * (36 * c1 / r ^ 3 + 12 * eT / r ^ 2)))
        ≤ δ * T ^ 3 / 3 + η * T ^ 4 / 2 + (B + η * T) * (δ * T + η * T ^ 2)
          + A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T) :=
      bulkAnnulusScalar hc1pos heT0 hδ0 hη0 hA0 hAB hle
    have hβarith : δ * T ^ 3 / 3 + η * T ^ 4 / 2 + (B + η * T) * (δ * T + η * T ^ 2)
        ≤ 100 * E := by
      have hlong := bulk_beta_arith (v := v) (R := R) (ρ := ρ) (μ := μ)
        hR hav hρ0 hcond hreg hbeta
      rw [← hδdef, ← hηdef, ← hTdef, ← hBdef, ← hEdef] at hlong
      exact hlong
    have hlog : 36 * c1 * (Real.log T - Real.log (4 * c1)) ≤ (36 * 10 ^ 8 + 1) * E := by
      have hlong := bulkTauLogRow (v := v) (R := R) (ρ := ρ) (μ := μ)
        hR hav hρ0 hreg hcond hle
      rw [← hc1def, ← hTdef, ← hEdef] at hlong
      exact hlong
    have heTRow : eT * T ≤ (2 * 10 ^ 6 * (323 / 156)) * E := by
      have hlong := bulkETTLe (v := v) (R := R) (ρ := ρ) (μ := μ) hav hcore
      rw [← heTdef, ← hTdef, ← hEdef] at hlong
      exact hlong
    have hA2 : A ^ 2 ≤ 1089 := by
      have hAle : A ≤ 33 := by
        rw [hAdef]; linarith [Real.pi_lt_four, hηT]
      have h := pow_le_pow_left₀ hA0 hAle 2
      norm_num at h
      exact h
    have hX : δ * T ^ 3 / 3 + η * T ^ 4 / 2 + (B + η * T) * (δ * T + η * T ^ 2)
          + A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T)
        ≤ (100 + A ^ 2 * (36 * 10 ^ 8 + 1) + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156)))) * E := by
      have hA2nn : 0 ≤ A ^ 2 := sq_nonneg A
      have h2 : A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)))
          ≤ A ^ 2 * ((36 * 10 ^ 8 + 1) * E) :=
        mul_le_mul_of_nonneg_left hlog hA2nn
      have h3 : A ^ 2 * (12 * eT * T) ≤ A ^ 2 * (12 * ((2 * 10 ^ 6 * (323 / 156)) * E)) :=
        mul_le_mul_of_nonneg_left (by linarith [heTRow]) hA2nn
      have hkey : A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T)
          ≤ A ^ 2 * ((36 * 10 ^ 8 + 1) * E)
            + A ^ 2 * (12 * ((2 * 10 ^ 6 * (323 / 156)) * E)) := by
        rw [mul_add]
        exact add_le_add h2 h3
      calc δ * T ^ 3 / 3 + η * T ^ 4 / 2 + (B + η * T) * (δ * T + η * T ^ 2)
            + A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T)
          ≤ 100 * E + (A ^ 2 * ((36 * 10 ^ 8 + 1) * E)
              + A ^ 2 * (12 * ((2 * 10 ^ 6 * (323 / 156)) * E))) :=
            add_le_add hβarith hkey
        _ = (100 + A ^ 2 * (36 * 10 ^ 8 + 1)
              + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156)))) * E := by ring
    have hnum : 4 * Real.pi
        * (100 + A ^ 2 * (36 * 10 ^ 8 + 1) + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156))))
        ≤ 10 ^ 15 := by
      have h1 : A ^ 2 * (36 * 10 ^ 8 + 1) ≤ 1089 * (36 * 10 ^ 8 + 1) :=
        mul_le_mul_of_nonneg_right hA2 (by norm_num)
      have h2 : A ^ 2 * (2 * 10 ^ 6 * (323 / 156)) ≤ 1089 * (2 * 10 ^ 6 * (323 / 156)) :=
        mul_le_mul_of_nonneg_right hA2 (by norm_num)
      have hpos : 0 ≤ 100 + A ^ 2 * (36 * 10 ^ 8 + 1)
          + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156))) := by
        have hA2nn : 0 ≤ A ^ 2 := sq_nonneg A
        have hc1 : 0 ≤ (36 * 10 ^ 8 + 1 : ℝ) := by norm_num
        have hc2 : 0 ≤ (2 * 10 ^ 6 * (323 / 156) : ℝ) := by norm_num
        have hm1 : 0 ≤ A ^ 2 * (36 * 10 ^ 8 + 1) := mul_nonneg hA2nn hc1
        have hm2 : 0 ≤ A ^ 2 * (2 * 10 ^ 6 * (323 / 156)) := mul_nonneg hA2nn hc2
        linarith
      calc 4 * Real.pi * (100 + A ^ 2 * (36 * 10 ^ 8 + 1)
            + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156))))
          ≤ 16 * (100 + A ^ 2 * (36 * 10 ^ 8 + 1)
            + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156)))) :=
            mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) hpos
        _ ≤ 16 * (100 + 1089 * (36 * 10 ^ 8 + 1)
            + 12 * (1089 * (2 * 10 ^ 6 * (323 / 156)))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith [h1, h2]
        _ ≤ 10 ^ 15 := by norm_num
    have hbound : 4 * Real.pi * (δ * T ^ 3 / 3 + η * T ^ 4 / 2
          + (B + η * T) * (δ * T + η * T ^ 2)
          + A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T))
        ≤ 10 ^ 15 * E := by
      calc 4 * Real.pi * (δ * T ^ 3 / 3 + η * T ^ 4 / 2
            + (B + η * T) * (δ * T + η * T ^ 2)
            + A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T))
          ≤ 4 * Real.pi * ((100 + A ^ 2 * (36 * 10 ^ 8 + 1)
              + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156)))) * E) :=
            mul_le_mul_of_nonneg_left hX (by positivity)
        _ = (4 * Real.pi * (100 + A ^ 2 * (36 * 10 ^ 8 + 1)
              + 12 * (A ^ 2 * (2 * 10 ^ 6 * (323 / 156))))) * E := by ring
        _ ≤ 10 ^ 15 * E := mul_le_mul_of_nonneg_right hnum hE0
    calc (∫ t in {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T},
          (psiSc v h ρ μ t - Work.BoseB6Est.fsI1Integrand (bogKernel v R ρ μ) eT c1 c2 t))
        ≤ ∫ t in {t : E3 | 4 * c1 < ‖t‖ ∧ ‖t‖ ≤ T}, bulkRadial δ η B A c1 eT T ‖t‖ := hmono
      _ = 4 * Real.pi * (∫ r in Set.Ioc (4 * c1) T, r ^ 2 * bulkRadial δ η B A c1 eT T r) := hrad
      _ ≤ 4 * Real.pi * (δ * T ^ 3 / 3 + η * T ^ 4 / 2 + (B + η * T) * (δ * T + η * T ^ 2)
            + A ^ 2 * (36 * c1 * (Real.log T - Real.log (4 * c1)) + 12 * eT * T)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hunfold : (∫ r in Set.Ioc (4 * c1) T, r ^ 2 * bulkRadial δ η B A c1 eT T r)
              = (∫ r in Set.Ioc (4 * c1) T,
                  r ^ 2 * ((δ + 2 * η * r) * (1 + (B + η * T + A) / (2 * r ^ 2))
                    + A ^ 2 * (36 * c1 / r ^ 3 + 12 * eT / r ^ 2))) := by
            simp only [bulkRadial]
          rw [hunfold]
          exact hscalar
      _ ≤ 10 ^ 15 * E := hbound

end

end Work.BoseBogFS
