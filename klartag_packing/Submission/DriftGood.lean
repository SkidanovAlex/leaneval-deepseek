import Mathlib
import Submission.DriftMain

/-!
# The drift bound on the good event, without integrability of `log det`

`Submission.DriftMain.integral_log_det_le` bounds the *total* integral of
`log det A_K` and needs `Integrable (log det A_K)`.  For the existence of a good sample we only
need the *upper* bound, on the good set, of the second-order Taylor polynomial

    T = d log a₀ + tr H / a₀ - (1/2) (a₀ + 2r)⁻¹² ‖H‖²  ,     H = A_K - a₀·Id,

which is integrable for trivial reasons.  Since `log det A_K ≤ T` pointwise outside `badNet`,
a bound on `∫_{badNetᶜ} T` suffices.

This file proves exactly that, by the same computation as `DriftMain.integral_log_det_le`
(splitting the trace and the norm square at `badNet`, using that the total trace integral
vanishes) but without ever mentioning `log det`.
-/

namespace Submission.DriftGood

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.Contact
open Submission.OpNorm
open Submission.Good
open Submission.Moment
open Submission.DriftMain

noncomputable section

variable {d m : ℕ}

/-- **The Taylor polynomial integrated over the good set.**  On the complement of `badNet`, the
second-order Taylor polynomial `T` of `log det` at `a₀·Id` has integral at most

    d log a₀ + E1/a₀ + (1/2)(a₀+2r)⁻¹² E2 − (1/2)(a₀+2r)⁻¹² ∫‖H‖² .

Here `E1` bounds the bad part of the trace and `E2` the bad part of `‖H‖²`. -/
theorem setIntegral_T_le (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε r E1 E2 : ℝ) (K : ℕ)
    (S : Finset (Vec d))
    (ha₀ : 0 < a₀) (ha₁ : 1 ≤ a₀) (hε : 0 ≤ ε)
    (hintT : Integrable (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace) (sampleLaw d K))
    (hintN : Integrable (fun ω => ‖HH R BoxL a₀ ε K ω‖ ^ 2) (sampleLaw d K))
    (hE1 : |∫ ω in (badNet R BoxL a₀ ε K S r), (matOf d (HH R BoxL a₀ ε K ω)).trace
              ∂(sampleLaw d K)| ≤ E1)
    (hE2 : ∫ ω in (badNet R BoxL a₀ ε K S r), ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) ≤ E2) :
    (∫ ω in (badNet R BoxL a₀ ε K S r)ᶜ,
        ((d : ℝ) * Real.log a₀ + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀
          - (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * ‖HH R BoxL a₀ ε K ω‖ ^ 2) ∂(sampleLaw d K))
      ≤ (d : ℝ) * Real.log a₀ + E1 / a₀ + (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * E2
        - (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2
            * (∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K)) := by
  classical
  set bad := badNet R BoxL a₀ ε K S r with hbaddef
  set G : Set (Fin K → MatV d × MatV d) := badᶜ with hGdef
  have hbadm : MeasurableSet bad := measurableSet_badNet R BoxL a₀ ε K S r
  have hGm : MeasurableSet G := hbadm.compl
  set c : ℝ := (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 with hcdef
  set T : (Fin K → MatV d × MatV d) → ℝ := fun ω => (d : ℝ) * Real.log a₀
      + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀ - c * ‖HH R BoxL a₀ ε K ω‖ ^ 2 with hTdef
  have hintT' : Integrable (fun ω => (d : ℝ) * Real.log a₀
      + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀) (sampleLaw d K) :=
    (integrable_const _).add (hintT.div_const a₀)
  have htrsplit : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K))
      + (∫ ω in bad, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K))
      = ∫ ω, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K) := by
    rw [← MeasureTheory.integral_add_compl hGm hintT, hGdef, compl_compl]
  have hnsplit : (∫ ω in G, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      + (∫ ω in bad, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      = ∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) := by
    rw [← MeasureTheory.integral_add_compl hGm hintN, hGdef, compl_compl]
  have htrzero : (∫ ω, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) = 0 := by
    rw [show (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace)
        = fun ω => inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K ω) from
      funext fun ω => trace_state_eq_inner R BoxL a₀ ε K ω]
    exact integral_inner_oneV_state_eq_zero (d := d) R BoxL a₀ ε K hε
  have hTG : (∫ ω in G, T ω ∂(sampleLaw d K))
      = ((d : ℝ) * Real.log a₀) * ((sampleLaw d K).real G)
        + (1 / a₀) * (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K))
        - c * (∫ ω in G, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K)) := by
    have hcongr : (∫ ω in G, T ω ∂(sampleLaw d K))
        = ∫ ω in G, ((fun ω => (d : ℝ) * Real.log a₀
              + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀) ω
            - (fun ω => c * ‖HH R BoxL a₀ ε K ω‖ ^ 2) ω) ∂(sampleLaw d K) := by
      refine MeasureTheory.setIntegral_congr_fun hGm ?_
      intro ω _
      simp only [hTdef]
    rw [hcongr]
    rw [MeasureTheory.integral_sub (hintT'.integrableOn) ((hintN.const_mul c).integrableOn)]
    rw [MeasureTheory.integral_add (integrable_const _).integrableOn (hintT.div_const a₀).integrableOn]
    rw [MeasureTheory.setIntegral_const, MeasureTheory.integral_const_mul]
    have htrc : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀ ∂(sampleLaw d K))
        = a₀⁻¹ * (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) := by
      rw [show (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀)
          = fun ω => a₀⁻¹ • (matOf d (HH R BoxL a₀ ε K ω)).trace from by
        funext ω; rw [div_eq_inv_mul]; rfl]
      rw [MeasureTheory.integral_smul, smul_eq_mul]
    rw [htrc]
    simp only [smul_eq_mul]
    ring
  have hGle : ((sampleLaw d K).real G) ≤ 1 := by
    have h1 : (sampleLaw d K).real G ≤ (sampleLaw d K).real Set.univ :=
      MeasureTheory.measureReal_mono (Set.subset_univ G) (MeasureTheory.measure_ne_top _ _)
    have h2 : (sampleLaw d K).real Set.univ = 1 := by
      rw [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one]
    linarith [h1, h2]
  have hc_nonneg : 0 ≤ c := by rw [hcdef]; positivity
  have htrb : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) ≤ E1 := by
    have hthis : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K))
        = -(∫ ω in bad, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) := by
      linarith [htrsplit, htrzero]
    rw [hthis]
    linarith [(abs_le.mp hE1).1]
  have hgt : 0 ≤ ∫ ω in bad, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) :=
    MeasureTheory.setIntegral_nonneg hbadm fun ω _ => sq_nonneg _
  have hnsb : (∫ ω in G, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      ≤ (∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K)) := by
    linarith [hnsplit, hgt]
  have hdlog : 0 ≤ (d : ℝ) * Real.log a₀ :=
    mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg ha₁)
  rw [show (∫ ω in (badNet R BoxL a₀ ε K S r)ᶜ,
        ((d : ℝ) * Real.log a₀ + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀
          - (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * ‖HH R BoxL a₀ ε K ω‖ ^ 2) ∂(sampleLaw d K))
      = ∫ ω in G, T ω ∂(sampleLaw d K) from rfl, hTG]
  have h3 : ((d : ℝ) * Real.log a₀) * ((sampleLaw d K).real G) ≤ (d : ℝ) * Real.log a₀ :=
    by simpa using mul_le_mul_of_nonneg_left hGle hdlog
  have h2 : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) / a₀
      ≤ E1 / a₀ :=
    div_le_div_of_nonneg_right htrb (le_of_lt ha₀)
  have hP : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) / a₀
      = (1 / a₀) * (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) := by
    ring
  rw [hP] at h2
  have h4 : -c * (∫ ω in G, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      ≤ -c * (∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K)) + c * E2 := by
    nlinarith [hnsb, hE2, hc_nonneg]
  linarith [h3, h2, h4]

end

end Submission.DriftGood
