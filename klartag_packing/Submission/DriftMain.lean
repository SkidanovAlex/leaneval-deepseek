import Mathlib
import Submission.Good
import Submission.Moment
import Submission.LogDetV
import Submission.Commons.Analysis.Matrix.det_add_smul_one_eq_prod_eigenvalues

/-!
# The drift estimate of the exploration process

This file assembles the main drift bound of `Submission/PLAN_V7.md` §2 from

* `Submission.Good`: the measurable "good event" (a finite net of the unit sphere stays within
  the band `2r`), on which the quadratic form bound holds;
* `Submission.LogDetV`: the deterministic global second-order Taylor bound for `log det`;
* `Submission.Moment`: the two moment identities `E ⟪Id, H⟫ = 0` and `E ‖H‖² = ε² ∑ E N_k`.

The outcome is

    E log det A_K ≤ d log a₀ - ½ (a₀+2r)⁻² · E ‖H‖² + (error terms) .

`E ‖H‖²` is then bounded below by the contact estimate (see `Submission/PLAN_V8.md`).
-/

namespace Submission.DriftMain

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.MatBridge
open Submission.GenProc
open Submission.Contact
open Submission.OpNorm
open Submission.Good
open Submission.Moment
open Submission.LogDetV

noncomputable section

variable {d m : ℕ}

/-- The state `H = A_K - a₀·Id` of the process. -/
def HH (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) : MatV d :=
  stateK (projL R BoxL) a₀ ε K ω

lemma add_HH (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) :
    a₀ • oneV d + HH R BoxL a₀ ε K ω = proc (projL R BoxL) a₀ ε K ω K := by
  simp only [HH, stateK]
  abel

lemma isSymm_HH (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) : (matOf d (HH R BoxL a₀ ε K ω)).IsSymm := by
  simpa only [HH, stateK] using symm_state_sub (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
      (fun A => good_projL R BoxL A) K ω

lemma isHermitian_HH (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) : (matOf d (HH R BoxL a₀ ε K ω)).IsHermitian :=
  isHermitian_matOf _ (isSymm_HH R BoxL a₀ ε K ω)

lemma integrable_trace_HH (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ) (hε : 0 ≤ ε) :
    Integrable (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace) (sampleLaw d K) := by
  have h1 : Integrable (fun ω => inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K ω))
      (sampleLaw d K) := by
    refine MeasureTheory.Integrable.mono'
      (f := fun ω => inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K ω))
      (g := fun ω => ‖oneV d‖ * ‖stateK (projL R BoxL) a₀ ε K ω‖) ?_ ?_ ?_
    · exact (integrable_stateK_norm R BoxL a₀ ε K hε).const_mul _
    · exact (continuous_const.inner continuous_id).measurable.comp
        (measurable_stateK R BoxL a₀ ε K) |>.aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact abs_real_inner_le_norm _ _
  rw [show (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace)
      = fun ω => inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K ω) from
    funext fun ω => trace_state_eq_inner R BoxL a₀ ε K ω]
  exact h1

/-- **The log-determinant bound on the good event.** -/
theorem log_det_le_of_not_badNet (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε r : ℝ) (K : ℕ)
    (S : Finset (Vec d)) (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    {ω : Fin K → MatV d × MatV d} (hω : ω ∉ badNet R BoxL a₀ ε K S r)
    (ha₀ : 0 < a₀) (hr : 0 ≤ r) (har : 2 * r < a₀) :
    Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det
      ≤ (d : ℝ) * Real.log a₀ + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀
        - (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * ‖HH R BoxL a₀ ε K ω‖ ^ 2 := by
  have hspec : ∀ x : Vec d, |quadFormV (HH R BoxL a₀ ε K ω) x| ≤ (2 * r) * ‖x‖ ^ 2 := by
    intro x
    simpa only [HH, stateK] using
      quadFormV_bound_of_not_badNet R BoxL a₀ ε K S hSun hcover hω hr K le_rfl x
  have h := log_det_matOf_add_le (HH R BoxL a₀ ε K ω) (isSymm_HH R BoxL a₀ ε K ω)
    ha₀ (by linarith) har hspec
  simpa only [add_HH] using h

/-- **The drift estimate.**  Hypotheses `hE1`–`hE3` are the contributions of the bad event:
the bad part of the trace, of the norm square, and of the log determinant. -/
theorem integral_log_det_le (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε r E1 E2 E3 : ℝ) (K : ℕ)
    (S : Finset (Vec d)) (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    (ha₀ : 0 < a₀) (ha₁ : 1 ≤ a₀) (hε : 0 ≤ ε) (hr : 0 ≤ r) (har : 2 * r < a₀)
    (hintT : Integrable (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace) (sampleLaw d K))
    (hintN : Integrable (fun ω => ‖HH R BoxL a₀ ε K ω‖ ^ 2) (sampleLaw d K))
    (hintL : Integrable (fun ω => Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det)
      (sampleLaw d K))
    (hE1 : |∫ ω in (badNet R BoxL a₀ ε K S r), (matOf d (HH R BoxL a₀ ε K ω)).trace
              ∂(sampleLaw d K)| ≤ E1)
    (hE2 : ∫ ω in (badNet R BoxL a₀ ε K S r), ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) ≤ E2)
    (hE3 : ∫ ω in (badNet R BoxL a₀ ε K S r),
              Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ∂(sampleLaw d K) ≤ E3) :
    (∫ ω, Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ∂(sampleLaw d K))
      ≤ (d : ℝ) * Real.log a₀
        - (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * (∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
        + (E1 / a₀ + (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * E2 + E3) := by
  classical
  set bad := badNet R BoxL a₀ ε K S r with hbaddef
  set G : Set (Fin K → MatV d × MatV d) := badᶜ with hGdef
  have hbadm : MeasurableSet bad := measurableSet_badNet R BoxL a₀ ε K S r
  have hGm : MeasurableSet G := hbadm.compl
  set c : ℝ := (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 with hcdef
  set T : (Fin K → MatV d × MatV d) → ℝ := fun ω => (d : ℝ) * Real.log a₀
      + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀ - c * ‖HH R BoxL a₀ ε K ω‖ ^ 2 with hTdef
  -- integrability of `T`
  have hintT' : Integrable (fun ω => (d : ℝ) * Real.log a₀
      + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀) (sampleLaw d K) :=
    (integrable_const _).add (hintT.div_const a₀)
  have hintT2 : Integrable T (sampleLaw d K) := by
    have h := hintT'.sub (hintN.const_mul c)
    rwa [show ((fun ω => (d : ℝ) * Real.log a₀
          + (matOf d (HH R BoxL a₀ ε K ω)).trace / a₀) - fun x => c * ‖HH R BoxL a₀ ε K x‖ ^ 2)
        = T from by
          funext ω
          rw [Pi.sub_apply, hTdef]] at h
  -- pointwise bound on `G`
  have hpt : ∀ ω ∈ G, Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ≤ T ω := by
    intro ω hω
    have hωbad : ω ∉ bad := by simpa only [hGdef, Set.mem_compl_iff] using hω
    have := log_det_le_of_not_badNet R BoxL a₀ ε r K S hSun hcover hωbad ha₀ hr har
    simpa only [hTdef, hbaddef] using this
  -- split the total integral
  have hsplit : (∫ ω, Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ∂(sampleLaw d K))
      = (∫ ω in G, Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ∂(sampleLaw d K))
        + ∫ ω in bad, Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det
            ∂(sampleLaw d K) := by
    rw [← MeasureTheory.integral_add_compl hGm hintL, hGdef, compl_compl]
  -- monotonicity on `G`
  have hmono : (∫ ω in G, Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ∂(sampleLaw d K))
      ≤ ∫ ω in G, T ω ∂(sampleLaw d K) :=
    MeasureTheory.setIntegral_mono_on hintL.integrableOn hintT2.integrableOn hGm hpt
  -- the trace integral splits
  have htrsplit : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K))
      + (∫ ω in bad, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K))
      = ∫ ω, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K) := by
    rw [← MeasureTheory.integral_add_compl hGm hintT, hGdef, compl_compl]
  -- the norm-square integral splits
  have hnsplit : (∫ ω in G, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      + (∫ ω in bad, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      = ∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) := by
    rw [← MeasureTheory.integral_add_compl hGm hintN, hGdef, compl_compl]
  -- the trace has vanishing total integral
  have htrzero : (∫ ω, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) = 0 := by
    rw [show (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace)
        = fun ω => inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K ω) from
      funext fun ω => trace_state_eq_inner R BoxL a₀ ε K ω]
    exact integral_inner_oneV_state_eq_zero (d := d) R BoxL a₀ ε K hε
  -- evaluate the integral of `T` over `G`
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

  -- the measure of `G` is at most one
  have hGle : ((sampleLaw d K).real G) ≤ 1 := by
    have h1 : (sampleLaw d K).real G ≤ (sampleLaw d K).real Set.univ :=
      MeasureTheory.measureReal_mono (Set.subset_univ G) (MeasureTheory.measure_ne_top _ _)
    have h2 : (sampleLaw d K).real Set.univ = 1 := by
      rw [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one]
    linarith [h1, h2]
  -- assemble
  have hdlog : 0 ≤ (d : ℝ) * Real.log a₀ :=
    mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg ha₁)
  have hc_nonneg : 0 ≤ c := by
    rw [hcdef]; positivity
  rw [hsplit]
  refine le_trans (add_le_add hmono hE3) ?_
  rw [hTG]
  have htrb : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K))
      ≤ E1 := by
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
  have h2 : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) / a₀
      ≤ E1 / a₀ := by
    rw [div_eq_inv_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left htrb (by positivity)
  have hP : (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) / a₀
      = (1 / a₀) * (∫ ω in G, (matOf d (HH R BoxL a₀ ε K ω)).trace ∂(sampleLaw d K)) := by
    ring
  have h3 : ((d : ℝ) * Real.log a₀) * ((sampleLaw d K).real G) ≤ (d : ℝ) * Real.log a₀ := by
    simpa using mul_le_mul_of_nonneg_left hGle hdlog
  have h4 : -c * (∫ ω in G, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      ≤ -c * (∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K)) + c * E2 := by
    have h5 : (∫ ω, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
        = (∫ ω in G, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
          + ∫ ω in bad, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) := hnsplit.symm
    nlinarith [h5, hE2, hc_nonneg]
  nlinarith [h2, hP, h3, h4, hE2, hgt, hc_nonneg, hdlog]

end

end Submission.DriftMain
