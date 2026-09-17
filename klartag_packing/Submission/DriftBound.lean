import Mathlib
import Submission.Moment
import Submission.DriftMain
import Submission.ContactBound

/-!
# The lower bound for the second moment of the state

See `Submission/PLAN_V9.md` §6b.  The state `H_K = A_K - a₀•Id` satisfies

    ∫‖H_K‖² = ε² ∑_{k<K} ∫ Nfun(A_k)        (`Moment.integral_norm_sq_state`)

and `Nfun A = dim F(A) ≥ (d(d+1) - |violSet A|)/2`
(`Contact.finrank_tangentSub_violSet_ge`).  Hence

    ∫‖H_K‖² ≥ (ε²/2)·(K·d(d+1) - ∑_{k<K} ∫|violSet A_k|) .

The whole drift estimate therefore reduces to bounding the total expected number of contacts
`∑_{k<K} E|violSet A_k|` — the subject of `PLAN_V9.md` §6b.
-/

namespace Submission.DriftBound

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.Contact
open Submission.ContactBound
open Submission.Moment
open Submission.OpNorm
open Submission.DriftMain

noncomputable section

variable {d m : ℕ}

/-- **The pointwise rank bound.** -/
lemma Nfun_ge_rank (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (hne : ∀ i, BoxL i ≠ 0) (hnegL : ∀ i, ∃ j, BoxL j = -BoxL i) (hR : 0 ≤ R)
    (A : MatV d) :
    (((d * (d + 1) : ℕ) : ℝ) - ((violSet R BoxL A).card : ℝ)) / 2 ≤ Nfun R BoxL A := by
  have h := finrank_tangentSub_violSet_ge R BoxL hne hnegL hR A
  have h1 : (((d * (d + 1) : ℕ) : ℝ))
      ≤ 2 * (Module.finrank ℝ ↥(tangentSub (violSet R BoxL A)) : ℝ)
        + ((violSet R BoxL A).card : ℝ) := by
    exact_mod_cast h
  simp only [Nfun]
  linarith

/-- Integrability of the number of contacts at an arbitrary time `k`. -/
lemma integrable_card_violSet_at (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (k : ℕ) :
    Integrable (fun ω : Fin K → MatV d × MatV d =>
      ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)) (sampleLaw d K) := by
  refine MeasureTheory.Integrable.mono'
    (g := fun _ : Fin K → MatV d × MatV d => (m : ℝ)) (integrable_const _) ?_ ?_
  · have h : (fun ω : Fin K → MatV d × MatV d =>
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ))
        = (cardOf BoxL) ∘ (fun ω => patt R BoxL (proc (projL R BoxL) a₀ ε K ω k)) :=
      funext fun ω => card_violSet_eq_cardOf R BoxL _
    rw [h]
    exact ((measurable_of_finite _).comp ((measurable_patt R BoxL).comp
      (measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
        (measurable_projL R BoxL) k))).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    refine Nat.cast_le.mpr ?_
    calc (violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card
        ≤ (Finset.univ.filter (fun i : Fin m => ‖BoxL i‖ ≤ R ∧
            quadFormV (proc (projL R BoxL) a₀ ε K ω k) (BoxL i) ≤ 1)).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The integral rank bound** at a single time `k`. -/
theorem integral_Nfun_lower (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (hne : ∀ i, BoxL i ≠ 0) (hnegL : ∀ i, ∃ j, BoxL j = -BoxL i) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) (k : Fin K) :
    (((d * (d + 1) : ℕ) : ℝ)
        - ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)) / 2
      ≤ ∫ ω : Fin K → MatV d × MatV d,
          Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω k) ∂(sampleLaw d K) := by
  have hpt : ∀ ω : Fin K → MatV d × MatV d,
      (((d * (d + 1) : ℕ) : ℝ)
          - ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)) / 2
        ≤ Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω k) :=
    fun ω => Nfun_ge_rank R BoxL a₀ ε K hne hnegL hR _
  have hcard : Integrable (fun ω : Fin K → MatV d × MatV d =>
      ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)) (sampleLaw d K) :=
    integrable_card_violSet_at R BoxL a₀ ε K k
  have hN : Integrable (fun ω : Fin K → MatV d × MatV d =>
      Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω k)) (sampleLaw d K) :=
    integrable_Nfun_comp R BoxL a₀ ε K k
  have hmono := MeasureTheory.integral_mono (((integrable_const _).sub hcard).div_const 2) hN hpt
  have hsplit : (∫ ω : Fin K → MatV d × MatV d,
      (((d * (d + 1) : ℕ) : ℝ)
        - ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)) / 2 ∂(sampleLaw d K))
      = (((d * (d + 1) : ℕ) : ℝ)
        - ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)) / 2 := by
    rw [MeasureTheory.integral_div]
    congr 1
    rw [MeasureTheory.integral_sub (integrable_const _) hcard]
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ]
  exact le_trans (le_of_eq hsplit.symm) hmono

/-- **The second moment, lower bound.**

`∫‖H_K‖² ≥ (ε²/2)·(K·d(d+1) − ∑_{k<K} ∫|violSet A_k|)`. -/
theorem integral_norm_sq_state_ge (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (hne : ∀ i, BoxL i ≠ 0) (hnegL : ∀ i, ∃ j, BoxL j = -BoxL i) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) :
    (ε ^ 2 / 2) * (((K : ℝ) * ((d * (d + 1) : ℕ) : ℝ))
        - ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K))
      ≤ ∫ ω : Fin K → MatV d × MatV d, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) := by
  simp only [HH]
  rw [Moment.integral_norm_sq_state R BoxL a₀ ε K hε]
  have hstep : (∑ k : Fin K,
        (((d * (d + 1) : ℕ) : ℝ)
          - ∫ ω : Fin K → MatV d × MatV d,
              ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)
                ∂(sampleLaw d K)) / 2)
      ≤ ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
          Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω k) ∂(sampleLaw d K) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have h := integral_Nfun_lower R BoxL a₀ ε K hne hnegL hR hε k
    linarith [h]
  have hsum : (∑ k : Fin K,
        (((d * (d + 1) : ℕ) : ℝ)
          - ∫ ω : Fin K → MatV d × MatV d,
              ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)
                ∂(sampleLaw d K)) / 2)
      = (1 / 2) * (((K : ℝ) * ((d * (d + 1) : ℕ) : ℝ))
        - ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at hstep
  have := mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ ε ^ 2)
  calc (ε ^ 2 / 2) * (((K : ℝ) * ((d * (d + 1) : ℕ) : ℝ))
        - ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K))
      = ε ^ 2 * ((1 / 2) * (((K : ℝ) * ((d * (d + 1) : ℕ) : ℝ))
        - ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)
              ∂(sampleLaw d K))) := by ring
    _ ≤ _ := this

/-- **The drift estimate, from the contact bound.**  Combining
`integral_norm_sq_state_ge` with `DriftMain.integral_log_det_le`: if the total expected number
of contacts is at most `M`, then the expected log-determinant of the final state is at most

    d·log a₀ − ½(a₀+2r)⁻²·( (ε²/2)(K·d(d+1) − M) ) + (bad-event errors) . -/
theorem integral_log_det_le_of_contact (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε r M E1 E2 E3 : ℝ)
    (K : ℕ) (S : Finset (Vec d)) (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    (ha₀ : 0 < a₀) (ha₁ : 1 ≤ a₀) (hε : 0 ≤ ε) (hr : 0 ≤ r) (har : 2 * r < a₀)
    (hne : ∀ i, BoxL i ≠ 0) (hnegL : ∀ i, ∃ j, BoxL j = -BoxL i) (hR : 0 ≤ R)
    (hintT : Integrable (fun ω => (matOf d (HH R BoxL a₀ ε K ω)).trace) (sampleLaw d K))
    (hintN : Integrable (fun ω => ‖HH R BoxL a₀ ε K ω‖ ^ 2) (sampleLaw d K))
    (hintL : Integrable (fun ω => Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det)
      (sampleLaw d K))
    (hE1 : |∫ ω in (Good.badNet R BoxL a₀ ε K S r), (matOf d (HH R BoxL a₀ ε K ω)).trace
              ∂(sampleLaw d K)| ≤ E1)
    (hE2 : ∫ ω in (Good.badNet R BoxL a₀ ε K S r), ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) ≤ E2)
    (hE3 : ∫ ω in (Good.badNet R BoxL a₀ ε K S r),
              Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ∂(sampleLaw d K) ≤ E3)
    (hcontact : ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K) ≤ M) :
    (∫ ω, Real.log (matOf d (proc (projL R BoxL) a₀ ε K ω K)).det ∂(sampleLaw d K))
      ≤ (d : ℝ) * Real.log a₀
        - (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * ((ε ^ 2 / 2) * (((K : ℝ) * ((d * (d + 1) : ℕ) : ℝ)) - M))
        + (E1 / a₀ + (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 * E2 + E3) := by
  have hN := integral_norm_sq_state_ge R BoxL a₀ ε K hne hnegL hR hε
  have hle : (K : ℝ) * ((d * (d + 1) : ℕ) : ℝ) - M
      ≤ (K : ℝ) * ((d * (d + 1) : ℕ) : ℝ)
        - ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K) := by
    linarith
  have hstep : (ε ^ 2 / 2) * (((K : ℝ) * ((d * (d + 1) : ℕ) : ℝ)) - M)
      ≤ ∫ ω : Fin K → MatV d × MatV d, ‖HH R BoxL a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K) :=
    le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) hN
  have hD := integral_log_det_le R BoxL a₀ ε r E1 E2 E3 K S hSun hcover ha₀ ha₁ hε hr har
    hintT hintN hintL hE1 hE2 hE3
  have hc : (0 : ℝ) ≤ (1 / 2) * (a₀ + 2 * r)⁻¹ ^ 2 := by positivity
  linarith [hD, hstep, hc, mul_le_mul_of_nonneg_left hstep hc]

end

end Submission.DriftBound
