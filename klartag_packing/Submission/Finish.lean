import Mathlib
import Submission.Main
import Submission.Commons.Lattice.Packing.rogers_conversion
import Submission.Commons.LinearAlgebra.Matrix.exists_linearMap_norm_sq_eq_sqrt_det

/-!
# The final assembly of Klartag's lattice sphere packing theorem

This file finishes the proof of `Submission.Helpers.klartag_lattice_large`:

* **S10** — existence of a *good sample*: a realisation of the exploration process on which the
  process stays in the `2r`-band around `a₀·Id`, no Gaussian increment is large, and
  `log det A_K ≤ Cg + 1 - 4 log d`;
* **S11** — the rescaling `A_K ↦ (1-θ)⁻¹ A_K` is `Λ`-free;
* **S12** — the lattice `Λ₁ = φ(Λ)` with `φ` the positive definite square root of `A`, whose
  covolume is `√(det A)·covol(Λ)`.
-/

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.Contact
open Submission.OpNorm
open Submission.Weight
open Submission.ContactFinal
open Submission.DriftMain
open Submission.Good
open Submission.Moment
open Submission.DriftBound
open Submission.Rescale
open Submission.Main
open Classical
open Commons.GeometryOfNumbers.Counting

set_option maxHeartbeats 4000000

namespace Submission.Finish

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d m : ℕ} {q : ℕ} {R : ℝ} {a : Fin d → ZMod q}

/-! ## Measurability and measure of the increment event -/

lemma measurableSet_incrEvent (d K : ℕ) (b : ℝ) : MeasurableSet (incrEvent d K b) := by
  have h : incrEvent d K b = ⋃ j : Fin K, {ω : Fin K → MatV d × MatV d | b < ‖(ω j).1‖} := by
    ext ω
    simp only [incrEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [h]
  exact MeasurableSet.iUnion fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).fst.norm)

/-- The number of steps, as a real number. -/
lemma KK_lt (d : ℕ) : (KK d : ℝ) < 16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1 := by
  have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 16 * (d:ℝ)^2 * Real.log (d:ℝ) from by
    have : (0:ℝ) ≤ Real.log (d:ℝ) := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd; simp
      · exact Real.log_nonneg (by exact_mod_cast hd)
    positivity)
  simpa only [KK] using h

lemma KK_le (d : ℕ) (hd : D0 ≤ d) :
    (KK d : ℝ) ≤ 17 * (d : ℝ) ^ 2 * Real.log (d : ℝ) := by
  have h1 := KK_lt d
  have h2 : (1:ℝ) ≤ (d:ℝ)^2 * Real.log (d:ℝ) := by
    have hd1 : 1 ≤ d := by simp only [D0] at hd; omega
    have hl : 1 ≤ Real.log (d:ℝ) := log_d_ge_one hd
    have hd1' : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
    nlinarith [hl, sq_nonneg ((d:ℝ) - 1)]
  nlinarith [h1, h2]

/-- `log d ≤ 2 √d`. -/
lemma log_le_two_sqrt (d : ℕ) (hd : D0 ≤ d) : Real.log (d:ℝ) ≤ 2 * Real.sqrt (d:ℝ) := by
  linarith [log_d_le_two_sqrt hd]

/-- `(K : ℝ) ≤ 17 d² log d`. -/
lemma KK_le' (d : ℕ) (hd : D0 ≤ d) : (KK d : ℝ) ≤ 17 * (d : ℝ) ^ 2 * Real.log (d : ℝ) :=
  KK_le d hd

/-- `(√d) ≥ 1632`. -/
lemma sqrt_d_ge (d : ℕ) (hd : D0 ≤ d) : (1632 : ℝ) ≤ Real.sqrt (d : ℝ) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  have h1 : (10:ℝ)^20 ≤ (d:ℝ) := by
    have := hd; simp only [D0] at this; exact_mod_cast this
  nlinarith [h1]

/-- `(K : ℝ) ≤ exp (d/2)`. -/
lemma KK_le_exp (d : ℕ) (hd : D0 ≤ d) : (KK d : ℝ) ≤ Real.exp ((d:ℝ)/2) := by
  have h1 : (KK d : ℝ) ≤ 17 * (d:ℝ)^2 * Real.log (d:ℝ) := KK_le d hd
  have hl := log_le_two_sqrt d hd
  have hs := sqrt_d_ge d hd
  have hsd : Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) = (d:ℝ) := Real.mul_self_sqrt (by positivity)
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by
    have : (10:ℝ)^20 ≤ (d:ℝ) := by
      have := hd; simp only [D0] at this; exact_mod_cast this
    linarith
  have h2 : 17 * (d:ℝ)^2 * Real.log (d:ℝ) ≤ (d:ℝ)^3 / 48 := by
    have h3 : 17 * (d:ℝ)^2 * Real.log (d:ℝ) ≤ 17 * (d:ℝ)^2 * (2 * Real.sqrt (d:ℝ)) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    have hA : 17 * (d:ℝ)^2 * (2 * Real.sqrt (d:ℝ))
        = 34 * ((d:ℝ)^2 * Real.sqrt (d:ℝ)) := by ring
    refine h3.trans (le_of_eq hA) |>.trans ?_
    have h4 : 34 * Real.sqrt (d:ℝ) ≤ (d:ℝ) / 48 := by nlinarith [hs, hsd]
    calc 34 * ((d:ℝ)^2 * Real.sqrt (d:ℝ)) = (d:ℝ)^2 * (34 * Real.sqrt (d:ℝ)) := by ring
      _ ≤ (d:ℝ)^2 * ((d:ℝ)/48) := mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
      _ = (d:ℝ)^3 / 48 := by ring
  have h6 : (d:ℝ)^3 / 48 ≤ Real.exp ((d:ℝ)/2) := by
    have h7 := Real.pow_div_factorial_le_exp ((d:ℝ)/2) (by positivity) 3
    rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num] at h7
    have h8 : ((d:ℝ)/2)^3 / 6 = (d:ℝ)^3 / 48 := by ring
    rwa [h8] at h7
  linarith [h1, h2, h6]

lemma two_pow_eq_exp (d : ℕ) :
    (2:ℝ)^(d*d) = Real.exp ((d:ℝ)^2 * Real.log 2) := by
  have h := Real.exp_nat_mul (Real.log 2) (d*d)
  rw [Real.exp_log (show (0:ℝ) < 2 by norm_num)] at h
  rw [← h]
  congr 1
  push_cast
  ring

lemma incrEvent_measure_le (d : ℕ) (hd : D0 ≤ d) :
    (sampleLaw d (KK d)).real (incrEvent d (KK d) (2 * (d:ℝ))) ≤ Real.exp (-(d:ℝ)) := by
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have h0 := Rescale.incrEvent_measureReal_le d (KK d) (b := 2 * (d:ℝ)) (by positivity)
  refine h0.trans ?_
  have hlog2 : Real.log 2 ≤ 3 / 4 :=
    le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num : (0.6931471808 : ℝ) < 3 / 4))
  have hfac : (2:ℝ)^(d*d) * Real.exp (-(3/8) * (2*(d:ℝ))^2) ≤ Real.exp (-(3/4) * (d:ℝ)^2) := by
    rw [two_pow_eq_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -(3/8 : ℝ) * (2*(d:ℝ))^2 = -(3/2) * (d:ℝ)^2 := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hlog2 (sq_nonneg (d:ℝ))
    nlinarith [h2]
  have hfacnn : 0 ≤ (2:ℝ)^(d*d) * Real.exp (-(3/8) * (2*(d:ℝ))^2) := by positivity
  have hfin : Real.exp ((d:ℝ)/2) * Real.exp (-(3/4) * (d:ℝ)^2) ≤ Real.exp (-(d:ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [show (2:ℝ) ≤ (d:ℝ) by exact_mod_cast hd2]
  calc (KK d : ℝ) * ((2:ℝ)^(d*d) * Real.exp (-(3/8) * (2*(d:ℝ))^2))
      ≤ Real.exp ((d:ℝ)/2) * Real.exp (-(3/4) * (d:ℝ)^2) :=
        mul_le_mul (KK_le_exp d hd) hfac hfacnn (Real.exp_nonneg _)
    _ ≤ Real.exp (-(d:ℝ)) := hfin

/-! ## Bounds on the state and on the Taylor polynomial -/

/-- The state is bounded by the increments. -/
lemma norm_HH_le (ω : Fin (KK d) → MatV d × MatV d)
    (hξ : ∀ j : Fin (KK d), ‖(ω j).1‖ ≤ 2 * (d:ℝ)) (hd : D0 ≤ d) :
    ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ≤ 34 * (d:ℝ) * Real.log (d:ℝ) := by
  have hd1 : 1 ≤ d := by simp only [D0] at hd; omega
  have hε : (0:ℝ) ≤ eps d := (eps_pos d (by omega)).le
  have hpos : (0:ℝ) < (d:ℝ) := by
    have h : (10:ℝ)^20 ≤ (d:ℝ) := by
      have := hd; simp only [D0] at this; exact_mod_cast this
    linarith
  have h1 : ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖
      ≤ ∑ j : Fin (KK d), eps d * ‖(ω j).1‖ :=
    Moment.norm_stateK_le (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε ω
  have h2 : ∑ j : Fin (KK d), eps d * ‖(ω j).1‖ ≤ ∑ _j : Fin (KK d), eps d * (2 * (d:ℝ)) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hξ j) hε
  have h3 : (∑ _j : Fin (KK d), eps d * (2 * (d:ℝ)))
      = (KK d : ℝ) * (eps d * (2 * (d:ℝ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : (KK d : ℝ) * (eps d * (2 * (d:ℝ))) ≤ 34 * (d:ℝ) * Real.log (d:ℝ) := by
    have hK := KK_le d hd
    have heq : eps d * (2 * (d:ℝ)) = 2 / (d:ℝ) := by
      rw [eps]; field_simp
    rw [heq]
    have h5 : (KK d : ℝ) * (2/(d:ℝ)) ≤ (17 * (d:ℝ)^2 * Real.log (d:ℝ)) * (2/(d:ℝ)) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    have h6 : (17 * (d:ℝ)^2 * Real.log (d:ℝ)) * (2/(d:ℝ))
        = 34 * (d:ℝ) * Real.log (d:ℝ) := by
      field_simp
      ring
    linarith [h5, h6]
  linarith [h1, h2, le_of_eq h3, h4]

/-- The trace of the state is bounded by the operator norm. -/
lemma abs_trace_HH_le (ω : Fin (KK d) → MatV d × MatV d) (hd : 2 ≤ d) :
    |(matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace|
      ≤ (d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ := by
  have hEq : (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace
      = inner ℝ (oneV d) (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω) := by
    simpa only [HH] using
      Moment.trace_state_eq_inner (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω
  rw [hEq]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_oneV]
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hs : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (d:ℝ) by positivity),
      Real.sqrt_nonneg (d:ℝ), hd1]
  exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)

/-- The upper bound for `cDrift`. -/
lemma cDrift_le_half (d : ℕ) (hd : 2 ≤ d) : cDrift d ≤ 1/2 := by
  rw [cDrift]
  have ha0 := Main.a0_ge_one hd
  have hrr := rr_nonneg d
  have h1 : (a0 d + 2 * rr d)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith : (0:ℝ) < a0 d + 2 * rr d)).mpr (by linarith)
  have h2 : (0:ℝ) ≤ (a0 d + 2 * rr d)⁻¹ := inv_nonneg.mpr (by linarith)
  have h3 : (a0 d + 2 * rr d)⁻¹ ^ 2 ≤ (1:ℝ)^2 := pow_le_pow_left₀ h2 h1 2
  linarith [h3]

/-- **The Taylor polynomial is bounded below on the increment event.** -/
lemma T_lower (ω : Fin (KK d) → MatV d × MatV d)
    (hξ : ∀ j : Fin (KK d), ‖(ω j).1‖ ≤ 2 * (d:ℝ)) (hd : D0 ≤ d) :
    -(2500 * (d:ℝ)^3) ≤ (d:ℝ) * Real.log (a0 d)
      + (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d)
      - cDrift d * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 := by
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have ha0 := Main.a0_ge_one hd2
  have hrrd := rr_nonneg d
  have hB := norm_HH_le (d := d) (q := q) (R := R) (a := a) ω hξ hd
  have htr := abs_trace_HH_le (d := d) (q := q) (R := R) (a := a) ω hd2
  have hlogd : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
  have hBnn : (0:ℝ) ≤ 34 * (d:ℝ) * Real.log (d:ℝ) := by positivity
  have hHHnn : (0:ℝ) ≤ ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ := norm_nonneg _
  -- bound on `|trace|`
  have htrb : |(matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace|
      ≤ 34 * (d:ℝ)^2 * Real.log (d:ℝ) := by
    refine htr.trans ?_
    calc (d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖
        ≤ (d:ℝ) * (34 * (d:ℝ) * Real.log (d:ℝ)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 34 * (d:ℝ)^2 * Real.log (d:ℝ) := by ring
  -- the trace term
  have htrterm : -((34:ℝ) * (d:ℝ)^2 * Real.log (d:ℝ))
      ≤ (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d) := by
    have h1 : -|(matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace|
        ≤ (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace := neg_abs_le _
    have h2 : -|(matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace|
        ≤ (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d) := by
      set t := (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace with ht
      by_cases ht0 : (0:ℝ) ≤ t
      · have h3 : 0 ≤ t / a0 d := div_nonneg ht0 (by linarith)
        rw [abs_of_nonneg ht0]; linarith
      · have h3 : t ≤ t / a0 d := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < a0 d)]
          nlinarith [lt_of_not_ge ht0, ha0]
        rw [abs_of_neg (lt_of_not_ge ht0)]; linarith
    linarith [h1, h2, htrb]
  -- the quadratic term
  have hqterm : -((578:ℝ) * (d:ℝ)^2 * (Real.log (d:ℝ))^2)
      ≤ - cDrift d * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 := by
    have hc := cDrift_le_half d hd2
    have hsq : ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2
        ≤ (34 * (d:ℝ) * Real.log (d:ℝ)) ^ 2 := pow_le_pow_left₀ hHHnn hB 2
    have hc2 : (0:ℝ) ≤ cDrift d := by
      rw [cDrift]; positivity
    nlinarith [hsq, hc, hc2, hHHnn]
  -- the logarithmic term
  have hlogterm : 0 ≤ (d:ℝ) * Real.log (a0 d) :=
    mul_nonneg (by positivity) (Real.log_nonneg ha0)
  -- numeric bounds for the leftovers
  have hs := sqrt_d_ge d hd
  have hsd : Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) = (d:ℝ) := Real.mul_self_sqrt (by positivity)
  have hlog2 := log_le_two_sqrt d hd
  have hnum1 : 34 * (d:ℝ)^2 * Real.log (d:ℝ) ≤ 68 * (d:ℝ)^3 := by
    have hs1 : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by nlinarith [hs, hsd]
    calc 34 * (d:ℝ)^2 * Real.log (d:ℝ) ≤ 34 * (d:ℝ)^2 * (2 * Real.sqrt (d:ℝ)) :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ ≤ 34 * (d:ℝ)^2 * (2 * (d:ℝ)) := by
          have : (0:ℝ) ≤ 34 * (d:ℝ)^2 := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith [hs1]) this
      _ = 68 * (d:ℝ)^3 := by ring
  have hnum2 : 578 * (d:ℝ)^2 * (Real.log (d:ℝ))^2 ≤ 2312 * (d:ℝ)^3 := by
    have hs1 : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by nlinarith [hs, hsd]
    have hsq : (Real.log (d:ℝ))^2 ≤ (2 * Real.sqrt (d:ℝ))^2 :=
      pow_le_pow_left₀ hlogd hlog2 2
    have h2 : (2 * Real.sqrt (d:ℝ))^2 = 4 * (d:ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (d:ℝ))]; norm_num
    nlinarith [hsq, h2, sq_nonneg (d:ℝ), sq_nonneg (Real.log (d:ℝ))]
  have hkey : -((68:ℝ) * (d:ℝ)^3) - 2312 * (d:ℝ)^3
      ≤ (d:ℝ) * Real.log (a0 d)
        + (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d)
        - cDrift d * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 := by
    linarith [htrterm, hqterm, hlogterm, hnum1, hnum2]
  have hnn : (0:ℝ) ≤ (d:ℝ)^3 := by positivity
  linarith [hkey, hnn]

/-! ## The numeric constants of the good-sample argument -/

lemma exp_half_gt (d : ℕ) (hd : D0 ≤ d) : 5001 * (d:ℝ)^7 < Real.exp ((d:ℝ)/2) := by
  have h7 := Real.pow_div_factorial_le_exp ((d:ℝ)/2) (by positivity) 8
  rw [show (Nat.factorial 8 : ℝ) = 40320 by norm_num] at h7
  have hdd : (10:ℝ)^20 ≤ (d:ℝ) := by
    have h := hd; simp only [D0] at h; exact_mod_cast h
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have h1 : ((d:ℝ)/2)^8 / 40320 = (d:ℝ)^8 / 10321920 := by
    rw [div_pow]
    rw [show ((2:ℝ)^8) = 256 by norm_num]
    field_simp
    ring
  rw [h1] at h7
  have h2 : 5001 * (d:ℝ)^7 < (d:ℝ)^8 / 10321920 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 10321920)]
    nlinarith [hdd, hd0, pow_pos hd0 7]
  linarith [h2, h7]

lemma numeric_W (d : ℕ) (hd : D0 ≤ d) :
    2*(d:ℝ)*Real.exp (-(d:ℝ))
      + 2*(d:ℝ)*Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4)*Real.exp (-(d:ℝ)/2)
      ≤ 5000 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) := by
  have hdd : (10:ℝ)^20 ≤ (d:ℝ) := by
    have h := hd; simp only [D0] at h; exact_mod_cast h
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by linarith
  have hlog : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg (by linarith)
  have hl : Real.log (d:ℝ) ≤ 2 * (d:ℝ) := by
    have := log_le_two_sqrt d hd
    have : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by
      nlinarith [Real.sq_sqrt (le_of_lt hd0), Real.sqrt_nonneg (d:ℝ), hd1]
    linarith
  have hexp1 : Real.exp (-(d:ℝ)) ≤ Real.exp (-(d:ℝ)/2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexpnn : (0:ℝ) ≤ Real.exp (-(d:ℝ)/2) := Real.exp_nonneg _
  -- first term
  have hA : 2*(d:ℝ)*Real.exp (-(d:ℝ)) ≤ 2 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) := by
    have h1 : (d:ℝ) ≤ (d:ℝ)^7 := by
      simpa using pow_le_pow_right₀ hd1 (by norm_num : 1 ≤ 7)
    calc 2*(d:ℝ)*Real.exp (-(d:ℝ)) ≤ 2*(d:ℝ)*Real.exp (-(d:ℝ)/2) := by
          have : (0:ℝ) ≤ 2*(d:ℝ) := by linarith
          exact mul_le_mul_of_nonneg_left hexp1 this
      _ ≤ 2*(d:ℝ)^7*Real.exp (-(d:ℝ)/2) := by
          apply mul_le_mul_of_nonneg_right _ hexpnn
          linarith
  -- second term
  have hB : 2*(d:ℝ)*Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4)*Real.exp (-(d:ℝ)/2)
      ≤ 4624 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) := by
    have hs : Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4)
        ≤ 578 * (d:ℝ)^4 * (Real.log (d:ℝ))^2 := by
      have h1 : (3:ℝ) ≤ 4 := by norm_num
      have h2 : Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4)
          ≤ Real.sqrt (4*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4) := by
        apply Real.sqrt_le_sqrt
        have := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4)
        linarith
      refine h2.trans ?_
      have h3 : (0:ℝ) ≤ 16*(d:ℝ)^2*Real.log (d:ℝ) + 1 := by positivity
      rw [show (4:ℝ)*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4
          = (2 * (16*(d:ℝ)^2*Real.log (d:ℝ)+1)^2)^2 by ring]
      rw [Real.sqrt_sq (by positivity)]
      have h4 : 16*(d:ℝ)^2*Real.log (d:ℝ) + 1 ≤ 17*(d:ℝ)^2*Real.log (d:ℝ) := by
        have hl1 : (1:ℝ) ≤ Real.log (d:ℝ) := log_d_ge_one hd
        have hd21 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith [hd1]
        have hmul : (1:ℝ) * 1 ≤ (d:ℝ)^2 * Real.log (d:ℝ) :=
          mul_le_mul hd21 hl1 (by norm_num) (by linarith)
        linarith
      have h5 : (2 * (16*(d:ℝ)^2*Real.log (d:ℝ)+1)^2) ≤ 578 * (d:ℝ)^4 * (Real.log (d:ℝ))^2 := by
        have h6 : (2 * (16*(d:ℝ)^2*Real.log (d:ℝ)+1)^2)
            ≤ 2 * (17*(d:ℝ)^2*Real.log (d:ℝ))^2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_left₀ (by positivity) h4 2
        have h7 : (2:ℝ) * (17*(d:ℝ)^2*Real.log (d:ℝ))^2 = 578 * (d:ℝ)^4 * (Real.log (d:ℝ))^2 := by ring
        linarith [h6, h7]
      linarith [h4, h5]
    have h9 : (Real.log (d:ℝ))^2 ≤ 4 * (d:ℝ)^2 := by
      have := pow_le_pow_left₀ hlog hl 2
      nlinarith [this]
    have h10 : 578 * (d:ℝ)^4 * (Real.log (d:ℝ))^2 ≤ 2312 * (d:ℝ)^6 := by
      nlinarith [h9, pow_pos hd0 4]
    have h11 : 2312 * (d:ℝ)^6 ≤ 2312 * (d:ℝ)^7 := by nlinarith [hd1, pow_pos hd0 6]
    have h12 : 2*(d:ℝ) * (578 * (d:ℝ)^4 * (Real.log (d:ℝ))^2) ≤ 4624 * (d:ℝ)^7 := by
      have h13 : 2*(d:ℝ)*(578 * (d:ℝ)^4 * (Real.log (d:ℝ))^2) ≤ 2*(d:ℝ)*(2312 * (d:ℝ)^6) := by
        apply mul_le_mul_of_nonneg_left h10 (by linarith)
      have h14 : 2*(d:ℝ)*(2312 * (d:ℝ)^6) = 4624 * (d:ℝ)^7 := by ring
      linarith [h13, h14]
    calc 2*(d:ℝ)*Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4)*Real.exp (-(d:ℝ)/2)
        ≤ 2*(d:ℝ)*(578 * (d:ℝ)^4 * (Real.log (d:ℝ))^2)*Real.exp (-(d:ℝ)/2) := by
          have hpos : (0:ℝ) ≤ Real.exp (-(d:ℝ)/2) := hexpnn
          have h15 : (0:ℝ) ≤ 2*(d:ℝ) := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs h15) hpos
      _ ≤ 4624 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) := by
          have hpos : (0:ℝ) ≤ Real.exp (-(d:ℝ)/2) := hexpnn
          exact mul_le_mul_of_nonneg_right h12 hpos
  have hfin : 2 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) + 4624 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2)
      = 4626 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) := by ring
  have h4626 : (4626:ℝ) ≤ 5000 := by norm_num
  have hpos7 : (0:ℝ) ≤ (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) := by positivity
  linarith [hA, hB, hfin]

/-! ## The lower bound on the trace term -/

lemma trace_div_lower (ω : Fin (KK d) → MatV d × MatV d) (hd : 2 ≤ d) :
    -((d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖)
      ≤ (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d) := by
  have htr := abs_trace_HH_le (d := d) (q := q) (R := R) (a := a) ω hd
  have ha0 := Main.a0_ge_one hd
  set t := (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace with ht
  by_cases ht0 : (0:ℝ) ≤ t
  · have h1 : 0 ≤ t / a0 d := div_nonneg ht0 (by linarith)
    rw [abs_of_nonneg ht0] at htr
    linarith
  · have h1 : t ≤ t / a0 d := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < a0 d)]
      nlinarith [lt_of_not_ge ht0, ha0]
    rw [abs_of_neg (lt_of_not_ge ht0)] at htr
    linarith

/-- **The Taylor polynomial is bounded below pointwise.** -/
lemma T_pointwise_lower (ω : Fin (KK d) → MatV d × MatV d) (hd : D0 ≤ d) :
    -(2*(d:ℝ) + 2*(d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖^2)
      ≤ (d:ℝ) * Real.log (a0 d)
        + (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d)
        - cDrift d * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 := by
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by
    have : (10:ℝ)^20 ≤ (d:ℝ) := by
      have h := hd; simp only [D0] at h; exact_mod_cast h
    linarith
  have ha0 := Main.a0_ge_one hd2
  set hh : ℝ := ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ with hhh
  have htr := trace_div_lower (d := d) (q := q) (R := R) (a := a) ω hd2
  rw [← hhh] at htr
  have hnn : (0:ℝ) ≤ hh := by rw [hhh]; positivity
  have hquad : -((1/2) * hh^2) ≤ - cDrift d * hh^2 := by
    have hc := cDrift_le_half d hd2
    nlinarith [sq_nonneg hh]
  have hlin : hh ≤ 2 + hh^2 := by nlinarith [sq_nonneg (hh - 1)]
  have hlog : 0 ≤ (d:ℝ) * Real.log (a0 d) :=
    mul_nonneg (by linarith) (Real.log_nonneg ha0)
  nlinarith [htr, hquad, hlog, hlin, hd1, hnn, sq_nonneg hh]

/-! ## S10 — the existence of a good sample -/

theorem exists_good_sample_K (d : ℕ) (hd : D0 ≤ d) {q : ℕ} {R : ℝ} {a : Fin d → ZMod q}
    (hRpos : 0 < R)
    (hmin : ∀ k : Fin d → ℤ, 0 < intQ k → intQ k ≤ R ^ 2 → ¬ LatticeGood2.kerCond a k)
    (hwt : (∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => LatticeGood2.kerCond a x),
        wt (d := d) (KK d) (a0 d) R k) ≤ (d : ℝ) ^ 4 / 2)
    {S : Finset (Vec d)} (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    (hcard : (S.card : ℝ) ≤ (12:ℝ) ^ d) :
    ∃ ω : Fin (KK d) → MatV d × MatV d,
      ω ∉ badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)
      ∧ (∀ j : Fin (KK d), ‖(ω j).1‖ ≤ 2 * (d:ℝ))
      ∧ Real.log (matOf d (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω (KK d))).det
          ≤ Cg + 1 - 4 * Real.log (d:ℝ) := by
  classical
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have hε : (0:ℝ) ≤ eps d := (eps_pos d (by omega)).le
  have ha0 : 1 ≤ a0 d := Main.a0_ge_one hd2
  have ha0pos : 0 < a0 d := lt_of_lt_of_le zero_lt_one ha0
  have hrnonneg : 0 ≤ rr d := rr_nonneg d
  have har : 2 * rr d < a0 d := by
    have h1 : 2 * rr d ≤ 1 := rr_le hd
    have h2 : 1 < a0 d := one_lt_a0 hd2
    linarith
  set bad : Set (Fin (KK d) → MatV d × MatV d) :=
    badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d) with hbaddef
  set inc : Set (Fin (KK d) → MatV d × MatV d) := incrEvent d (KK d) (2 * (d:ℝ)) with hincdef
  set G : Set (Fin (KK d) → MatV d × MatV d) := badᶜ ∩ incᶜ with hGdef
  set T : (Fin (KK d) → MatV d × MatV d) → ℝ := fun ω => (d:ℝ) * Real.log (a0 d)
      + (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d)
      - cDrift d * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 with hTdef
  set A1 : ℝ := Cg + 1 - 4 * Real.log (d:ℝ) with hA1def
  have hmeas_bad : MeasurableSet bad := by
    rw [hbaddef]; exact measurableSet_badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)
  have hmeas_inc : MeasurableSet inc := by
    rw [hincdef]; exact measurableSet_incrEvent d (KK d) (2 * (d:ℝ))
  have hmeas_G : MeasurableSet G := by rw [hGdef]; exact hmeas_bad.compl.inter hmeas_inc.compl
  have hbadm : (sampleLaw d (KK d)).real bad ≤ Real.exp (-(d:ℝ)) := by
    rw [hbaddef]; exact Main.badNet_measure_le d hd hSun hcard
  have hincm : (sampleLaw d (KK d)).real inc ≤ Real.exp (-(d:ℝ)) := by
    rw [hincdef]; exact incrEvent_measure_le d hd
  have hsub : badᶜ ∩ inc ⊆ inc := Set.inter_subset_right
  have hμs : (sampleLaw d (KK d)).real (badᶜ ∩ inc) ≤ Real.exp (-(d:ℝ)) :=
    (MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)).trans hincm
  -- integrability
  have hintTr : Integrable (fun ω => (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace)
      (sampleLaw d (KK d)) :=
    DriftMain.integrable_trace_HH (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε
  have hintN : Integrable (fun ω => ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2)
      (sampleLaw d (KK d)) :=
    Moment.integrable_stateK_norm_sq (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε
  have hintT : Integrable T (sampleLaw d (KK d)) := by
    rw [hTdef]
    exact ((integrable_const _).add (hintTr.div_const _)).sub (hintN.const_mul _)
  -- the drift bound
  have hdrift : (∫ ω in badᶜ, T ω ∂(sampleLaw d (KK d))) ≤ Cg - 4 * Real.log (d:ℝ) := by
    rw [hbaddef, hTdef]
    exact Main.drift_bound d hd hRpos hmin hwt hSun hcard
  -- the split of the drift integral
  have hunion : badᶜ = G ∪ (badᶜ ∩ inc) := by
    rw [hGdef, ← Set.inter_union_distrib_left, Set.compl_union_self, Set.inter_univ]
  have hdisj : Disjoint G (badᶜ ∩ inc) := by
    rw [hGdef, Set.disjoint_left]
    exact fun x hx hy => hx.2 hy.2
  have hsplit : (∫ ω in badᶜ, T ω ∂(sampleLaw d (KK d)))
      = (∫ ω in G, T ω ∂(sampleLaw d (KK d)))
        + ∫ ω in badᶜ ∩ inc, T ω ∂(sampleLaw d (KK d)) := by
    conv_lhs => rw [hunion]
    exact MeasureTheory.setIntegral_union hdisj (hmeas_bad.compl.inter hmeas_inc)
      (hintT.integrableOn.mono_set (Set.subset_univ _))
      (hintT.integrableOn.mono_set (Set.subset_univ _))
  -- the measure of `G`
  have hGle : 1 - 2 * Real.exp (-(d:ℝ)) ≤ (sampleLaw d (KK d)).real G := by
    have h1 : (sampleLaw d (KK d)).real badᶜ
        = (sampleLaw d (KK d)).real G + (sampleLaw d (KK d)).real (badᶜ ∩ inc) := by
      conv_lhs => rw [hunion]
      exact MeasureTheory.measureReal_union hdisj (hmeas_bad.compl.inter hmeas_inc)
        (MeasureTheory.measure_ne_top (sampleLaw d (KK d)) G)
        (MeasureTheory.measure_ne_top (sampleLaw d (KK d)) (badᶜ ∩ inc))
    have h2 : (sampleLaw d (KK d)).real badᶜ = 1 - (sampleLaw d (KK d)).real bad := by
      rw [MeasureTheory.measureReal_compl hmeas_bad]
      simp only [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one]
    have h3 : (sampleLaw d (KK d)).real (badᶜ ∩ inc) ≤ Real.exp (-(d:ℝ)) :=
      (MeasureTheory.measureReal_mono Set.inter_subset_right
        (MeasureTheory.measure_ne_top _ _)).trans hincm
    linarith [h1, h2, hbadm, h3]
  -- the lower bound on the `inc` piece
  set W0 : ℝ := 5000 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) with hW0def
  have hW0nn : (0:ℝ) ≤ W0 := by rw [hW0def]; positivity
  have hpiece : -W0 ≤ ∫ ω in badᶜ ∩ inc, T ω ∂(sampleLaw d (KK d)) := by
    set s : Set (Fin (KK d) → MatV d × MatV d) := badᶜ ∩ inc with hsdef
    have hs : MeasurableSet s := hmeas_bad.compl.inter hmeas_inc
    have hmono : (∫ ω in s, -(2*(d:ℝ) + 2*(d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖^2)
          ∂(sampleLaw d (KK d)))
        ≤ ∫ ω in s, T ω ∂(sampleLaw d (KK d)) := by
      refine MeasureTheory.setIntegral_mono_on ?_ ?_ hs (fun ω _ => ?_)
      · exact (((MeasureTheory.integrable_const (2*(d:ℝ))).add
          (hintN.const_mul (2*(d:ℝ)))).neg).integrableOn
      · exact hintT.integrableOn.mono_set (Set.subset_univ _)
      · exact T_pointwise_lower (d := d) (q := q) (R := R) (a := a) ω hd
    have hval : (∫ ω in s, (2*(d:ℝ) + 2*(d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖^2)
          ∂(sampleLaw d (KK d)))
        = 2*(d:ℝ) * (sampleLaw d (KK d)).real s
          + 2*(d:ℝ) * ∫ ω in s, ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖^2
              ∂(sampleLaw d (KK d)) := by
      rw [MeasureTheory.integral_add
        (f := fun _ : Fin (KK d) → MatV d × MatV d => 2*(d:ℝ))
        (g := fun ω => 2*(d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖^2)
        (MeasureTheory.integrable_const (2*(d:ℝ))).integrableOn (hintN.integrableOn.const_mul _)]
      rw [MeasureTheory.setIntegral_const, MeasureTheory.integral_const_mul]
      simp only [smul_eq_mul]
      ring
    have hCS : (∫ ω in s, ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2
          ∂(sampleLaw d (KK d)))
        ≤ Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4) * Real.exp (-(d:ℝ)/2) := by
      have h1 := Main.setIntegral_le_sqrt_mul_sqrt (μ := sampleLaw d (KK d)) (s := s)
        (f := fun ω => ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2)
        (fun ω => by positivity)
        (((Main.measurable_HH (d := d) (q := q) (R := R) (a := a) hε).pow_const 2).aestronglyMeasurable)
        (by simpa only [← pow_mul] using
          Main.integrable_norm_pow_four (d := d) (q := q) (R := R) (a := a) hε)
        hs
      refine h1.trans ?_
      have h2 : Real.sqrt (∫ ω : Fin (KK d) → MatV d × MatV d,
            ((fun ω => ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2) ω) ^ 2
              ∂(sampleLaw d (KK d)))
          ≤ Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4) := by
        refine Real.sqrt_le_sqrt ?_
        simpa only [← pow_mul] using
          Main.integral_norm_pow_four_le (d := d) (q := q) (R := R) (a := a) hε hd2
      have h3 : Real.sqrt ((sampleLaw d (KK d)).real s) ≤ Real.exp (-(d:ℝ)/2) := by
        refine (Real.sqrt_le_sqrt hμs).trans (le_of_eq ?_)
        rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
        congr 1
        ring
      refine (mul_le_mul h2 h3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans ?_
      rw [show Real.sqrt (3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 4)
            * Real.exp (-(d:ℝ) / 2)
          = Real.sqrt (3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 4) * Real.exp (-(d:ℝ)/2)
        from rfl]
    have hb1 : 2*(d:ℝ) * (sampleLaw d (KK d)).real s ≤ 2*(d:ℝ) * Real.exp (-(d:ℝ)) :=
      mul_le_mul_of_nonneg_left hμs (by positivity)
    have hb2 : 2*(d:ℝ) * (∫ ω in s, ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2
          ∂(sampleLaw d (KK d)))
        ≤ 2*(d:ℝ) * (Real.sqrt (3*(16*(d:ℝ)^2*Real.log (d:ℝ)+1)^4) * Real.exp (-(d:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    have hbound : 2*(d:ℝ) * (sampleLaw d (KK d)).real s
        + 2*(d:ℝ) * (∫ ω in s, ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2
            ∂(sampleLaw d (KK d))) ≤ W0 := by
      rw [hW0def]
      linarith [hb1, hb2, numeric_W (d := d) hd]
    rw [MeasureTheory.integral_neg, hval] at hmono
    linarith [hmono, hbound]
  -- the numeric contradiction
  have hCg : 2 * (Cg + 1) ≤ (d:ℝ)^7 := by
    rw [show Cg = (10:ℝ)^6 from rfl]
    have hdd : (10:ℝ)^20 ≤ (d:ℝ) := by
      have h := hd; simp only [D0] at h; exact_mod_cast h
    have hle : 2 * ((10:ℝ)^6 + 1) ≤ (10:ℝ)^20 := by norm_num
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by linarith
    calc 2 * ((10:ℝ)^6 + 1) ≤ (10:ℝ)^20 := hle
      _ ≤ (d:ℝ) := hdd
      _ ≤ (d:ℝ)^7 := by
          simpa using pow_le_pow_right₀ hd1 (by norm_num : 1 ≤ 7)
  have hkey2 : 2 * A1 * Real.exp (-(d:ℝ)) + W0 < 1 := by
    have hA1le : A1 ≤ Cg + 1 := by
      rw [hA1def]
      have := Main.log_d_ge_one hd
      linarith
    have hdnn : (0:ℝ) ≤ (d:ℝ) := by positivity
    have hexp1 : Real.exp (-(d:ℝ)) ≤ Real.exp (-(d:ℝ)/2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hexpnn : (0:ℝ) ≤ Real.exp (-(d:ℝ)/2) := Real.exp_nonneg _
    have h1 : 2 * A1 * Real.exp (-(d:ℝ)) ≤ 2 * (Cg + 1) * Real.exp (-(d:ℝ)/2) := by
      have h3 : 2 * A1 ≤ 2 * (Cg + 1) := by linarith
      calc 2 * A1 * Real.exp (-(d:ℝ)) ≤ 2 * (Cg + 1) * Real.exp (-(d:ℝ)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
        _ ≤ 2 * (Cg + 1) * Real.exp (-(d:ℝ)/2) := by
            refine mul_le_mul_of_nonneg_left hexp1 ?_
            rw [show Cg = (10:ℝ)^6 from rfl]; norm_num
    have h2 : 2 * (Cg + 1) * Real.exp (-(d:ℝ)/2) + W0
        ≤ 5001 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) := by
      rw [hW0def]
      have : 2 * (Cg + 1) + 5000 * (d:ℝ)^7 ≤ 5001 * (d:ℝ)^7 := by linarith [hCg]
      nlinarith [this, hexpnn]
    have h3 : 5001 * (d:ℝ)^7 * Real.exp (-(d:ℝ)/2) < 1 := by
      have h7 : Real.exp (-(d:ℝ)/2) = (Real.exp ((d:ℝ)/2))⁻¹ := by
        rw [show -(d:ℝ)/2 = -((d:ℝ)/2) by ring, Real.exp_neg]
      rw [h7, inv_eq_one_div, mul_one_div, div_lt_one (Real.exp_pos _)]
      exact exp_half_gt d hd
    linarith [h1, h2, h3]
  have hW0lt1 : W0 < 1 := by
    rw [hW0def]
    have hexp := exp_half_gt d hd
    have h7 : Real.exp (-(d:ℝ)/2) = (Real.exp ((d:ℝ)/2))⁻¹ := by
      rw [show -(d:ℝ)/2 = -((d:ℝ)/2) by ring, Real.exp_neg]
    rw [h7, inv_eq_one_div, mul_one_div, div_lt_one (Real.exp_pos _)]
    have hd0 : (0:ℝ) < (d:ℝ) := by positivity
    linarith [hexp, pow_pos hd0 7]
  -- the mean-value contradiction
  by_contra hcon
  have hpt : ∀ ω ∈ G, A1 ≤ T ω := by
    intro ω hω
    have hb : ω ∉ bad := hω.1
    have h1 : Real.log (matOf d (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω (KK d))).det
        ≤ T ω := by
      rw [hTdef]
      exact DriftMain.log_det_le_of_not_badNet (R := Rb) (BoxL := BoxL d q R a) (a₀ := a0 d)
        (ε := eps d) (r := rr d) (K := KK d) (S := S) hSun hcover hb ha0pos hrnonneg har
    have h2 : A1 < Real.log (matOf d (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω (KK d))).det := by
      by_contra hle
      push_neg at hle
      exact hcon ⟨ω, hb, fun j => le_of_not_gt (fun hj => hω.2 ⟨j, hj⟩), hle⟩
    linarith
  have hmono : (∫ ω in G, A1 ∂(sampleLaw d (KK d)))
      ≤ ∫ ω in G, T ω ∂(sampleLaw d (KK d)) :=
    MeasureTheory.setIntegral_mono_on MeasureTheory.integrableOn_const
      (hintT.integrableOn.mono_set (Set.subset_univ _)) hmeas_G (fun ω hω => hpt ω hω)
  rw [MeasureTheory.setIntegral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hGle1 : (sampleLaw d (KK d)).real G ≤ 1 := by
    refine (MeasureTheory.measureReal_mono (Set.subset_univ G) (MeasureTheory.measure_ne_top _ _)).trans ?_
    rw [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one]
  have hA0 : Cg - 4 * Real.log (d:ℝ) = A1 - 1 := by rw [hA1def]; ring
  have hmain : 1 + A1 * ((sampleLaw d (KK d)).real G - 1) ≤ W0 := by
    have h1 := hdrift
    rw [hsplit] at h1
    have h2 : A1 * ((sampleLaw d (KK d)).real G)
        ≤ ∫ ω in G, T ω ∂(sampleLaw d (KK d)) := by
      linarith [hmono]
    linarith [h1, h2, hpiece, hA0]
  by_cases hA : (0:ℝ) ≤ A1
  · have h3 : -2 * A1 * Real.exp (-(d:ℝ)) ≤ A1 * ((sampleLaw d (KK d)).real G - 1) := by
      have h5 : -2 * Real.exp (-(d:ℝ)) ≤ ((sampleLaw d (KK d)).real G - 1) := by linarith [hGle]
      have h6 := mul_le_mul_of_nonneg_left h5 hA
      rw [show A1 * (-2 * Real.exp (-(d:ℝ))) = -2 * A1 * Real.exp (-(d:ℝ)) by ring] at h6
      exact h6
    linarith [hmain, h3, hkey2]
  · have hA' : A1 < 0 := lt_of_not_ge hA
    have h3 : 0 ≤ A1 * ((sampleLaw d (KK d)).real G - 1) :=
      mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA') (by linarith [hGle1])
    linarith [hmain, h3, hW0lt1]

/-! ## S11 — the rescaling, with the net-based good event -/

lemma quadFormV_state_squeeze_net {R a₀ ε r : ℝ} {K : ℕ} {m : ℕ} {BoxL : Fin m → Vec d}
    (S : Finset (Vec d)) (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    {ω : Fin K → MatV d × MatV d} (hbad : ω ∉ badNet R BoxL a₀ ε K S r)
    (hr : 0 ≤ r) (k : ℕ) (hk : k ≤ K) (y : Vec d) :
    (a₀ - 2 * r) * ‖y‖ ^ 2 ≤ quadFormV (proc (projL R BoxL) a₀ ε K ω k) y ∧
      quadFormV (proc (projL R BoxL) a₀ ε K ω k) y ≤ (a₀ + 2 * r) * ‖y‖ ^ 2 := by
  have hb := Good.quadFormV_bound_of_not_badNet (R := R) (BoxL := BoxL) (a₀ := a₀) (ε := ε)
    (K := K) S hSun hcover hbad hr k hk y
  have hsplit : quadFormV (proc (projL R BoxL) a₀ ε K ω k) y
      = quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y + a₀ * ‖y‖ ^ 2 := by
    conv_lhs => rw [show proc (projL R BoxL) a₀ ε K ω k
        = (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) + a₀ • oneV d from by abel]
    rw [quadFormV_add, quadFormV_oneV]
  constructor
  · rw [hsplit]
    have h1 := (abs_le.mp hb).1
    nlinarith
  · rw [hsplit]
    have h1 := (abs_le.mp hb).2
    nlinarith
theorem one_sub_theta_le_quadFormV_net (R ε a₀ : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) (BoxL : Fin m → Vec d)
    (Λ : Submodule ℤ (Vec d)) {r : ℝ} (S : Finset (Vec d))
    (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    (hmin : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → 1 ≤ ‖x‖)
    (hbox : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → ‖x‖ ≤ R → ∃ i : Fin m, BoxL i = x)
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (ha₀ : 1 < a₀) (hR0 : 0 ≤ R)
    (hband : 1 ≤ (a₀ - 2 * r) * R ^ 2)
    (hξ : ∀ j : Fin K, ‖(ω j).1‖ ≤ 2 * d)
    (hbad : ω ∉ badNet R BoxL a₀ ε K S r)
    {x : Vec d} (hxΛ : x ∈ Λ) (hx0 : x ≠ 0) :
    1 - ε * (2 * d) * R ^ 2 ≤ quadFormV (proc (projL R BoxL) a₀ ε K ω K) x := by
  by_cases hcase : 1 ≤ quadFormV (proc (projL R BoxL) a₀ ε K ω K) x
  · have hnn : (0 : ℝ) ≤ ε * (2 * (d : ℝ)) * R ^ 2 := by
      have h1 : (0 : ℝ) ≤ ε := hε
      have h2 : (0 : ℝ) ≤ R ^ 2 := sq_nonneg R
      positivity
    linarith
  · push_neg at hcase
    have hR2pos : 0 < R ^ 2 := by
      by_contra h
      have h0 : R ^ 2 ≤ 0 := not_lt.mp h
      have hz : R ^ 2 = 0 := le_antisymm h0 (sq_nonneg R)
      nlinarith [hband]
    have hpos : 0 < a₀ - 2 * r := by
      by_contra h
      have h0 : a₀ - 2 * r ≤ 0 := not_lt.mp h
      have := mul_nonpos_of_nonpos_of_nonneg h0 (le_of_lt hR2pos)
      nlinarith [hband]
    have hxR : ‖x‖ ≤ R := by
      have hle1 := (quadFormV_state_squeeze_net S hSun hcover hbad hr K le_rfl x).1
      have hlt2 : (a₀ - 2 * r) * ‖x‖ ^ 2 < 1 := lt_of_le_of_lt hle1 hcase
      have hlt3 : (a₀ - 2 * r) * ‖x‖ ^ 2 < (a₀ - 2 * r) * R ^ 2 :=
        lt_of_lt_of_le hlt2 hband
      have hsq : ‖x‖ ^ 2 < R ^ 2 := lt_of_mul_lt_mul_left hlt3 (le_of_lt hpos)
      have h4 := (sq_le_sq.mp (le_of_lt hsq))
      rwa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg hR0] at h4
    obtain ⟨i, hi⟩ := hbox x hxΛ hx0 hxR
    have hex : ∃ k, quadFormV (proc (projL R BoxL) a₀ ε K ω k) x ≤ 1 := ⟨K, le_of_lt hcase⟩
    set k₀ := Nat.find hex with hk₀def
    have hk₀le : k₀ ≤ K := Nat.find_min' hex (le_of_lt hcase)
    have hk₀viol : quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x ≤ 1 := Nat.find_spec hex
    have hA0 : 1 < quadFormV (proc (projL R BoxL) a₀ ε K ω 0) x := by
      have h1 : proc (projL R BoxL) a₀ ε K ω 0 = a₀ • oneV d := rfl
      rw [h1, quadFormV_oneV]
      have h2 : (1 : ℝ) ≤ ‖x‖ ^ 2 := by
        have h3 := hmin x hxΛ hx0
        nlinarith [norm_nonneg x]
      nlinarith
    have hk₀pos : 1 ≤ k₀ := by
      rcases Nat.eq_zero_or_pos k₀ with h | h
      · rw [h] at hk₀viol; linarith
      · exact h
    have hprev : 1 < quadFormV (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)) x := by
      by_contra hle
      push_neg at hle
      have hlt : k₀ - 1 < k₀ := by omega
      exact Nat.find_min hex hlt hle
    have hm : k₀ - 1 < K := by omega
    have hstep : quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x
        = quadFormV (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)) x
          + ε * quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
              ((ω ⟨k₀ - 1, hm⟩).1)) x := by
      have hk : k₀ = (k₀ - 1) + 1 := by omega
      conv_lhs => rw [hk]
      rw [proc_succ, dif_pos hm, step, quadFormV_add, quadFormV_smul]
    have hbound : |quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
        ((ω ⟨k₀ - 1, hm⟩).1)) x| ≤ (2 * d) * R ^ 2 := by
      rw [quadFormV_eq_inner]
      have h1 := abs_real_inner_le_norm
        ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1))) ((ω ⟨k₀ - 1, hm⟩).1))
        (tensorV x)
      have h2 := norm_projL_apply_le R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1))
        ((ω ⟨k₀ - 1, hm⟩).1)
      have h3 : ‖tensorV x‖ = ‖x‖ ^ 2 := norm_tensorV x
      have h4 : ‖(ω ⟨k₀ - 1, hm⟩).1‖ ≤ 2 * d := hξ ⟨k₀ - 1, hm⟩
      have h5 : (0 : ℝ) ≤ 2 * d := by positivity
      have h6 : ‖((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
          ((ω ⟨k₀ - 1, hm⟩).1))‖ * ‖tensorV x‖ ≤ (2 * d) * R ^ 2 := by
        rw [h3]
        exact mul_le_mul (le_trans h2 h4) (by nlinarith [norm_nonneg x]) (by positivity) h5
      linarith
    have hfrozen := quadFormV_frozen R ε a₀ K BoxL ω hk₀le le_rfl
      ((mem_violSet_iff).mpr ⟨i, hi ▸ hxR, hi ▸ hk₀viol, hi⟩)
    have hfin : quadFormV (proc (projL R BoxL) a₀ ε K ω K) x
        = quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x := hfrozen.2
    have hkey : quadFormV (proc (projL R BoxL) a₀ ε K ω k₀) x
        > 1 - ε * (2 * d) * R ^ 2 := by
      have h1 : ε * quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
          ((ω ⟨k₀ - 1, hm⟩).1)) x ≥ -ε * ((2 * d) * R ^ 2) := by
        nlinarith [neg_abs_le (quadFormV ((projL R BoxL (proc (projL R BoxL) a₀ ε K ω (k₀ - 1)))
          ((ω ⟨k₀ - 1, hm⟩).1)) x), hbound, hε]
      linarith [hstep, hprev, h1]
    linarith [hfin, hkey]

/-! ## S12 — auxiliary lemmas for the final lattice -/

lemma two_rr_le_half (d : ℕ) (hd : D0 ≤ d) : 2 * rr d ≤ 1 / 2 := by
  have hdd : (10:ℝ)^20 ≤ (d:ℝ) := by
    have h := hd; simp only [D0] at h; exact_mod_cast h
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by linarith
  have hlognn : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg hd1
  have hs : (18432:ℝ) ≤ Real.sqrt (d:ℝ) := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hd0)]
    nlinarith [hdd]
  have hsd : Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) = (d:ℝ) := Real.mul_self_sqrt (le_of_lt hd0)
  have hlog : Real.log (d:ℝ) ≤ 2 * Real.sqrt (d:ℝ) := log_le_two_sqrt d hd
  have h1 : 9216 * Real.log (d:ℝ) ≤ (d:ℝ) := by nlinarith [hlog, hs, hsd]
  have h2 : 96 * Real.sqrt (Real.log (d:ℝ)) ≤ Real.sqrt (d:ℝ) := by
    have h3 : Real.sqrt (9216 * Real.log (d:ℝ)) ≤ Real.sqrt (d:ℝ) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9216) (Real.log (d:ℝ)),
      show Real.sqrt (9216:ℝ) = 96 by
        rw [show (9216:ℝ) = 96 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
    exact h3
  have h4 : Real.sqrt (d:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd0)
  rw [rr, show 2 * (24 * Real.sqrt (Real.log (d:ℝ)) / Real.sqrt (d:ℝ))
      = 48 * Real.sqrt (Real.log (d:ℝ)) / Real.sqrt (d:ℝ) by ring]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hd0)]
  linarith [h2]

lemma posDef_matOf_of_quadFormV {v : MatV d} (hsym : (matOf d v).IsSymm)
    (h : ∀ y : Vec d, y ≠ 0 → 0 < quadFormV v y) : (matOf d v).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (LogDetV.isHermitian_matOf v hsym) ?_
  intro x hx
  have hx' : x ≠ 0 := hx
  have hstar : star x = x := by funext i; exact star_trivial (x i)
  rw [hstar]
  have hy : WithLp.toLp 2 x ≠ 0 := by
    intro h0
    exact hx' (by rw [← WithLp.ofLp_toLp 2 x, h0]; rfl)
  have h1 := h (WithLp.toLp 2 x) hy
  rw [quadFormV_eq_dotProduct, WithLp.ofLp_toLp] at h1
  exact h1

lemma isZLattice_map_linear {n : ℕ} (f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : Function.Injective f) (S : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology S]
    [IsZLattice ℝ S] [DiscreteTopology (Submodule.map (f.restrictScalars ℤ) S)] :
    IsZLattice ℝ (Submodule.map (f.restrictScalars ℤ) S) := by
  refine IsZLattice.mk ?_
  have hset : (↑(Submodule.map (f.restrictScalars ℤ) S) : Set (EuclideanSpace ℝ (Fin n)))
      = f '' (↑S : Set (EuclideanSpace ℝ (Fin n))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  rw [hset, ← Submodule.map_span (f := f) (s := (↑S : Set (EuclideanSpace ℝ (Fin n)))),
    IsZLattice.span_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hf)
theorem inCone_rescaled_net (R ε a₀ : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) (BoxL : Fin m → Vec d)
    (Λ : Submodule ℤ (Vec d)) {r : ℝ} (S : Finset (Vec d))
    (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4)
    (hmin : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → 1 ≤ ‖x‖)
    (hbox : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → ‖x‖ ≤ R → ∃ i : Fin m, BoxL i = x)
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (ha₀ : 1 < a₀) (hR0 : 0 ≤ R)
    (hband : 1 ≤ (a₀ - 2 * r) * R ^ 2)
    (hθ : ε * (2 * d) * R ^ 2 < 1)
    (hξ : ∀ j : Fin K, ‖(ω j).1‖ ≤ 2 * d)
    (hbad : ω ∉ badNet R BoxL a₀ ε K S r) :
    ∀ x ∈ Λ, x ≠ 0 →
      1 ≤ quadFormV ((1 - ε * (2 * d) * R ^ 2)⁻¹ •
        proc (projL R BoxL) a₀ ε K ω K) x := by
  intro x hxΛ hx0
  have hlow := one_sub_theta_le_quadFormV_net R ε a₀ K ω BoxL Λ S hSun hcover hmin hbox hε hr ha₀
    hR0 hband hξ hbad hxΛ hx0
  have hpos : (0 : ℝ) < 1 - ε * (2 * d) * R ^ 2 := by linarith
  rw [quadFormV_smul, le_inv_mul_iff₀ hpos]
  linarith


theorem exists_finset_sphere_net_three (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      (∀ x ∈ S, ‖x‖ = 1) ∧
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ δ) ∧
      (S.card : ℝ) ≤ (3 / δ) ^ d := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let sph : Set E := {y : E | ‖y‖ = 1}
  let Fam : Set (Set E) :=
    {A : Set E | A ⊆ sph ∧
      ∀ ⦃x : E⦄, x ∈ A → ∀ ⦃y : E⦄, y ∈ A → x ≠ y → δ ≤ ‖x - y‖}
  have hub : ∀ c : Set (Set E), c ⊆ Fam → IsChain (· ⊆ ·) c →
      ∃ ub ∈ Fam, ∀ s ∈ c, s ⊆ ub := by
    intro c hcFam hchain
    refine ⟨⋃₀ c, ?_, ?_⟩
    · change (⋃₀ c) ⊆ sph ∧
        ∀ ⦃x : E⦄, x ∈ ⋃₀ c → ∀ ⦃y : E⦄, y ∈ ⋃₀ c → x ≠ y → δ ≤ ‖x - y‖
      constructor
      · intro x hx
        rcases hx with ⟨A, hAc, hxA⟩
        have hAFam : A ∈ Fam := hcFam hAc
        have hA_pair : A ⊆ sph ∧
            ∀ ⦃x : E⦄, x ∈ A → ∀ ⦃y : E⦄, y ∈ A → x ≠ y → δ ≤ ‖x - y‖ := by
          simpa [Fam] using hAFam
        exact hA_pair.1 hxA
      · intro x hx y hy hxy
        rcases hx with ⟨Ax, hAxc, hxAx⟩
        rcases hy with ⟨Ay, hAyc, hyAy⟩
        have hAxFam : Ax ∈ Fam := hcFam hAxc
        have hAyFam : Ay ∈ Fam := hcFam hAyc
        have hAx_pair : Ax ⊆ sph ∧
            ∀ ⦃x : E⦄, x ∈ Ax → ∀ ⦃y : E⦄, y ∈ Ax → x ≠ y → δ ≤ ‖x - y‖ := by
          simpa [Fam] using hAxFam
        have hAy_pair : Ay ⊆ sph ∧
            ∀ ⦃x : E⦄, x ∈ Ay → ∀ ⦃y : E⦄, y ∈ Ay → x ≠ y → δ ≤ ‖x - y‖ := by
          simpa [Fam] using hAyFam
        by_cases heq : Ax = Ay
        · subst Ay
          exact hAx_pair.2 hxAx hyAy hxy
        · rcases hchain hAxc hAyc heq with hlt | hlt
          · -- Ax ⊆ Ay
            exact hAy_pair.2 (hlt hxAx) hyAy hxy
          · -- Ay ⊆ Ax
            exact hAx_pair.2 hxAx (hlt hyAy) hxy
    · intro s hs
      exact Set.subset_sUnion_of_mem hs
  rcases zorn_subset Fam hub with ⟨S, hS⟩
  -- hS : Maximal (· ∈ Fam) S
  have hS_Fam : S ∈ Fam := hS.1
  have hS_mem : S ⊆ sph ∧
      ∀ ⦃x : E⦄, x ∈ S → ∀ ⦃y : E⦄, y ∈ S → x ≠ y → δ ≤ ‖x - y‖ := by
    simpa [Fam] using hS_Fam
  have hS_sph : S ⊆ sph := hS_mem.1
  have hS_sep : ∀ ⦃x : E⦄, x ∈ S → ∀ ⦃y : E⦄, y ∈ S → x ≠ y → δ ≤ ‖x - y‖ := hS_mem.2
  have hS_sphere : ∀ x : EuclideanSpace ℝ (Fin d), x ∈ S → ‖x‖ = 1 := by
    intro x hx
    exact hS_sph hx
  have hcover : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ δ := by
    intro y hy
    by_cases hyS : y ∈ S
    · refine ⟨y, hyS, ?_⟩
      rw [sub_self, norm_zero]
      exact le_of_lt hδ0
    · by_contra hnone
      push Not at hnone
      have hsep_insert : ∀ ⦃x : E⦄, x ∈ insert y S → ∀ ⦃z : E⦄, z ∈ insert y S →
          x ≠ z → δ ≤ ‖x - z‖ := by
        intro x hx z hz hxz
        by_cases hxy : x = y
        · subst x
          have hzS : z ∈ S := by
            rcases Set.mem_insert_iff.mp hz with rfl | hzS
            · exact (hxz rfl).elim
            · exact hzS
          exact le_of_lt (hnone z hzS)
        · have hxS : x ∈ S := by
            rcases Set.mem_insert_iff.mp hx with rfl | hxS
            · exact (hxy rfl).elim
            · exact hxS
          by_cases hzy : z = y
          · subst z
            rw [norm_sub_rev]
            exact le_of_lt (hnone x hxS)
          · have hzS : z ∈ S := by
              rcases Set.mem_insert_iff.mp hz with rfl | hzS
              · exact (hzy rfl).elim
              · exact hzS
            exact hS_sep hxS hzS hxz
      have hsub_insert : insert y S ⊆ sph := by
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hxS
        · exact hy
        · exact hS_sph hxS
      have hinsertFam : insert y S ∈ Fam := by
        change insert y S ⊆ sph ∧
          ∀ ⦃x : E⦄, x ∈ insert y S → ∀ ⦃z : E⦄, z ∈ insert y S → x ≠ z → δ ≤ ‖x - z‖
        exact ⟨hsub_insert, hsep_insert⟩
      have hmax : insert y S ⊆ S := hS.2 hinsertFam (Set.subset_insert y S)
      have hyS' : y ∈ S := hmax (by simp)
      exact hyS hyS'
  -- finiteness / bound
  have hfinite_bound : ∀ T : Set E, T.Finite → T ⊆ S → (T.ncard : ℝ) ≤ (3 / δ) ^ d := by
    intro T hTfin hTS
    exact Commons.Topology.MetricSpace.sphere_net_cardinality_finite_le d δ hδ0 hδ1 T hTfin
      (fun x hx => hS_sphere x (hTS hx))
      (fun ⦃x⦄ hx ⦃y⦄ hy hxy => hS_sep (hTS hx) (hTS hy) hxy)
  have hSfin : S.Finite := by
    by_contra hfin
    rcases exists_nat_gt ((3 / δ) ^ d) with ⟨M, hM⟩
    have hSinf : S.Infinite := by simpa using hfin
    rcases (Set.Infinite.exists_subset_ncard_eq hSinf M) with ⟨T, hTS, hTfin, hTcard⟩
    have hTbound : (T.ncard : ℝ) ≤ (3 / δ) ^ d := hfinite_bound T hTfin hTS
    rw [hTcard] at hTbound
    linarith
  refine ⟨hSfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    exact hS_sphere x ((Set.Finite.mem_toFinset hSfin).mp hx)
  · intro y hy
    obtain ⟨x, hxS, hxy⟩ := hcover y hy
    exact ⟨x, (Set.Finite.mem_toFinset hSfin).mpr hxS, hxy⟩
  · rw [← Set.ncard_eq_toFinset_card S hSfin]
    exact hfinite_bound S hSfin (subset_rfl)

/-! ## S12 — the final lattice and the target theorem -/

lemma exp_sub_four_log (d : ℕ) (hd : (0:ℝ) < (d:ℝ)) (C : ℝ) :
    Real.exp (C - 4 * Real.log (d:ℝ)) = Real.exp C / (d:ℝ)^4 := by
  rw [Real.exp_sub]
  have h1 : Real.exp (4 * Real.log (d:ℝ)) = (d:ℝ)^4 := by
    rw [show (4:ℝ) * Real.log (d:ℝ) = (4:ℕ) * Real.log (d:ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hd]
  rw [h1]

lemma inv_one_sub_eight_le_exp (d : ℕ) (hd : (16:ℝ) ≤ (d:ℝ)) :
    ((1 - 8 / (d:ℝ))⁻¹) ^ d ≤ Real.exp 16 := by
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have hpos : 0 < 1 - 8 / (d:ℝ) := by
    rw [sub_pos, div_lt_one hd0]; linarith
  have hlog : -Real.log (1 - 8 / (d:ℝ)) ≤ 16 / (d:ℝ) := by
    have h1 : Real.log ((1 - 8 / (d:ℝ))⁻¹) ≤ (1 - 8 / (d:ℝ))⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h1
    have h2 : (1 - 8 / (d:ℝ))⁻¹ - 1 = (8 / (d:ℝ)) * (1 - 8 / (d:ℝ))⁻¹ := by
      have h3 : (1 - 8 / (d:ℝ)) * (1 - 8 / (d:ℝ))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      nlinarith [h3]
    rw [h2] at h1
    have h3 : (8 / (d:ℝ)) * (1 - 8 / (d:ℝ))⁻¹ ≤ 16 / (d:ℝ) := by
      have h5 : (1 - 8 / (d:ℝ))⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hpos (by norm_num : (0:ℝ) < 2)]
        rw [show (2:ℝ)⁻¹ = 1/2 by norm_num]
        have h8 : 8 / (d:ℝ) ≤ 1/2 := by
          rw [div_le_iff₀ hd0]; nlinarith [hd]
        linarith
      have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 8 / (d:ℝ))
      have h7 : (8/(d:ℝ)) * 2 = 16/(d:ℝ) := by ring
      linarith [h6, h7]
    linarith [h1, h3]
  have hpow : Real.exp ((d:ℝ) * Real.log ((1 - 8 / (d:ℝ))⁻¹))
      = ((1 - 8 / (d:ℝ))⁻¹) ^ d := by
    rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hpos)]
  rw [← hpow]
  refine Real.exp_le_exp.mpr ?_
  rw [Real.log_inv]
  have h5 : (d:ℝ) * (-Real.log (1 - 8 / (d:ℝ))) ≤ 16 := by
    have h6 := mul_le_mul_of_nonneg_left hlog (le_of_lt hd0)
    have h7 : (d:ℝ) * (16 / (d:ℝ)) = 16 := by field_simp
    linarith [h6, h7]
  exact h5

/-- **Klartag's theorem in lattice (density) form**, with the unit ball volume written as
`om d` (which is `Submission.Helpers.omega d` by definition). -/
theorem klartag_lattice_large_om :
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, 2 ≤ D ∧
      ∀ d : ℕ, D ≤ d →
        ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
          (h₁ : DiscreteTopology Λ) (h₂ : IsZLattice ℝ Λ),
          (∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) ∧
          ZLattice.covolume Λ ≤ om d / (c * ((d : ℝ) - 1) ^ 2) := by
  obtain ⟨Dsh, hshellD⟩ := Commons.Analysis.Gaussian.integral_shell_weight_le
  have hnum : 0 < 1 / (Real.exp ((Cg + 17) / 2 + 1) * Cc * 4) := by
    have h1 : (0:ℝ) < Real.exp ((Cg + 17) / 2 + 1) := Real.exp_pos _
    have h2 : (0:ℝ) < Cc := by norm_num [Cc]
    positivity
  refine ⟨1 / (Real.exp ((Cg + 17) / 2 + 1) * Cc * 4), hnum,
    Nat.max D0 (Nat.max Dsh 2), ?_, ?_⟩
  · exact le_trans (le_max_right Dsh 2) (le_max_right D0 (Nat.max Dsh 2))
  · intro d hd
    have hd0 : D0 ≤ d := le_trans (le_max_left _ _) hd
    have hdsh : Dsh ≤ d :=
      le_trans (le_trans (le_max_left Dsh 2) (le_max_right D0 (Nat.max Dsh 2))) hd
    have hd2 : 2 ≤ d :=
      le_trans (le_trans (le_max_right Dsh 2) (le_max_right D0 (Nat.max Dsh 2))) hd
    have hd16 : (16:ℝ) ≤ (d:ℝ) := by
      have h : 16 ≤ d := by simp only [D0] at hd0; omega
      exact_mod_cast h
    have hε : (0:ℝ) ≤ eps d := (eps_pos d (by omega)).le
    have ha0 : 1 ≤ a0 d := Main.a0_ge_one hd2
    have ha0' : 1 < a0 d := one_lt_a0 hd2
    have hrrn : 0 ≤ rr d := rr_nonneg d
    have hdpos : (0:ℝ) < (d:ℝ) := by
      have h : (10:ℝ)^20 ≤ (d:ℝ) := by
        have hh := hd0; simp only [D0] at hh; exact_mod_cast hh
      linarith
    -- the `1/4`-net of the unit sphere
    obtain ⟨S, hSun, hcover, hScard⟩ :=
      exists_finset_sphere_net_three d (δ := 1/4) (by norm_num) (by norm_num)
    have hcard : (S.card : ℝ) ≤ (12:ℝ)^d := by
      refine hScard.trans (le_of_eq ?_)
      congr 1
      norm_num
    -- the `q`-ary data
    have hK : (KK d : ℝ) ≤ 16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1 := le_of_lt (KK_lt d)
    obtain ⟨q, R, a, hdat⟩ :=
      exists_data d hd0 (K := KK d) hK (hshellD d hdsh (KK d) hK)
    have hqprime : q.Prime := hdat.1
    have hR1 : 1 ≤ R := hdat.2.1
    have hRq : 2 * R < (q : ℝ) := hdat.2.2.1
    have hqR : Cc * om d * R ^ d = (q : ℝ) := hdat.2.2.2.1
    have hR3 : (d:ℝ)^(3/2:ℝ) ≤ R := hdat.2.2.2.2.1
    have ha0ne : a ≠ 0 := hdat.2.2.2.2.2.1
    have hmin : ∀ k : Fin d → ℤ, 0 < intQ k → intQ k ≤ R ^ 2 → ¬ LatticeGood2.kerCond a k :=
      hdat.2.2.2.2.2.2.1
    have hwt : (∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => LatticeGood2.kerCond a x),
        wt (d := d) (KK d) (a0 d) R k) ≤ (d : ℝ) ^ 4 / 2 := hdat.2.2.2.2.2.2.2
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    -- the good sample
    obtain ⟨ω, hωbad, hωinc, hωdet⟩ :=
      exists_good_sample_K d hd0 hRpos hmin hwt hSun hcover hcard
    -- the `q`-ary lattice
    haveI : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨Λ, hΛdis, hΛZL, hΛcov0, hΛmem⟩ :=
      Commons.Lattice.Counting.exists_qary_lattice_covolume_and_image (n := d) (q := q) (R := R)
        hRpos a ha0ne
    haveI := hΛdis
    haveI := hΛZL
    have hmemsmul : ∀ x : Vec d, x ∈ Λ → ∃ k : Fin d → ℤ,
        LatticeGood2.kerCond a k ∧ x = (1 / R) • intVec k := by
      intro x hx
      obtain ⟨k, hk, hkx⟩ := (hΛmem x).mp hx
      exact ⟨k, hk, by rw [hkx, smul_intVec_div]⟩
    have hΛmin : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → 1 ≤ ‖x‖ := by
      intro x hx hx0
      obtain ⟨k, hk, hkx⟩ := hmemsmul x hx
      have hk0 : k ≠ 0 := by
        intro h0
        apply hx0
        rw [hkx, h0]
        ext i; simp [intVec]
      have hpos : 0 < intQ k := Weight.intQ_pos_of_ne_zero hk0
      have hgt : R ^ 2 < intQ k := by
        by_contra hcon
        push_neg at hcon
        exact hmin k hpos hcon hk
      have hQ : intQ k = R ^ 2 * ‖x‖ ^ 2 := by
        rw [hkx]; exact intQ_of_smul hRpos k
      have hsq : 1 < ‖x‖ ^ 2 := by
        have hR2 : (0:ℝ) < R ^ 2 := by positivity
        have h : R ^ 2 * 1 < R ^ 2 * ‖x‖ ^ 2 := by rw [← hQ, mul_one]; exact hgt
        exact lt_of_mul_lt_mul_left h (le_of_lt hR2)
      nlinarith [norm_nonneg x]
    have hbox : ∀ x : Vec d, x ∈ Λ → x ≠ 0 → ‖x‖ ≤ Rb →
        ∃ i : Fin (candIdx d q R a).card, BoxL d q R a i = x := fun x hx hx0 hxn =>
      boxL_hbox hRpos Λ hmemsmul hx hx0 hxn
    -- the band and the rescaled state
    have hband : 1 ≤ (a0 d - 2 * rr d) * Rb ^ 2 := by
      have hrr' : 2 * rr d ≤ 1/2 := two_rr_le_half d hd0
      rw [Rb]; nlinarith [ha0, hrr']
    set θ : ℝ := 8 / (d:ℝ) with hθdef
    have hθeq : eps d * (2 * (d:ℝ)) * Rb ^ 2 = θ := by
      rw [hθdef, Rb, eps]
      field_simp
      ring
    have hθlt : eps d * (2 * (d:ℝ)) * Rb ^ 2 < 1 := by
      rw [hθeq, hθdef, div_lt_one hdpos]
      have h : 8 < d := by simp only [D0] at hd0; omega
      exact_mod_cast h
    have hθpos : 0 < 1 - θ := by linarith
    have hrescale := inCone_rescaled_net Rb (eps d) (a0 d) (KK d) ω (BoxL d q R a) Λ S
      hSun hcover hΛmin hbox hε hrrn ha0' (by rw [Rb]; norm_num) hband hθlt hωinc hωbad
    set AK : MatV d := proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω (KK d) with hAKdef
    have hrescale' : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ quadFormV ((1 - θ)⁻¹ • AK) x := by
      intro x hx hx0
      rw [hAKdef, ← hθeq]
      exact hrescale x hx hx0
    set A : MatV d := (1 - θ)⁻¹ • AK with hAdef
    -- positivity
    have hAKsym : (matOf d AK).IsSymm := by
      rw [hAKdef]
      exact (mem_symV).mp (GenProc.proc_mem_symV (pl := projL Rb (BoxL d q R a)) (a₀ := a0 d)
        (ε := eps d) (K := KK d) (fun A => good_projL Rb (BoxL d q R a) A) (KK d) ω)
    have hAKpd : ∀ y : Vec d, y ≠ 0 → 0 < quadFormV AK y := by
      intro y hy
      rw [hAKdef]
      have hq := (quadFormV_state_squeeze_net (R := Rb) (BoxL := BoxL d q R a)
        (a₀ := a0 d) (ε := eps d) (K := KK d) S hSun hcover hωbad hrrn (KK d) le_rfl y).1
      have hposr : 0 < a0 d - 2 * rr d := by
        have := hband; rw [Rb] at this; nlinarith
      have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
      nlinarith [hq, hposr, hyn, sq_nonneg ‖y‖]
    have hAsym : (matOf d A).IsSymm := by
      rw [hAdef, map_smul]
      exact hAKsym.smul _
    have hApd : ∀ y : Vec d, y ≠ 0 → 0 < quadFormV A y := by
      intro y hy
      rw [hAdef, quadFormV_smul]
      exact mul_pos (inv_pos.mpr hθpos) (hAKpd y hy)
    obtain ⟨φ, hφnorm, hφdet⟩ :=
      Commons.LinearAlgebra.Matrix.exists_linearMap_norm_sq_eq_sqrt_det (matOf d A)
        (posDef_matOf_of_quadFormV hAsym hApd)
    have hφnorm' : ∀ x : Vec d, ‖φ x‖ ^ 2 = quadFormV A x := by
      intro x
      rw [hφnorm x, quadFormV_eq_dotProduct]
      simp [dotProduct]
    have hφinj : Function.Injective φ := by
      intro x y hxy
      by_contra hne
      have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
      have h1 : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h2 : quadFormV A (x - y) = 0 := by
        rw [← hφnorm' (x - y), h1, norm_zero]; norm_num
      have h3 : 0 < quadFormV A (x - y) := hApd (x - y) hne'
      linarith
    -- the final lattice
    haveI hdis₁ : DiscreteTopology (Submodule.map (φ.restrictScalars ℤ) Λ) :=
      Commons.Lattice.Discrete.discreteTopology_of_linearImage φ hφinj Λ
    haveI hZL₁ : IsZLattice ℝ (Submodule.map (φ.restrictScalars ℤ) Λ) :=
      isZLattice_map_linear φ hφinj Λ
    have hcov₁ : ZLattice.covolume (Submodule.map (φ.restrictScalars ℤ) Λ)
        = |LinearMap.det φ| * ZLattice.covolume Λ :=
      Commons.Lattice.Packing.covolume_map_linear Λ φ hφinj
    -- the determinant bound
    have hdetAK : (matOf d AK).det ≤ Real.exp (Cg + 1) / (d:ℝ)^4 := by
      rw [hAKdef]
      by_cases hpos : 0 < (matOf d (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d)
          ω (KK d))).det
      · rw [show (matOf d (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω (KK d))).det
            = Real.exp (Real.log (matOf d (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d)
              ω (KK d))).det) from (Real.exp_log hpos).symm]
        exact (Real.exp_le_exp.mpr hωdet).trans (le_of_eq (exp_sub_four_log d hdpos (Cg + 1)))
      · have hle : (matOf d (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω (KK d))).det ≤ 0 :=
          le_of_not_gt hpos
        have hpos' : (0:ℝ) < Real.exp (Cg + 1) / (d:ℝ)^4 := by positivity
        linarith
    have hdetA : (matOf d A).det ≤ Real.exp (Cg + 17) / (d:ℝ)^4 := by
      have hsmul : matOf d A = (1 - θ)⁻¹ • matOf d AK := by rw [hAdef, map_smul]
      rw [hsmul, Matrix.det_smul]
      simp only [Fintype.card_fin]
      have hdetAKpos : 0 < (matOf d AK).det := (posDef_matOf_of_quadFormV hAKsym hAKpd).det_pos
      have h1 : ((1 - θ)⁻¹) ^ d ≤ Real.exp 16 := by
        rw [hθdef]
        exact inv_one_sub_eight_le_exp d hd16
      have h2 : ((1 - θ)⁻¹) ^ d * (matOf d AK).det
          ≤ Real.exp 16 * (Real.exp (Cg + 1) / (d:ℝ)^4) :=
        mul_le_mul h1 hdetAK (le_of_lt hdetAKpos) (Real.exp_nonneg _)
      refine h2.trans (le_of_eq ?_)
      rw [show Real.exp 16 * (Real.exp (Cg + 1) / (d:ℝ)^4)
          = Real.exp 16 * Real.exp (Cg + 1) / (d:ℝ)^4 from by ring,
        show Real.exp 16 * Real.exp (Cg + 1) = Real.exp (Cg + 17) by
          rw [← Real.exp_add]; congr 1; ring]
    have hsqrt : |LinearMap.det φ| ≤ Real.exp ((Cg + 17) / 2) / (d:ℝ)^2 := by
      rw [hφdet, Real.sqrt_le_left (by positivity)]
      refine hdetA.trans (le_of_eq ?_)
      rw [div_pow, ← Real.exp_nat_mul, show ((d:ℝ)^2)^2 = (d:ℝ)^4 by ring]
      congr 2
      ring
    -- the covolume of the `q`-ary lattice
    have hωom : 0 < om d := by
      rw [om]; exact Submission.LatticeGood.omega_pos d (by omega)
    have hcovΛ : ZLattice.covolume Λ ≤ Cc * om d := by
      rw [hΛcov0, ← hqR]
      rw [show Cc * om d * R ^ d / R ^ d = Cc * om d from by
        rw [mul_div_assoc, div_self (pow_ne_zero d (ne_of_gt hRpos)), mul_one]]
    refine ⟨Submodule.map (φ.restrictScalars ℤ) Λ, hdis₁, hZL₁, ?_, ?_⟩
    · intro v hv
      obtain ⟨x, hx, hxv⟩ := (Submodule.mem_map).mp v.2
      have hx0 : x ≠ 0 := by
        intro h0
        apply hv
        apply Subtype.ext
        rw [← hxv, h0]
        simp
      have h1 : 1 ≤ quadFormV A x := hrescale' x hx hx0
      have h2 : ‖(v : EuclideanSpace ℝ (Fin d))‖ ^ 2 = quadFormV A x := by
        rw [← hxv]
        exact hφnorm' x
      have h3 : (1:ℝ) ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by rw [h2]; exact h1
      nlinarith [norm_nonneg (v : EuclideanSpace ℝ (Fin d))]
    · calc ZLattice.covolume (Submodule.map (φ.restrictScalars ℤ) Λ)
          = |LinearMap.det φ| * ZLattice.covolume Λ := hcov₁
        _ ≤ (Real.exp ((Cg + 17) / 2) / (d:ℝ)^2) * (Cc * om d) :=
            mul_le_mul hsqrt hcovΛ (le_of_lt (ZLattice.covolume_pos Λ volume)) (by positivity)
        _ ≤ om d / ((1 / (Real.exp ((Cg + 17) / 2 + 1) * Cc * 4)) * ((d:ℝ) - 1) ^ 2) := by
            have hEpos : (0:ℝ) < Real.exp ((Cg + 17) / 2 + 1) := Real.exp_pos _
            have hE17 : (0:ℝ) < Real.exp ((Cg + 17) / 2) := Real.exp_pos _
            have hCcpos : (0:ℝ) < Cc := by norm_num [Cc]
            have hd1 : (0:ℝ) < (d:ℝ) - 1 := by linarith
            have hA : Real.exp ((Cg + 17) / 2 + 1) * Cc * 4 ≠ 0 := ne_of_gt (by positivity)
            have hB : ((d:ℝ) - 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
            rw [show Real.exp ((Cg + 17) / 2) / (d:ℝ)^2 * (Cc * om d)
                = (Real.exp ((Cg + 17) / 2) * (Cc * om d)) / (d:ℝ)^2 from by ring]
            rw [show om d / ((1 / (Real.exp ((Cg + 17) / 2 + 1) * Cc * 4)) * ((d:ℝ) - 1) ^ 2)
                = (om d * (Real.exp ((Cg + 17) / 2 + 1) * Cc * 4)) / ((d:ℝ) - 1) ^ 2 from by
              field_simp]
            rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (d:ℝ)^2)
              (by positivity : (0:ℝ) < ((d:ℝ) - 1)^2)]
            have hE : Real.exp ((Cg + 17) / 2 + 1) = Real.exp ((Cg + 17) / 2) * Real.exp 1 := by
              rw [← Real.exp_add]
            rw [hE]
            have h1 : ((d:ℝ) - 1)^2 ≤ (d:ℝ)^2 :=
              pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ (d:ℝ) - 1) (by linarith : (d:ℝ) - 1 ≤ (d:ℝ)) 2
            have he1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
            have h2 : (d:ℝ)^2 ≤ Real.exp 1 * 4 * (d:ℝ)^2 := by nlinarith [he1, sq_nonneg (d:ℝ)]
            have h3 : ((d:ℝ) - 1)^2 ≤ Real.exp 1 * 4 * (d:ℝ)^2 := le_trans h1 h2
            have h4 : Real.exp ((Cg + 17) / 2) * Cc * om d * ((d:ℝ) - 1)^2
                ≤ Real.exp ((Cg + 17) / 2) * Cc * om d * (Real.exp 1 * 4 * (d:ℝ)^2) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
            linarith [h4]

end

end Submission.Finish
