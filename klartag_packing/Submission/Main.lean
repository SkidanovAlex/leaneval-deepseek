import Mathlib
import Submission.Setup
import Submission.DriftBound
import Submission.OmBound
import Submission.Commons.GeometryOfNumbers.Counting.exists_prime_radius_C_large
import Submission.Commons.GeometryOfNumbers.Counting.sum_tailG_annulus_le_of_shell
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_two_omega
import Submission.Commons.Analysis.Gaussian.integral_shell_weight_le
import Submission.Commons.Lattice.Counting.exists_qary_lattice_covolume_and_image
import Submission.Commons.Probability.Gaussian.integral_norm_pow_four_stdGaussian_le

/-!
# Klartag's lattice sphere packing theorem: the main assembly

This file assembles the proof of `Submission.Helpers.klartag_lattice_large` from the
exploration process of `Submission.PLAN_V4.md`, the contact estimate of `Submission.PLAN_V10.md`
and the parameters recorded in `Submission.Setup`.
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
open Classical
open Commons.GeometryOfNumbers.Counting

set_option maxHeartbeats 4000000

namespace Submission.Main

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {q : ℕ} {R : ℝ} {a : Fin d → ZMod q}

/-! ## The weighted lattice sum and the point count -/

/-- The weighted sum over the integer points of the ball of radius `2R` equals the radial
profile summed over the annulus `R < ‖x‖`. -/
lemma sum_wt_eq {K : ℕ} (hR : 0 < R) :
    (∑ x ∈ intPoints (d := d) (2 * R), wt (d := d) K (a0 d) R x)
      = ∑ x ∈ (intPoints (d := d) (2 * R)).filter (fun x => R < ‖intVec x‖),
          Submission.Weight.prof (d := d) K (a0 d) R ‖intVec x‖ := by
  classical
  rw [← Finset.sum_subset (Finset.filter_subset (fun x : Fin d → ℤ => R < ‖intVec x‖) _) ?_]
  · refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    refine wt_eq_prof K (a0 d) R hR.le ?_ ?_
    · have h := hx.2
      rw [intQ]
      exact sq_lt_sq.mpr (by rw [abs_of_nonneg hR.le, abs_of_nonneg (norm_nonneg _)]; exact h)
    · have h := (mem_intPoints (d := d) (R := 2 * R)).mp hx.1
      rw [intQ] at h ⊢
      nlinarith [h]
  · intro x hx hxnot
    simp only [Finset.mem_filter] at hx hxnot
    refine wt_eq_zero_of_not_annulus K (a0 d) R ?_
    rintro ⟨h1, -⟩
    have h2 : ‖intVec x‖ ≤ R := le_of_not_gt fun hc => hxnot ⟨hx, hc⟩
    rw [intQ] at h1
    nlinarith [h2, norm_nonneg (intVec x)]

/-- The number of integer points of the ball of radius `R` is at most `2 ω_d R^d`. -/
lemma card_intPoints_le {ω : ℝ} (hd1 : 1 ≤ d) (hR : 1 ≤ R)
    (hRbig : (d : ℝ) ^ (3 / 2 : ℝ) ≤ R)
    (hω : ω = om d) :
    (((intPoints (d := d) R).filter (fun x => 0 < intQ x)).card : ℝ) ≤ 2 * ω * R ^ d := by
  have h1 : ((intPoints (d := d) R).filter (fun x => 0 < intQ x)).card
      ≤ (intPoints (d := d) R).card := Finset.card_filter_le _ _
  have h2 : (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ)
      ≤ 2 * om d * R ^ d := by
    have := card_int_points_ball_le_two_omega (d := d) hd1 hR hRbig
    simpa [om] using this
  have h3 : ((intPoints (d := d) R).card : ℝ)
      ≤ (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ) := by
    have e1 : (intPoints (d := d) R).card
        = Nat.card ↥((intPoints (d := d) R) : Set (Fin d → ℤ)) :=
      (Submission.LatticeGood.natCard_finset_coe _).symm
    have e2 : ((intPoints (d := d) R) : Set (Fin d → ℤ))
        = {x : Fin d → ℤ | (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} := by
      rw [intPoints]
      exact Set.Finite.coe_toFinset _
    rw [e1, e2]
    exact le_of_eq rfl
  rw [hω]
  calc (((intPoints (d := d) R).filter (fun x => 0 < intQ x)).card : ℝ)
      ≤ ((intPoints (d := d) R).card : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h3
    _ ≤ 2 * om d * R ^ d := h2

/-- **The weight bound.**  The total weight of the integer points of the ball of radius `2R` is
at most `10^7 d^4 ω_d R^d`. -/
lemma hWsum_le {ω : ℝ} (hd : 100000 ≤ d) {K : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hRbig : (d : ℝ) ^ (3 / 2 : ℝ) ≤ R)
    (hK : (K : ℝ) ≤ 16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1)
    (hshell : ∫ y in (1 : ℝ)..2, y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
          (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z})
      ≤ 10 ^ 6 * (d : ℝ) ^ 3)
    (hω : ω = om d) :
    (∑ x ∈ intPoints (d := d) (2 * R), wt (d := d) K (a0 d) R x)
      ≤ 10 ^ 7 * (d : ℝ) ^ 4 * ω * R ^ d := by
  rw [sum_wt_eq (d := d) (K := K) (R := R) (by linarith)]
  have hmain := sum_tailG_annulus_le_of_shell (d := d) hd (K := K) (R := R) hR hRbig hK hshell
  have hcongr : (∑ x ∈ (intPoints (d := d) (2 * R)).filter (fun x => R < ‖intVec x‖),
      Submission.Weight.prof (d := d) K (a0 d) R ‖intVec x‖)
      = ∑ x ∈ ((finite_int_points_ball (d := d) (2 * R)).toFinset.filter
          (fun x : Fin d → ℤ => R < ‖intVec x‖)),
        ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
          (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - R ^ 2 / ‖intVec x‖ ^ 2)
            * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z} := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    rw [Submission.Weight.prof]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmax : max ‖intVec x‖ R = ‖intVec x‖ := max_eq_left hx.2.le
    rw [hmax]
    rfl
  rw [hcongr]
  have hgoal : (10:ℝ) ^ 7 * (d : ℝ) ^ 4 * ω * R ^ d
      = 10 ^ 7 * (d : ℝ) ^ 4
        * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal * R ^ d := by
    rw [hω]; rfl
  rw [hgoal]
  exact hmain


/-! ## The second and fourth moments of the state -/

lemma eps_sq_eq (d : ℕ) : eps d ^ 2 = 1 / (d : ℝ) ^ 4 := by
  rw [eps]; ring_nf

/-- `∫ ‖H‖² ≤ 17 log d`. -/
lemma integral_norm_sq_le (hε : 0 ≤ eps d) (hd : 2 ≤ d) :
    (∫ ω : Fin (KK d) → MatV d × MatV d,
        ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 ∂(sampleLaw d (KK d)))
      ≤ 17 * Real.log d := by
  have hsq := Moment.integral_norm_sq_state (d := d) (R := Rb) (BoxL := BoxL d q R a)
    (a₀ := a0 d) (ε := eps d) (KK d) hε
  rw [show (fun ω : Fin (KK d) → MatV d × MatV d =>
      ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2)
      = fun ω => ‖stateK (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω‖ ^ 2 from rfl,
    hsq]
  have hN : ∀ k : Fin (KK d),
      (∫ ω : Fin (KK d) → MatV d × MatV d,
        Nfun Rb (BoxL d q R a) (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω k)
          ∂(sampleLaw d (KK d))) ≤ ((d * d : ℕ) : ℝ) := by
    intro k
    have h := MeasureTheory.integral_mono
      (Moment.integrable_Nfun_comp (d := d) (R := Rb) (BoxL := BoxL d q R a) (a₀ := a0 d)
        (ε := eps d) (KK d) k)
      (MeasureTheory.integrable_const ((d * d : ℕ) : ℝ))
      (fun ω => Moment.Nfun_le (d := d) (R := Rb) (BoxL := BoxL d q R a) _)
    simpa using h
  have hsum : (∑ k : Fin (KK d), ∫ ω : Fin (KK d) → MatV d × MatV d,
        Nfun Rb (BoxL d q R a) (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω k)
          ∂(sampleLaw d (KK d))) ≤ (KK d : ℝ) * ((d * d : ℕ) : ℝ) := by
    calc (∑ k : Fin (KK d), ∫ ω : Fin (KK d) → MatV d × MatV d,
          Nfun Rb (BoxL d q R a) (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω k)
            ∂(sampleLaw d (KK d)))
        ≤ ∑ _k : Fin (KK d), ((d * d : ℕ) : ℝ) := Finset.sum_le_sum fun k _ => hN k
      _ = (KK d : ℝ) * ((d * d : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_left hsum (sq_nonneg (eps d))).trans ?_
  have hK : (KK d : ℝ) ≤ 16 * (d : ℝ) ^ 2 * Real.log d + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hpos : (0:ℝ) < (d : ℝ) := by positivity
  have hlog : 1 / (d : ℝ) ^ 2 ≤ Real.log d := by
    have h1 : (2:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h2 : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) h1
    have h3 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h4 : 1 / (d : ℝ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hdd : ((d * d : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
  rw [eps_sq_eq, hdd]
  have h1 : 1 / (d : ℝ) ^ 4 * ((KK d : ℝ) * (d : ℝ) ^ 2)
      ≤ 1 / (d : ℝ) ^ 4 * ((16 * (d : ℝ) ^ 2 * Real.log d + 1) * (d : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK (by positivity)) (by positivity)
  have h2 : 1 / (d : ℝ) ^ 4 * ((16 * (d : ℝ) ^ 2 * Real.log d + 1) * (d : ℝ) ^ 2)
      = 16 * Real.log d + 1 / (d : ℝ) ^ 2 := by
    field_simp
  rw [h2] at h1
  nlinarith [h1, hlog]


/-! ## The data: the q-ary covector and the lattice -/

/-- For `d ≥ D0`, the q-ary first-moment construction produces a prime `q`, a radius `R ≥ d^{3/2}`
and a covector `a` with the minimum-norm property and the weight bound. -/
theorem exists_data (d : ℕ) (hd : D0 ≤ d) {K : ℕ}
    (hK : (K : ℝ) ≤ 16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1)
    (hshell : ∫ y in (1 : ℝ)..2, y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
          (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z})
      ≤ 10 ^ 6 * (d : ℝ) ^ 3) :
    ∃ (q : ℕ) (R : ℝ) (a : Fin d → ZMod q),
      q.Prime ∧ 1 ≤ R ∧ 2 * R < (q : ℝ) ∧ Cc * om d * R ^ d = (q : ℝ) ∧
      (d : ℝ) ^ (3 / 2 : ℝ) ≤ R ∧ a ≠ 0 ∧
      (∀ k : Fin d → ℤ, 0 < intQ k → intQ k ≤ R ^ 2 → ¬ LatticeGood2.kerCond a k) ∧
      (∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => LatticeGood2.kerCond a x),
          wt (d := d) K (a0 d) R k) ≤ (d : ℝ) ^ 4 / 2 := by
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have hd29 : 29 ≤ d := by simp only [D0] at hd; omega
  have hd1 : 1 ≤ d := by omega
  have hd100k : 100000 ≤ d := by simp only [D0] at hd; omega
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1R
  have hωpos : 0 < om d := by
    rw [om]; exact Submission.LatticeGood.omega_pos d (by omega)
  have hω1 : om d ≤ 1 := OmBound.omega_le_one hd29
  have hC4 : (4 : ℝ) ≤ Cc := by norm_num [Cc]
  obtain ⟨q, hq, R, hRpos, hRq, hqR, hR3, hRbig⟩ :=
    exists_prime_radius_C_large (ω := om d) (C := Cc) hd2 hωpos hω1 hC4
  have hR1 : 1 ≤ R := by
    refine le_trans ?_ hRbig
    calc (1 : ℝ) = (1 : ℝ) ^ (3 / 2 : ℝ) := by norm_num
      _ ≤ (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hd1R (by norm_num)
  have hcount := card_intPoints_le (d := d) (ω := om d) hd1 hR1 hRbig rfl
  have hWsum := hWsum_le (d := d) (ω := om d) hd100k (K := K) hR1 hRbig hK hshell rfl
  have hCcge : (10 : ℝ) ^ 9 ≤ Cc := le_of_eq (by norm_num [Cc])
  obtain ⟨a, ha0, hmin, hwt⟩ :=
    LatticeGood2.exists_covector (d := d) (q := q) hd2 hq hRpos hR1 hRq hωpos hC4 hqR hcount hWsum hCcge
  exact ⟨q, R, a, hq, hR1, hRq, hqR, hRbig, ha0, hmin, hwt⟩


/-! ## The contact bound -/

/-- **The total expected number of contacts is at most `4d⁴`.** -/
theorem contact_bound_applied (d : ℕ) (hd : D0 ≤ d) {q : ℕ} {R : ℝ} {a : Fin d → ZMod q}
    (hRpos : 0 < R)
    (hmin : ∀ k : Fin d → ℤ, 0 < intQ k → intQ k ≤ R ^ 2 → ¬ LatticeGood2.kerCond a k)
    (hwt : (∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => LatticeGood2.kerCond a x),
        wt (d := d) (KK d) (a0 d) R k) ≤ (d : ℝ) ^ 4 / 2) :
    (∑ k : Fin (KK d), ∫ ω : Fin (KK d) → MatV d × MatV d,
        ((violSet Rb (BoxL d q R a) (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω k)).card : ℝ)
          ∂(sampleLaw d (KK d)))
      ≤ 4 * (d : ℝ) ^ 4 := by
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have hM : (∑ i : Fin (candIdx d q R a).card,
      Wt (d := d) (KK d) (a0 d) (eps d) (BoxL d q R a i)) ≤ (d : ℝ) ^ 4 / 2 :=
    sum_Wt_BoxL (d := d) (q := q) (R := R) (a := a) hRpos hmin (KK d) (a0 d) hwt
  have h := contact_bound (d := d) Rb (BoxL d q R a) (a₀ := a0 d) (ε := eps d)
    (K := KK d) (boxL_injective (d := d) (q := q) (R := R) (a := a) hRpos)
    (eps_pos d (by omega)) (one_lt_a0 (d := d) hd2)
    (fun i => boxL_min (d := d) (q := q) (R := R) (a := a) hRpos hd2 hmin i)
    (fun i => boxL_norm_le (d := d) (q := q) (R := R) (a := a) hRpos i) ((d:ℝ)^4/2) hM
  linarith [h]


/-! ## The measure of the bad net event -/

lemma rr_nonneg (d : ℕ) : 0 ≤ rr d := by
  rw [rr]; positivity

lemma log_twelve_le : Real.log 12 ≤ 11 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 12)
  linarith

/-- **The net-based bad event has probability at most `e^{-d}`.** -/
theorem badNet_measure_le (d : ℕ) (hd : D0 ≤ d) {q : ℕ} {R : ℝ} {a : Fin d → ZMod q}
    {S : Finset (Vec d)} (hSun : ∀ x ∈ S, ‖x‖ = 1) (hcard : (S.card : ℝ) ≤ (12:ℝ) ^ d) :
    (sampleLaw d (KK d)).real
        (badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)) ≤ Real.exp (-(d : ℝ)) := by
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hLpos : 0 < Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hLhalf : (1:ℝ)/2 ≤ Real.log (d:ℝ) := by
    have h1 : Real.log 2 ≤ Real.log (d:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hd2)
    linarith [Real.log_two_gt_d9]
  have hε : (0:ℝ) ≤ eps d := (eps_pos d (by omega)).le
  have hK : (KK d : ℝ) < 16 * (d:ℝ)^2 * Real.log d + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hKm : 16 * (d:ℝ)^2 * Real.log d ≤ (KK d : ℝ) := Nat.le_ceil _
  have hKpos : (0:ℝ) < (KK d : ℝ) := by
    have : (0:ℝ) < 16 * (d:ℝ)^2 * Real.log d := by positivity
    linarith
  have h1 := Good.badNet_measureReal_le (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S
    hSun (rr_nonneg d) hε
  have hsq : Real.sqrt (d:ℝ) ^ 2 = (d:ℝ) := Real.sq_sqrt hdpos.le
  have hrrsq : (rr d)^2 = 576 * Real.log (d:ℝ) / (d:ℝ) := by
    rw [rr, div_pow, mul_pow, hsq, Real.sq_sqrt hLpos.le]
    norm_num
  have hratio : 17 * (d:ℝ) ≤ (rr d)^2 / (2 * (KK d : ℝ) * (eps d)^2) := by
    rw [hrrsq, eps_sq_eq]
    rw [show (576 * Real.log (d:ℝ) / (d:ℝ)) / (2 * (KK d : ℝ) * (1 / (d:ℝ)^4))
        = 288 * Real.log (d:ℝ) * (d:ℝ)^3 / (KK d : ℝ) from by
      field_simp
      ring]
    rw [le_div_iff₀ hKpos]
    have h2 : 17 * (d:ℝ) * (KK d : ℝ) < 17 * (d:ℝ) * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) :=
      mul_lt_mul_of_pos_left hK (by positivity : (0:ℝ) < 17 * (d:ℝ))
    have hd2R : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd2
    have hd3 : 4 * (d:ℝ) ≤ (d:ℝ)^3 := by nlinarith
    have hkey : 17 * (d:ℝ) ≤ 16 * Real.log (d:ℝ) * (d:ℝ)^3 := by
      nlinarith [hd3, hLhalf, hd2R, Real.log_nonneg hd1R]
    nlinarith [h2, hkey]
  have hexp : Real.exp (-((rr d)^2) / (2 * (KK d : ℝ) * (eps d)^2)) ≤ Real.exp (-(17 * (d:ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_le_neg_iff]
    exact hratio
  refine h1.trans ?_
  refine (mul_le_mul_of_nonneg_right hcard
    (by positivity : (0:ℝ) ≤ 8 * Real.exp (-((rr d)^2) / (2 * (KK d : ℝ) * (eps d)^2)))).trans ?_
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 8))
    (by positivity : (0:ℝ) ≤ (12:ℝ) ^ d)
  refine h2.trans ?_
  have h3 : (12:ℝ) ^ d ≤ Real.exp (11 * (d:ℝ)) := by
    have h4 : (12:ℝ) ≤ Real.exp 11 := by
      have h1 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have h3 : (2:ℝ)^11 ≤ (Real.exp 1)^11 := pow_le_pow_left₀ (by norm_num) h2.le 11
      rw [h1]
      norm_num at h3 ⊢
      linarith
    calc (12:ℝ) ^ d ≤ (Real.exp 11) ^ d := pow_le_pow_left₀ (by norm_num) h4 d
      _ = Real.exp (11 * (d:ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
  refine le_trans (mul_le_mul_of_nonneg_right h3 (by positivity)) ?_
  have h5 : Real.log 8 ≤ 5 * (d:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8)
    have hd2R : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd2
    linarith
  have h6 : Real.exp (11 * (d:ℝ)) * (8 * Real.exp (-(17 * (d:ℝ)))) ≤ Real.exp (-(d:ℝ)) := by
    have hpow : Real.exp (11 * (d:ℝ)) * Real.exp (-(17 * (d:ℝ))) = Real.exp (-(6 * (d:ℝ))) := by
      rw [← Real.exp_add]; ring_nf
    rw [show Real.exp (11 * (d:ℝ)) * (8 * Real.exp (-(17 * (d:ℝ))))
        = 8 * (Real.exp (11 * (d:ℝ)) * Real.exp (-(17 * (d:ℝ)))) from by ring, hpow]
    rw [show (8:ℝ) = Real.exp (Real.log 8) from (Real.exp_log (by norm_num)).symm, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith [h5]
  exact h6


/-! ## The fourth moment of the state -/

lemma integrable_eval_norm_pow_four (K : ℕ) (j : Fin K) :
    Integrable (fun u : Fin K → MatV d × MatV d => ‖(u j).1‖ ^ 4) (sampleLaw d K) := by
  have hg : AEMeasurable (fun u : Fin K → MatV d × MatV d => (u j).1) (sampleLaw d K) :=
    ((measurable_pi_apply j).fst).aemeasurable
  have hmem := ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (MatV d))
    4 (by norm_num)
  have hnorm : Integrable (fun x : MatV d => ‖x‖ ^ 4) (ProbabilityTheory.stdGaussian (MatV d)) :=
    hmem.integrable_norm_pow (p := 4) (by norm_num)
  have h1 : Integrable (fun x : MatV d => ‖x‖ ^ 4)
      ((sampleLaw d K).map (fun u : Fin K → MatV d × MatV d => (u j).1)) := by
    rw [Submission.Rescale.sampleLaw_map_fst]; exact hnorm
  exact (MeasureTheory.integrable_map_measure
    ((continuous_norm.pow 4).measurable.aestronglyMeasurable) hg).mp h1

lemma integral_eval_norm_pow_four (K : ℕ) (j : Fin K) :
    (∫ u : Fin K → MatV d × MatV d, ‖(u j).1‖ ^ 4 ∂(sampleLaw d K))
      = ∫ x : MatV d, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian (MatV d)) := by
  have hg : AEMeasurable (fun u : Fin K → MatV d × MatV d => (u j).1) (sampleLaw d K) :=
    ((measurable_pi_apply j).fst).aemeasurable
  rw [← MeasureTheory.integral_map (μ := sampleLaw d K)
      (φ := fun u : Fin K → MatV d × MatV d => (u j).1) (f := fun x : MatV d => ‖x‖ ^ 4) hg
      ((continuous_norm.pow 4).aestronglyMeasurable),
    Submission.Rescale.sampleLaw_map_fst]

/-- A Hölder-type bound: `(∑ aⱼ)⁴ ≤ K³ ∑ aⱼ⁴`. -/
lemma sum_pow_four_le_card_pow_three_mul (K : ℕ) (a : Fin K → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (∑ j, a j) ^ 4 ≤ (K : ℝ) ^ 3 * ∑ j, (a j) ^ 4 := by
  have h1 : (∑ j, a j) ^ 2 ≤ (K : ℝ) * ∑ j, (a j) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin K))) (f := a)
  have h2 : (∑ j, (a j) ^ 2) ^ 2 ≤ (K : ℝ) * ∑ j, ((a j) ^ 2) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin K)))
      (f := fun j => (a j) ^ 2)
  have heq : ∀ j, ((a j) ^ 2) ^ 2 = (a j) ^ 4 := fun j => by ring
  simp only [heq] at h2
  calc (∑ j, a j) ^ 4 = ((∑ j, a j) ^ 2) ^ 2 := by ring
    _ ≤ ((K : ℝ) * ∑ j, (a j) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (K : ℝ) ^ 2 * (∑ j, (a j) ^ 2) ^ 2 := by ring
    _ ≤ (K : ℝ) ^ 2 * ((K : ℝ) * ∑ j, (a j) ^ 4) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (K : ℝ) ^ 3 * ∑ j, (a j) ^ 4 := by ring

/-- **The fourth moment of the state.** -/
lemma integral_norm_pow_four_le (hε : 0 ≤ eps d) (hd : 2 ≤ d) :
    (∫ ω : Fin (KK d) → MatV d × MatV d,
        ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 4 ∂(sampleLaw d (KK d)))
      ≤ 3 * (16 * (d : ℝ) ^ 2 * Real.log d + 1) ^ 4 := by
  have hpt : ∀ ω : Fin (KK d) → MatV d × MatV d,
      ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 4
        ≤ (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j, ‖(ω j).1‖ ^ 4 := by
    intro ω
    have h1 : ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖
        ≤ ∑ j : Fin (KK d), eps d * ‖(ω j).1‖ :=
      Moment.norm_stateK_le (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε ω
    have h3 := sum_pow_four_le_card_pow_three_mul (KK d)
      (fun j => eps d * ‖(ω j).1‖) (fun j => mul_nonneg hε (norm_nonneg _))
    have h4 : (∑ j : Fin (KK d), (eps d * ‖(ω j).1‖) ^ 4)
        = (eps d) ^ 4 * ∑ j : Fin (KK d), ‖(ω j).1‖ ^ 4 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow]
    rw [h4] at h3
    calc ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 4
        ≤ (∑ j : Fin (KK d), eps d * ‖(ω j).1‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      _ ≤ (KK d : ℝ) ^ 3 * ((eps d) ^ 4 * ∑ j : Fin (KK d), ‖(ω j).1‖ ^ 4) := h3
      _ = (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j : Fin (KK d), ‖(ω j).1‖ ^ 4 := by ring
  have hint : Integrable (fun ω : Fin (KK d) → MatV d × MatV d =>
      (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j, ‖(ω j).1‖ ^ 4) (sampleLaw d (KK d)) :=
    (MeasureTheory.integrable_finsetSum (s := Finset.univ) (fun j _ =>
      integrable_eval_norm_pow_four (d := d) (KK d) j)).const_mul _
  have h1 : (∫ ω : Fin (KK d) → MatV d × MatV d,
        ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 4 ∂(sampleLaw d (KK d)))
      ≤ ∫ ω : Fin (KK d) → MatV d × MatV d,
          (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j, ‖(ω j).1‖ ^ 4 ∂(sampleLaw d (KK d)) :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
      hint (Filter.Eventually.of_forall hpt)
  have hval : (∫ ω : Fin (KK d) → MatV d × MatV d,
        (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j, ‖(ω j).1‖ ^ 4 ∂(sampleLaw d (KK d)))
      = (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ((KK d : ℝ)
          * ∫ x : MatV d, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian (MatV d))) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum]
    · rw [show (∑ j : Fin (KK d), ∫ ω : Fin (KK d) → MatV d × MatV d,
            ‖(ω j).1‖ ^ 4 ∂(sampleLaw d (KK d)))
          = ∑ _j : Fin (KK d),
              ∫ x : MatV d, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian (MatV d)) from
        Finset.sum_congr rfl fun j _ => integral_eval_norm_pow_four (d := d) (KK d) j]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · intro j _
      exact integrable_eval_norm_pow_four (d := d) (KK d) j
  have hfour : (∫ x : MatV d, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian (MatV d)))
      ≤ 3 * (Fintype.card (Fin d × Fin d) : ℝ) ^ 4 := by
    have h := Commons.Probability.Gaussian.integral_norm_pow_four_stdGaussian_le
      (ι := Fin d × Fin d)
    have heq : (3:ℝ) * (Fintype.card (Fin d × Fin d) : ℝ) ^ 2
          * (Fintype.card (Fin d × Fin d) : ℝ) ^ 2
        = 3 * (Fintype.card (Fin d × Fin d) : ℝ) ^ 4 := by ring
    rw [heq] at h
    exact h
  have hcard : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  rw [hval] at h1
  refine h1.trans ?_
  have heps4 : (eps d) ^ 4 = 1 / (d : ℝ) ^ 8 := by
    rw [eps, div_pow, one_pow]; ring_nf
  rw [heps4]
  have hK4 : (KK d : ℝ) ≤ 16 * (d : ℝ) ^ 2 * Real.log d + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have h3 : 1 / (d : ℝ) ^ 8 * (KK d : ℝ) ^ 3
        * ((KK d : ℝ) * (3 * ((d : ℝ) ^ 2) ^ 4))
      = 3 * (KK d : ℝ) ^ 4 := by
    field_simp
  have h4 : 1 / (d : ℝ) ^ 8 * (KK d : ℝ) ^ 3
        * ((KK d : ℝ) * (∫ x : MatV d, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian (MatV d))))
      ≤ 1 / (d : ℝ) ^ 8 * (KK d : ℝ) ^ 3 * ((KK d : ℝ) * (3 * ((d : ℝ) ^ 2) ^ 4)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    have h := hfour
    rw [hcard] at h
    exact h
  rw [h3] at h4
  refine h4.trans ?_
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hK4 4) (by norm_num)

/-! ## The bad-event error terms and the drift bound -/

lemma measurable_HH (hε : 0 ≤ eps d) :
    Measurable (fun ω : Fin (KK d) → MatV d × MatV d =>
      ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖) :=
  (Moment.measurable_stateK (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d)).norm

lemma hpt_norm_pow_four (hε : 0 ≤ eps d) (ω : Fin (KK d) → MatV d × MatV d) :
    ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 4
      ≤ (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j, ‖(ω j).1‖ ^ 4 := by
  have h1 : ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖
      ≤ ∑ j : Fin (KK d), eps d * ‖(ω j).1‖ :=
    Moment.norm_stateK_le (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε ω
  have h3 := sum_pow_four_le_card_pow_three_mul (KK d)
    (fun j => eps d * ‖(ω j).1‖) (fun j => mul_nonneg hε (norm_nonneg _))
  have h4 : (∑ j : Fin (KK d), (eps d * ‖(ω j).1‖) ^ 4)
      = (eps d) ^ 4 * ∑ j : Fin (KK d), ‖(ω j).1‖ ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]
  rw [h4] at h3
  calc ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 4
      ≤ (∑ j : Fin (KK d), eps d * ‖(ω j).1‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
    _ ≤ (KK d : ℝ) ^ 3 * ((eps d) ^ 4 * ∑ j : Fin (KK d), ‖(ω j).1‖ ^ 4) := h3
    _ = (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j : Fin (KK d), ‖(ω j).1‖ ^ 4 := by ring

lemma integrable_norm_pow_four (hε : 0 ≤ eps d) :
    Integrable (fun ω : Fin (KK d) → MatV d × MatV d =>
      ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 4) (sampleLaw d (KK d)) := by
  have hint : Integrable (fun ω : Fin (KK d) → MatV d × MatV d =>
      (eps d) ^ 4 * (KK d : ℝ) ^ 3 * ∑ j, ‖(ω j).1‖ ^ 4) (sampleLaw d (KK d)) :=
    (MeasureTheory.integrable_finsetSum (s := Finset.univ) (fun j _ =>
      integrable_eval_norm_pow_four (d := d) (KK d) j)).const_mul _
  refine MeasureTheory.Integrable.mono' hint
    ((measurable_HH (d := d) (q := q) (R := R) (a := a) hε).pow_const 4).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_of_nonneg (by positivity)]
  exact hpt_norm_pow_four (d := d) (q := q) (R := R) (a := a) hε ω

lemma holderConj_two : (2:ℝ).HolderConjugate 2 :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Cauchy–Schwarz on a measurable set: `∫_s f ≤ √(∫ f²) · √(μ s)` for `f ≥ 0`. -/
lemma setIntegral_le_sqrt_mul_sqrt {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} {s : Set α} (hf : ∀ x, 0 ≤ f x)
    (hfmeas : AEStronglyMeasurable f μ)
    (hfin : Integrable (fun x => f x ^ 2) μ) (hsm : MeasurableSet s) :
    ∫ x in s, f x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hmf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas).mpr (by simpa using hfin)
  have hmf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hmf
  have hmg : MemLp (s.indicator (fun _ => (1:ℝ))) (ENNReal.ofReal 2) μ := by
    simpa using MemLp.indicator hsm (memLp_const (1:ℝ))
  have h0g : ∀ x, 0 ≤ s.indicator (fun _ => (1:ℝ)) x :=
    fun x => Set.indicator_nonneg (by norm_num) x
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg holderConj_two
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall h0g) hmf' hmg
  have hEq : (fun x => s.indicator f x)
      = fun x => f x * (s.indicator (fun _ => (1:ℝ))) x := by
    funext x
    by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [← integral_indicator hsm, show (∫ x, s.indicator f x ∂μ)
      = ∫ x, f x * (s.indicator (fun _ => (1:ℝ))) x ∂μ from by rw [hEq]]
  refine hholder.trans (le_of_eq ?_)
  have h1 : (∫ x, f x ^ (2:ℝ) ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Real.rpow_two (f x)
  have h2 : (∫ x, (s.indicator (fun _ => (1:ℝ))) x ^ (2:ℝ) ∂μ) = μ.real s := by
    rw [show (fun x => (s.indicator (fun _ => (1:ℝ))) x ^ (2:ℝ))
        = s.indicator (fun _ => (1:ℝ)) from by
      funext x
      by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx,
        Real.rpow_two]]
    exact integral_indicator_one hsm
  rw [h1, h2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-! ## Numeric helpers for the error terms -/

/-- If `log C ≤ x` and `C > 0` then `C·e^{-x} ≤ 1`. -/
lemma mul_exp_neg_le_one {C x : ℝ} (hC : 0 < C) (h : Real.log C ≤ x) :
    C * Real.exp (-x) ≤ 1 := by
  have h1 : C = Real.exp (Real.log C) := (Real.exp_log hC).symm
  rw [h1, ← Real.exp_add]
  refine Real.exp_le_one_iff.mpr ?_
  linarith

lemma log_d_ge_one {d : ℕ} (hd : D0 ≤ d) : 1 ≤ Real.log (d : ℝ) := by
  have hd3 : (3:ℝ) ≤ (d:ℝ) := by
    have : 3 ≤ d := by simp only [D0] at hd; omega
    exact_mod_cast this
  have h2 : Real.exp 1 < (d:ℝ) :=
    lt_of_lt_of_le (by linarith [Real.exp_one_lt_d9]) hd3
  exact (Real.le_log_iff_exp_le (by positivity)).mpr h2.le

lemma log_d_le_two_sqrt {d : ℕ} (hd : D0 ≤ d) : Real.log (d:ℝ) ≤ 2 * Real.sqrt (d:ℝ) - 2 := by
  have hpos : (0:ℝ) < (d:ℝ) := by
    have : 0 < d := by simp only [D0] at hd; omega
    exact_mod_cast this
  have h1 : Real.log (Real.sqrt (d:ℝ)) ≤ Real.sqrt (d:ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpos)
  rw [Real.log_sqrt hpos.le] at h1
  linarith

lemma log_log_le_log {d : ℕ} (hd : D0 ≤ d) :
    Real.log (Real.log (d : ℝ)) ≤ Real.log (d : ℝ) := by
  have h1 := log_d_ge_one hd
  have h2 : Real.log (Real.log (d:ℝ)) ≤ Real.log (d:ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  linarith

lemma log_KK_bound {d : ℕ} (hd : D0 ≤ d) :
    Real.log (16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1) ≤ 3 + 3 * Real.log (d : ℝ) := by
  have h1 := log_d_ge_one hd
  have h2 : (0:ℝ) < Real.log (d:ℝ) := by linarith
  have h3 : (1:ℝ) ≤ (d:ℝ) := by
    have : 1 ≤ d := by simp only [D0] at hd; omega
    exact_mod_cast this
  have h4 : (1:ℝ) ≤ (d:ℝ) ^ 2 * Real.log (d:ℝ) := by nlinarith
  have h5 : 16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1 ≤ 17 * ((d:ℝ)^2 * Real.log (d:ℝ)) := by linarith
  have h6 : (0:ℝ) < (d:ℝ)^2 * Real.log (d:ℝ) := by linarith
  have h7 : Real.log 17 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 17)]
    have heq : Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [heq]
    have h2' : (2.71:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h3 : (2.71:ℝ)^3 < (Real.exp 1)^3 :=
      pow_lt_pow_left₀ h2' (by norm_num) (by norm_num : (3:ℕ) ≠ 0)
    have h4 : (17:ℝ) < (2.71:ℝ)^3 := by norm_num
    linarith
  calc Real.log (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1)
      ≤ Real.log (17 * ((d:ℝ)^2 * Real.log (d:ℝ))) := Real.log_le_log (by linarith) h5
    _ = Real.log 17 + (Real.log ((d:ℝ)^2) + Real.log (Real.log (d:ℝ))) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt h6), Real.log_mul (by positivity) (ne_of_gt h2)]
    _ ≤ 3 + (2 * Real.log (d:ℝ) + Real.log (d:ℝ)) := by
        have h9 : Real.log ((d:ℝ)^2) = 2 * Real.log (d:ℝ) := Real.log_pow _ _
        rw [h9]
        linarith [log_log_le_log hd]
    _ = 3 + 3 * Real.log (d:ℝ) := by ring

lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

lemma sqrt_KK_sq_exp_le_one {d : ℕ} (hd : D0 ≤ d) :
    Real.sqrt (3 * (16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1) ^ 4) * Real.exp (-((d : ℝ) / 2))
      ≤ 1 := by
  have h1 := log_d_ge_one hd
  have hK := log_KK_bound hd
  have hlogd := log_d_le_two_sqrt hd
  have hKpos : 0 < 16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1 := by
    have : 0 < Real.log (d:ℝ) := by linarith
    positivity
  have hbig : (2304:ℝ) ≤ (d:ℝ) := by
    have : 2304 ≤ d := by simp only [D0] at hd; omega
    exact_mod_cast this
  have hsqrt48 : (48:ℝ) ≤ Real.sqrt (d:ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    push_cast
    linarith
  have hsqrt : Real.sqrt (3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 4)
      = Real.sqrt 3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 2 := by
    rw [Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 4
        = ((16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hC : 0 < Real.sqrt 3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 2 := by positivity
  refine mul_exp_neg_le_one (x := (d:ℝ)/2) hC ?_
  have h4 : Real.log (Real.sqrt 3) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3))
    linarith [sqrt_three_lt_two]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h9 : Real.log (Real.sqrt 3) = Real.log 3 / 2 := Real.log_sqrt (by norm_num)
  have h10 : Real.log 3 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 3)]
    have heq : Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [heq]
    have h2' : (2.71:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h3 : (2.71:ℝ)^3 < (Real.exp 1)^3 :=
      pow_lt_pow_left₀ h2' (by norm_num) (by norm_num : (3:ℕ) ≠ 0)
    have h4 : (3:ℝ) < (2.71:ℝ)^3 := by norm_num
    linarith
  rw [h9]
  have hsqr : Real.sqrt (d:ℝ) ^ 2 = (d:ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [hK, hlogd, h10, h4, hsqrt48, hsqr, sq_nonneg (Real.sqrt (d:ℝ) - 24),
    sq_nonneg (Real.sqrt (d:ℝ) - 12)]

lemma sqrt_d_log_exp_le_one {d : ℕ} (hd : D0 ≤ d) :
    Real.sqrt (d:ℝ) * Real.sqrt (17 * Real.log (d:ℝ)) * Real.exp (-((d:ℝ)/2)) ≤ 1 := by
  have h1 := log_d_ge_one hd
  have hlogd := log_d_le_two_sqrt hd
  have hpos : (0:ℝ) < Real.log (d:ℝ) := by linarith
  have hsqrt48 : (48:ℝ) ≤ Real.sqrt (d:ℝ) := by
    have hbig : (2304:ℝ) ≤ (d:ℝ) := by
      have : 2304 ≤ d := by simp only [D0] at hd; omega
      exact_mod_cast this
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    push_cast
    linarith
  have hC : 0 < Real.sqrt (d:ℝ) * Real.sqrt (17 * Real.log (d:ℝ)) := by positivity
  refine mul_exp_neg_le_one (x := (d:ℝ)/2) hC ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
    Real.log_sqrt (by positivity)]
  have hsqr : Real.sqrt (d:ℝ) ^ 2 = (d:ℝ) := Real.sq_sqrt (by positivity)
  have h15 : Real.log (17 * Real.log (d:ℝ)) ≤ 17 * Real.log (d:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 17 * Real.log (d:ℝ))
    linarith
  nlinarith [hlogd, h15, hsqrt48, hsqr, sq_nonneg (Real.sqrt (d:ℝ) - 18)]

/-- **`E2`**: `∫_{bad} ‖H‖² ≤ 1`. -/
lemma setIntegral_norm_sq_badNet_le (hε : 0 ≤ eps d) (hd : D0 ≤ d)
    {S : Finset (Vec d)} (hSun : ∀ x ∈ S, ‖x‖ = 1) (hcard : (S.card : ℝ) ≤ (12:ℝ)^d) :
    (∫ ω in (badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)),
        ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 ∂(sampleLaw d (KK d))) ≤ 1 := by
  have hε' : (0:ℝ) ≤ eps d := hε
  have h4 := integral_norm_pow_four_le (d := d) (q := q) (R := R) (a := a) hε (by
    simp only [D0] at hd; omega)
  have hbad := badNet_measure_le (d := d) (q := q) (R := R) (a := a) hd hSun hcard
  have h2 := setIntegral_le_sqrt_mul_sqrt (μ := sampleLaw d (KK d))
    (s := badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d))
    (f := fun ω => ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2)
    (fun ω => by positivity)
    (((measurable_HH (d := d) (q := q) (R := R) (a := a) hε').pow_const 2).aestronglyMeasurable)
    (by simpa only [← pow_mul] using integrable_norm_pow_four (d := d) (q := q) (R := R) (a := a) hε')
    (measurableSet_badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d))
  refine h2.trans ?_
  have h3 : Real.sqrt (∫ ω : Fin (KK d) → MatV d × MatV d,
        (‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2) ^ 2 ∂(sampleLaw d (KK d)))
      ≤ Real.sqrt (3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 4) := by
    refine Real.sqrt_le_sqrt ?_
    simpa only [← pow_mul] using h4
  have h5 : Real.sqrt ((sampleLaw d (KK d)).real
      (badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)))
      ≤ Real.exp (-((d:ℝ)/2)) := by
    refine (Real.sqrt_le_sqrt hbad).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have h6 : Real.sqrt (3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 4)
      * Real.sqrt ((sampleLaw d (KK d)).real
        (badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)))
      ≤ Real.sqrt (3 * (16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) ^ 4) * Real.exp (-((d:ℝ)/2)) :=
    mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
  refine (mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)).trans ?_
  exact h6.trans (sqrt_KK_sq_exp_le_one hd)

lemma norm_oneV (d : ℕ) : ‖oneV d‖ = Real.sqrt (d:ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (oneV d)), LogDetV.norm_sq_eq_sum_sq]
  congr 1
  rw [Fintype.sum_prod_type]
  have h : ∀ i j : Fin d, (oneV d) (i, j) ^ 2 = (1 : Matrix (Fin d) (Fin d) ℝ) i j ^ 2 := by
    intro i j
    rw [← matOf_apply d (oneV d) i j, matOf_oneV]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))]
  simp [Matrix.one_apply]

/-- **`E1`**: `|∫_{bad} tr H| ≤ 1`. -/
lemma abs_setIntegral_trace_badNet_le (hε : 0 ≤ eps d) (hd : D0 ≤ d)
    {S : Finset (Vec d)} (hSun : ∀ x ∈ S, ‖x‖ = 1) (hcard : (S.card : ℝ) ≤ (12:ℝ)^d) :
    |∫ ω in (badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)),
        (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace ∂(sampleLaw d (KK d))|
      ≤ 1 := by
  have hε' : (0:ℝ) ≤ eps d := hε
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  set s := badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d) with hs
  have hsm : MeasurableSet s :=
    measurableSet_badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d)
  have htr : ∀ ω : Fin (KK d) → MatV d × MatV d,
      (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace
        = inner ℝ (oneV d) (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω) :=
    fun ω => Moment.trace_state_eq_inner (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω
  have hintT := DriftMain.integrable_trace_HH (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε'
  have hintN := Moment.integrable_stateK_norm (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε'
  -- step 1: the absolute value of the integral is at most the integral of the absolute value
  have h1 : |∫ ω in s, (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace
        ∂(sampleLaw d (KK d))|
      ≤ ∫ ω in s, |(matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace|
        ∂(sampleLaw d (KK d)) := by
    rw [← integral_indicator hsm, ← integral_indicator hsm]
    refine MeasureTheory.abs_integral_le_integral_abs.trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  -- step 2: pointwise `|tr H| ≤ √d ‖H‖`
  have h2 : ∫ ω in s, |(matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace|
        ∂(sampleLaw d (KK d))
      ≤ Real.sqrt (d:ℝ) * ∫ ω in s,
          ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ∂(sampleLaw d (KK d)) := by
    rw [← integral_indicator hsm, ← integral_indicator hsm, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
      ((hintN.indicator hsm).const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
    · exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) ω
    · by_cases hx : ω ∈ s
      · simp only [Set.indicator_of_mem hx, Pi.mul_apply]
        rw [htr ω]
        calc |inner ℝ (oneV d) (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)|
            ≤ ‖oneV d‖ * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ :=
              abs_real_inner_le_norm _ _
          _ = Real.sqrt (d:ℝ) * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ := by
              rw [norm_oneV]
      · simp [Set.indicator_of_notMem hx]
  -- step 3: Cauchy–Schwarz
  have h3 := setIntegral_le_sqrt_mul_sqrt (μ := sampleLaw d (KK d)) (s := s)
    (f := fun ω => ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖)
    (fun ω => norm_nonneg _)
    ((measurable_HH (d := d) (q := q) (R := R) (a := a) hε').aestronglyMeasurable)
    (by simpa only [HH] using
      Moment.integrable_stateK_norm_sq (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε')
    hsm
  have h4 : Real.sqrt (∫ ω : Fin (KK d) → MatV d × MatV d,
        ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 ∂(sampleLaw d (KK d)))
      ≤ Real.sqrt (17 * Real.log (d:ℝ)) := Real.sqrt_le_sqrt (integral_norm_sq_le (d := d) (q := q)
        (R := R) (a := a) hε' (by simp only [D0] at hd; omega))
  have hbad := badNet_measure_le (d := d) (q := q) (R := R) (a := a) hd hSun hcard
  have h5 : Real.sqrt ((sampleLaw d (KK d)).real s) ≤ Real.exp (-((d:ℝ)/2)) := by
    refine (Real.sqrt_le_sqrt hbad).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have h6 : Real.sqrt (d:ℝ) * (Real.sqrt (17 * Real.log (d:ℝ)) * Real.exp (-((d:ℝ)/2))) ≤ 1 := by
    rw [← mul_assoc]; exact sqrt_d_log_exp_le_one hd
  have h7 : ∫ ω in s, ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ∂(sampleLaw d (KK d))
      ≤ Real.sqrt (17 * Real.log (d:ℝ)) * Real.exp (-((d:ℝ)/2)) :=
    h3.trans (mul_le_mul h4 h5 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc |∫ ω in s, (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace
        ∂(sampleLaw d (KK d))|
      ≤ _ := h1
    _ ≤ Real.sqrt (d:ℝ) * ∫ ω in s,
          ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ∂(sampleLaw d (KK d)) := h2
    _ ≤ Real.sqrt (d:ℝ) * (Real.sqrt (17 * Real.log (d:ℝ)) * Real.exp (-((d:ℝ)/2))) :=
        mul_le_mul_of_nonneg_left h7 (Real.sqrt_nonneg _)
    _ ≤ 1 := h6

/-! ## The drift bound -/

lemma rr_nonneg' (d : ℕ) : 0 ≤ rr d := rr_nonneg d

lemma rr_le {d : ℕ} (hd : D0 ≤ d) : 2 * rr d ≤ 1 := by
  have hlog := log_d_le_two_sqrt hd
  have h1 := log_d_ge_one hd
  have h2 : (21233664:ℝ) ≤ (d:ℝ) := by
    have : 21233664 ≤ d := by simp only [D0] at hd; omega
    exact_mod_cast this
  have hsqrt : (4608:ℝ) ≤ Real.sqrt (d:ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    push_cast
    linarith
  have hsqr : Real.sqrt (d:ℝ) ^ 2 = (d:ℝ) := Real.sq_sqrt (by positivity)
  have hL : (0:ℝ) < Real.log (d:ℝ) := by linarith
  have hsqrtL : Real.sqrt (Real.log (d:ℝ)) ≤ Real.sqrt (2 * Real.sqrt (d:ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [rr, show 2 * (24 * Real.sqrt (Real.log (d:ℝ)) / Real.sqrt (d:ℝ))
      = 48 * Real.sqrt (Real.log (d:ℝ)) / Real.sqrt (d:ℝ) from by ring,
    div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (d:ℝ))]
  nlinarith [hsqrtL, hsqrt, hsqr, Real.sqrt_nonneg (Real.log (d:ℝ)),
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (d:ℝ))]

lemma eps_sq_half_mul_ge {d : ℕ} (hd : D0 ≤ d) :
    8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) ≤ (eps d)^2 / 2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1))) := by
  have hd1 : 1 ≤ d := by simp only [D0] at hd; omega
  have hd1' : 1 < d := by simp only [D0] at hd; omega
  have hdpos : (0:ℝ) < (d:ℝ) := by positivity
  have hK : 16 * (d:ℝ)^2 * Real.log (d:ℝ) ≤ (KK d : ℝ) := Nat.le_ceil _
  have hL : 0 < Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast hd1')
  have h2 : 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))
      = (1 / (d:ℝ)^4 / 2) * ((16 * (d:ℝ)^2 * Real.log (d:ℝ)) * ((d:ℝ) * ((d:ℝ) + 1))) := by
    field_simp
    ring
  rw [h2, eps, div_pow, one_pow]
  rw [show (((d:ℝ))^2)^2 = (d:ℝ)^4 from by ring]
  have h3 : (1:ℝ) ≤ (d:ℝ) * ((d:ℝ) + 1) := by
    have h3' : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
    nlinarith [h3', hdpos]
  have h4 : (0:ℝ) ≤ Real.log (d:ℝ) := hL.le
  have h5 : (0:ℝ) < 1 / (d:ℝ) ^ 4 / 2 := by positivity
  have h6 : 16 * (d:ℝ)^2 * Real.log (d:ℝ) * ((d:ℝ) * ((d:ℝ) + 1))
      ≤ (KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right hK (by linarith [h3])
  exact mul_le_mul_of_nonneg_left h6 h5.le

/-- `w d = d^{1/4}`. -/
noncomputable def w (d : ℕ) : ℝ := Real.sqrt (Real.sqrt (d:ℝ))

lemma log_le_four_w {d : ℕ} (hd : 1 ≤ d) : Real.log (d:ℝ) ≤ 4 * w d := by
  have hpos : (0:ℝ) < (d:ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hw : (0:ℝ) < w d := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hpos)
  have h1 : Real.log (w d) = Real.log (d:ℝ) / 4 := by
    rw [w, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hpos.le]
    ring
  have h2 : Real.log (w d) ≤ w d - 1 := Real.log_le_sub_one_of_pos hw
  linarith

lemma w_sq {d : ℕ} : w d ^ 2 = Real.sqrt (d:ℝ) :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

lemma one_le_w {d : ℕ} (hd : 1 ≤ d) : 1 ≤ w d := by
  have h1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  rw [w]
  exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr h1)

lemma sixteen_rr_logd_le {d : ℕ} (hd : D0 ≤ d) : 16 * rr d * Real.log (d:ℝ) ≤ 10^5 := by
  have hd1 : 1 ≤ d := by simp only [D0] at hd; omega
  have hdpos : (0:ℝ) < (d:ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hL := log_le_four_w hd1
  have hw1 := one_le_w hd1
  have hwpos : (0:ℝ) < w d := lt_of_lt_of_le zero_lt_one hw1
  have hsqw : w d ^ 2 = Real.sqrt (d:ℝ) := w_sq
  have hLnn : (0:ℝ) ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
  have hsqrtL : Real.sqrt (Real.log (d:ℝ)) ≤ 2 * Real.sqrt (w d) := by
    refine (Real.sqrt_le_sqrt (by linarith : Real.log (d:ℝ) ≤ 4 * w d)).trans (le_of_eq ?_)
    rw [show (4:ℝ) * w d = 2 ^ 2 * w d from by norm_num,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2 ^ 2) (w d), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hEq : 16 * rr d * Real.log (d:ℝ)
      = 384 * Real.log (d:ℝ) * Real.sqrt (Real.log (d:ℝ)) / Real.sqrt (d:ℝ) := by
    rw [rr]; field_simp; ring
  rw [hEq, div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (d:ℝ)),
    show (10:ℝ)^5 * Real.sqrt (d:ℝ) = 10^5 * w d ^ 2 from by rw [hsqw]]
  have hA : 384 * Real.log (d:ℝ) * Real.sqrt (Real.log (d:ℝ))
      ≤ 384 * (4 * w d) * (2 * Real.sqrt (w d)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num)) hsqrtL
      (Real.sqrt_nonneg _) (by positivity)
  refine hA.trans ?_
  have h7 : Real.sqrt (w d) * Real.sqrt (w d) = w d := by
    rw [← sq, Real.sq_sqrt hwpos.le]
  have h8 : (1:ℝ) ≤ Real.sqrt (w d) := Real.one_le_sqrt.mpr hw1
  have h9 : (3072:ℝ) * (Real.sqrt (w d) * w d) ≤ 10^5 * w d ^ 2 := by
    nlinarith [h7, h8, hwpos, hw1]
  have h10 : 384 * (4 * w d) * (2 * Real.sqrt (w d)) = 3072 * (Real.sqrt (w d) * w d) := by ring
  rw [h10]
  exact h9

lemma a0_le {d : ℕ} (hd : 2 ≤ d) : a0 d ≤ 4 := by
  have hd2R : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have h1 : (1/2:ℝ) ≤ 1 - 1/(d:ℝ) := by
    have : 1/(d:ℝ) ≤ 1/2 := by rw [div_le_div_iff₀ hdpos (by norm_num)]; linarith
    linarith
  have h3 : (1/4:ℝ) ≤ (1 - 1/(d:ℝ))^2 := by nlinarith
  exact (inv_le_comm₀ (show (0:ℝ) < (1 - 1/(d:ℝ))^2 by positivity) (by norm_num : (0:ℝ) < 4)).mpr (by
    rw [show ((4:ℝ))⁻¹ = 1/4 from by norm_num]
    exact h3)

lemma a0_add_rr_le {d : ℕ} (hd : D0 ≤ d) : a0 d + 2 * rr d ≤ 5 := by
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have h1 := a0_le hd2
  have h2 := rr_le hd
  linarith

lemma log_a0_le {d : ℕ} (hd : 3 ≤ d) : (d:ℝ) * Real.log (a0 d) ≤ 3 := by
  have hd3 : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hpos : (0:ℝ) < 1 - 1/(d:ℝ) := by
    have : 1/(d:ℝ) < 1 := by rw [div_lt_one hdpos]; linarith
    linarith
  have h1 : Real.log (a0 d) = -2 * Real.log (1 - 1/(d:ℝ)) := by
    rw [a0, ← inv_pow, Real.log_pow, Real.log_inv]
    ring
  have h2 : Real.log (1 - 1/(d:ℝ)) = -Real.log (1 + 1/((d:ℝ) - 1)) := by
    have h20 : 1 - 1/(d:ℝ) = (1 + 1/((d:ℝ)-1))⁻¹ := by
      rw [show (1 + 1/((d:ℝ)-1)) = (d:ℝ)/((d:ℝ)-1) from by
        rw [show (1:ℝ) + 1/((d:ℝ)-1) = ((d:ℝ)-1)/((d:ℝ)-1) + 1/((d:ℝ)-1) from by
          rw [div_self (by linarith : ((d:ℝ)-1) ≠ 0)], ← add_div]
        rw [show ((d:ℝ)-1) + 1 = (d:ℝ) from by ring], inv_div]
      field_simp
    rw [h20, Real.log_inv]
  have hpos2 : (0:ℝ) < 1 + 1/((d:ℝ)-1) := by
    have : (0:ℝ) < (d:ℝ) - 1 := by linarith
    positivity
  have h3 : Real.log (1 + 1/((d:ℝ)-1)) ≤ 1/((d:ℝ)-1) := by
    have := Real.log_le_sub_one_of_pos hpos2
    linarith
  have h4 : (d:ℝ) * (2 * (1/((d:ℝ)-1))) ≤ 3 := by
    have hpos' : (0:ℝ) < (d:ℝ) - 1 := by linarith
    rw [show (d:ℝ) * (2 * (1/((d:ℝ)-1))) = 2*(d:ℝ)/((d:ℝ)-1) from by field_simp,
      div_le_iff₀ hpos']
    linarith
  have h5 : (d:ℝ) * Real.log (a0 d) ≤ (d:ℝ) * (2 * (1/((d:ℝ)-1))) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hdpos)
    rw [h1, h2]
    linarith
  linarith [h4, h5]

lemma a0_sub_one_le {d : ℕ} (hd : 3 ≤ d) : a0 d - 1 ≤ 4 / (d:ℝ) := by
  have hd2R : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have h1 : a0 d = ((d:ℝ)/((d:ℝ)-1))^2 := by
    rw [a0]
    have h10 : 1 - 1/(d:ℝ) = ((d:ℝ)-1)/(d:ℝ) := by field_simp
    rw [h10, ← inv_pow]
    congr 1
    rw [inv_div]
  have hpos : (0:ℝ) < ((d:ℝ)-1)^2 := by nlinarith [hdpos]
  have h2 : a0 d * (d:ℝ) ≤ (d:ℝ) + 4 := by
    rw [h1, div_pow, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [hd2R]
  rw [sub_le_iff_le_add, h1, div_pow]
  have h3 : (4:ℝ)/(d:ℝ) + 1 = ((d:ℝ) + 4)/(d:ℝ) := by field_simp; ring
  rw [h3, div_le_div_iff₀ hpos hdpos]
  nlinarith [hd2R, hdpos, sq_nonneg ((d:ℝ) - 3)]

lemma a0_ge_one {d : ℕ} (hd : 2 ≤ d) : 1 ≤ a0 d := by
  have hdpos : (0:ℝ) < (d:ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have h1 : (0:ℝ) < 1 - 1/(d:ℝ) := by
    have : 1/(d:ℝ) < 1 := by rw [div_lt_one hdpos]; exact_mod_cast hd
    linarith
  have h2 : (1 - 1/(d:ℝ))^2 ≤ 1 := by
    have h2' : (1 - 1/(d:ℝ)) ≤ 1 := by
      have : (0:ℝ) ≤ 1/(d:ℝ) := by positivity
      linarith
    nlinarith [h2', h1.le]
  have h3 : (0:ℝ) < (1 - 1/(d:ℝ))^2 := by positivity
  rw [a0]
  exact (one_le_inv₀ h3).mpr h2

lemma inv_sq_ge (s : ℝ) (hs : 0 ≤ s) : 1 - 2 * s ≤ (1 + s)⁻¹ ^ 2 := by
  have h1 : (0:ℝ) < 1 + s := by linarith
  rw [inv_pow, inv_eq_one_div, le_div_iff₀ (by positivity : (0:ℝ) < (1 + s)^2)]
  nlinarith [hs, sq_nonneg s, mul_nonneg hs (sq_nonneg s)]

lemma c_drift_ge {d : ℕ} (hd : D0 ≤ d) :
    (1:ℝ)/2 - 2 * rr d - (a0 d - 1) ≤ (1/2) * (a0 d + 2 * rr d)⁻¹ ^ 2 := by
  have hd1 : 1 ≤ d := by simp only [D0] at hd; omega
  have hd2 : 2 ≤ d := by simp only [D0] at hd; omega
  have ha0 : 1 ≤ a0 d := a0_ge_one hd2
  have hrr : 0 ≤ rr d := rr_nonneg d
  have hs : (0:ℝ) ≤ (a0 d - 1) + 2 * rr d := by linarith
  have hkey := inv_sq_ge ((a0 d - 1) + 2 * rr d) hs
  have h2 : (1:ℝ)/2 - 2 * rr d - (a0 d - 1)
      = (1/2) * (1 - 2 * ((a0 d - 1) + 2 * rr d)) := by ring
  rw [h2]
  refine (mul_le_mul_of_nonneg_left hkey (by norm_num)).trans (le_of_eq ?_)
  rw [show (1 + ((a0 d - 1) + 2 * rr d)) = a0 d + 2 * rr d from by ring]

noncomputable def cDrift (d : ℕ) : ℝ := (1/2) * (a0 d + 2 * rr d)⁻¹ ^ 2

lemma logd_le_four_w {d : ℕ} (hd : 1 ≤ d) : Real.log (d:ℝ) ≤ 4 * w d := log_le_four_w hd

lemma logd_div_d_le {d : ℕ} (hd : 1 ≤ d) : Real.log (d:ℝ) / (d:ℝ) ≤ 4 := by
  have h1 := log_le_four_w hd
  have hdpos : (0:ℝ) < (d:ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hw1 := one_le_w hd
  have hwpos : (0:ℝ) < w d := lt_of_lt_of_le zero_lt_one hw1
  have hsq : w d ^ 2 = Real.sqrt (d:ℝ) := w_sq
  have h4 : w d ^ 4 = (d:ℝ) := by
    rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq, Real.sq_sqrt hdpos.le]
  rw [div_le_iff₀ hdpos]
  refine h1.trans ?_
  rw [← h4]
  have h5 : w d ≤ w d ^ 4 := by simpa using pow_le_pow_right₀ hw1 (by norm_num : 1 ≤ 4)
  linarith

theorem drift_bound (d : ℕ) (hd : D0 ≤ d) {q : ℕ} {R : ℝ} {a : Fin d → ZMod q}
    (hRpos : 0 < R)
    (hmin : ∀ k : Fin d → ℤ, 0 < intQ k → intQ k ≤ R ^ 2 → ¬ LatticeGood2.kerCond a k)
    (hwt : (∑ k ∈ (intPoints (d := d) (2 * R)).filter (fun x => LatticeGood2.kerCond a x),
        wt (d := d) (KK d) (a0 d) R k) ≤ (d : ℝ) ^ 4 / 2)
    {S : Finset (Vec d)} (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcard : (S.card : ℝ) ≤ (12:ℝ) ^ d) :
    (∫ ω in (badNet Rb (BoxL d q R a) (a0 d) (eps d) (KK d) S (rr d))ᶜ,
        ((d:ℝ) * Real.log (a0 d)
          + (matOf d (HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω)).trace / (a0 d)
          - cDrift d * ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2) ∂(sampleLaw d (KK d)))
      ≤ Cg - 4 * Real.log (d:ℝ) := by
  have hd3 : 3 ≤ d := by simp only [D0] at hd; omega
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hε : (0:ℝ) ≤ eps d := (eps_pos d (by omega)).le
  have ha0 : (0:ℝ) < a0 d := lt_of_lt_of_le zero_lt_one (a0_ge_one hd2)
  have ha1 : (1:ℝ) ≤ a0 d := a0_ge_one hd2
  have hE1 := abs_setIntegral_trace_badNet_le (d := d) (q := q) (R := R) (a := a) hε hd hSun hcard
  have hE2 := setIntegral_norm_sq_badNet_le (d := d) (q := q) (R := R) (a := a) hε hd hSun hcard
  have hT := DriftGood.setIntegral_T_le (R := Rb) (BoxL := BoxL d q R a) (a₀ := a0 d)
    (ε := eps d) (r := rr d) (E1 := 1) (E2 := 1) (K := KK d) (S := S)
    ha0 ha1 hε
    (DriftMain.integrable_trace_HH (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε)
    (Moment.integrable_stateK_norm_sq (d := d) Rb (BoxL d q R a) (a0 d) (eps d) (KK d) hε)
    hE1 hE2
  have hcontact := contact_bound_applied (d := d) (q := q) (R := R) (a := a) hd hRpos hmin hwt
  have hnegL : ∀ i : Fin (candIdx d q R a).card, ∃ j, BoxL d q R a j = -BoxL d q R a i :=
    fun i => boxL_negL (d := d) (q := q) (R := R) (a := a) hRpos i
  have hne : ∀ i : Fin (candIdx d q R a).card, BoxL d q R a i ≠ 0 :=
    fun i => boxL_ne_zero (d := d) (q := q) (R := R) (a := a) hRpos i
  have hnorm := DriftBound.integral_norm_sq_state_ge (R := Rb) (BoxL := BoxL d q R a)
    (a₀ := a0 d) (ε := eps d) (K := KK d) hne hnegL (by rw [Rb]; norm_num) hε
  -- rewrite `HH = stateK` in `hnorm`
  have hnorm' : (eps d ^ 2 / 2) * (((KK d : ℝ) * ((d * (d + 1) : ℕ) : ℝ))
        - ∑ k : Fin (KK d), ∫ ω : Fin (KK d) → MatV d × MatV d,
            ((violSet Rb (BoxL d q R a) (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω k)).card : ℝ)
              ∂(sampleLaw d (KK d)))
      ≤ ∫ ω : Fin (KK d) → MatV d × MatV d,
          ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 ∂(sampleLaw d (KK d)) :=
    hnorm
  have hcd := c_drift_ge (d := d) hd
  have heps := eps_sq_half_mul_ge (d := d) hd
  have hrl := sixteen_rr_logd_le (d := d) hd
  have hlogd := logd_div_d_le hd1
  have ha0sub := a0_sub_one_le hd3
  have hlog := log_a0_le hd3
  have hrr := rr_nonneg d
  have hc_le : cDrift d ≤ 1/2 := by
    rw [cDrift]
    have h1 : (a0 d + 2 * rr d)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith [ha1, hrr] : (0:ℝ) < a0 d + 2 * rr d)).mpr (by linarith [ha1, hrr])
    have h2 : (0:ℝ) ≤ (a0 d + 2 * rr d)⁻¹ := inv_nonneg.mpr (by linarith [ha1, hrr])
    nlinarith [h1, h2, sq_nonneg ((a0 d + 2 * rr d)⁻¹)]
  have hcM : cDrift d * ((eps d)^2/2 * (4 * (d:ℝ)^4)) ≤ 1 := by
    have h2 : (eps d)^2/2 * (4 * (d:ℝ)^4) = 2 := by
      rw [eps_sq_eq]; field_simp; ring
    rw [h2]
    nlinarith [hc_le]
  have hnat : ((d * (d + 1) : ℕ) : ℝ) = (d:ℝ) * ((d:ℝ) + 1) := by push_cast; ring
  have hnormN : (eps d ^ 2 / 2) * (((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1))) - 4 * (d:ℝ)^4)
      ≤ ∫ ω : Fin (KK d) → MatV d × MatV d,
          ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 ∂(sampleLaw d (KK d)) := by
    have hh := hnorm'
    rw [hnat] at hh
    have hsub : ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1)) - 4 * (d:ℝ)^4)
        ≤ ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1))
            - ∑ k : Fin (KK d), ∫ ω : Fin (KK d) → MatV d × MatV d,
                ((violSet Rb (BoxL d q R a) (proc (projL Rb (BoxL d q R a)) (a0 d) (eps d) (KK d) ω k)).card : ℝ)
                  ∂(sampleLaw d (KK d))) :=
      sub_le_sub_left hcontact _
    exact le_trans (mul_le_mul_of_nonneg_left hsub (by positivity)) hh
  refine hT.trans ?_
  have hExp : (d:ℝ) * Real.log (a0 d) + 1 / (a0 d) + ((1/2:ℝ) * (a0 d + 2 * rr d)⁻¹ ^ 2) * 1
        - (1/2) * (a0 d + 2 * rr d)⁻¹ ^ 2
            * (∫ ω : Fin (KK d) → MatV d × MatV d,
                ‖HH Rb (BoxL d q R a) (a0 d) (eps d) (KK d) ω‖ ^ 2 ∂(sampleLaw d (KK d)))
      ≤ (d:ℝ) * Real.log (a0 d) + 1 / (a0 d) + cDrift d
        - cDrift d * ((eps d)^2/2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1)) - 4 * (d:ℝ)^4)) := by
    rw [cDrift]
    have h1 : (0:ℝ) ≤ (1/2) * (a0 d + 2 * rr d)⁻¹ ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hnormN h1
    linarith [h2]
  refine hExp.trans ?_
  rw [show (d:ℝ) * Real.log (a0 d) + 1 / (a0 d) + cDrift d
        - cDrift d * ((eps d)^2/2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1)) - 4 * (d:ℝ)^4))
      = ((d:ℝ) * Real.log (a0 d)) + 1 / (a0 d) + cDrift d
        - cDrift d * ((eps d)^2/2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1))))
        + cDrift d * ((eps d)^2/2 * (4 * (d:ℝ)^4)) from by ring]
  have hkey : 3 + 1 + 1/2 - 4 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))
        + 2 * (16 * rr d * Real.log (d:ℝ)) + 64 * (Real.log (d:ℝ) / (d:ℝ))
        + 1 + 4 * Real.log (d:ℝ) ≤ Cg := by
    have h4 : 2 * (16 * rr d * Real.log (d:ℝ)) ≤ 2 * 10^5 := by linarith [hrl]
    have h5 : 64 * (Real.log (d:ℝ) / (d:ℝ)) ≤ 256 := by linarith [hlogd]
    have h7 : 4 * Real.log (d:ℝ) - 4 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))
        = -(4 * (Real.log (d:ℝ)/(d:ℝ))) := by
      field_simp
      ring
    rw [show Cg = (10:ℝ)^6 from rfl]
    linarith [h4, h5, h7]
  have hmain : (d:ℝ) * Real.log (a0 d) + 1 / (a0 d) + cDrift d
        - cDrift d * ((eps d)^2/2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1))))
        + cDrift d * ((eps d)^2/2 * (4 * (d:ℝ)^4))
      ≤ Cg - 4 * Real.log (d:ℝ) := by
    have h1 : (d:ℝ) * Real.log (a0 d) ≤ 3 := hlog
    have h2 : 1 / (a0 d) ≤ 1 := by
      rw [div_le_one ha0]; exact ha1
    have h3 : cDrift d ≤ 1/2 := hc_le
    have h4 := hcM
    have hYnn : (0:ℝ) ≤ (eps d)^2/2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1))) := by positivity
    have hXnn : (0:ℝ) ≤ 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) := by
      have hL : (0:ℝ) ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
      have h1d : (0:ℝ) ≤ 1 + 1/(d:ℝ) := by positivity
      positivity
    have hc0 : (0:ℝ) ≤ cDrift d := by
      rw [cDrift]; positivity
    have hgain : 4 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))
        - 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d + (a0 d - 1))
        ≤ cDrift d * ((eps d)^2/2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1)))) := by
      have h5 : (1/2 - 2 * rr d - (a0 d - 1)) * (8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)))
          ≤ cDrift d * (8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))) :=
        mul_le_mul_of_nonneg_right hcd hXnn
      have h6 := mul_le_mul_of_nonneg_left heps hc0
      have hEq : 4 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))
          - 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d + (a0 d - 1))
          = (1/2 - 2 * rr d - (a0 d - 1)) * (8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))) := by ring
      rw [hEq]
      exact h5.trans h6
    have h6 : 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d + (a0 d - 1))
        ≤ 2 * (16 * rr d * Real.log (d:ℝ)) + 64 * (Real.log (d:ℝ) / (d:ℝ)) := by
      have hL : (0:ℝ) ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
      have h7 : 1 + 1/(d:ℝ) ≤ 2 := by
        have h8 : 1/(d:ℝ) ≤ 1 := by rw [div_le_one (by positivity : (0:ℝ) < (d:ℝ))]; exact_mod_cast hd1
        linarith
      have hsplit : 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d + (a0 d - 1))
          = 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d)
            + 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (a0 d - 1) := by ring
      rw [hsplit]
      have h9 : 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d)
          ≤ 32 * rr d * Real.log (d:ℝ) := by
        have hA : (0:ℝ) ≤ 16 * rr d * Real.log (d:ℝ) := by positivity
        have hB := mul_le_mul_of_nonneg_left h7 hA
        nlinarith [hB]
      have h10 : 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (a0 d - 1)
          ≤ 64 * (Real.log (d:ℝ) / (d:ℝ)) := by
        have hd' : (0:ℝ) < (d:ℝ) := by positivity
        have hA : (0:ℝ) ≤ 8 * Real.log (d:ℝ) := by linarith
        have hB : (0:ℝ) ≤ 1 + 1/(d:ℝ) := by positivity
        have hC : (0:ℝ) ≤ a0 d - 1 := by
          linarith [a0_ge_one (show 2 ≤ d by simp only [D0] at hd; omega)]
        have h11 : 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (a0 d - 1)
            ≤ 8 * Real.log (d:ℝ) * 2 * (4/(d:ℝ)) := by
          calc 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (a0 d - 1)
              = (8 * Real.log (d:ℝ)) * ((1 + 1/(d:ℝ)) * (a0 d - 1)) := by ring
            _ ≤ (8 * Real.log (d:ℝ)) * (2 * (4/(d:ℝ))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h7 ha0sub hC (by norm_num)) hA
            _ = 8 * Real.log (d:ℝ) * 2 * (4/(d:ℝ)) := by ring
        have h12 : (8:ℝ) * Real.log (d:ℝ) * 2 * (4/(d:ℝ))
            = 64 * (Real.log (d:ℝ) / (d:ℝ)) := by
          field_simp
          ring
        linarith [h11, h12]
      linarith [h9, h10]
    have hA : (d:ℝ) * Real.log (a0 d) + 1 / (a0 d) + cDrift d
          - cDrift d * ((eps d)^2/2 * ((KK d : ℝ) * ((d:ℝ) * ((d:ℝ) + 1))))
          + cDrift d * ((eps d)^2/2 * (4 * (d:ℝ)^4))
        ≤ 3 + 1 + 1/2
          - (4 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))
              - 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d + (a0 d - 1))) + 1 := by
      linarith [h1, h2, h3, h4, hgain]
    have hB : 3 + 1 + 1/2
          - (4 * Real.log (d:ℝ) * (1 + 1/(d:ℝ))
              - 8 * Real.log (d:ℝ) * (1 + 1/(d:ℝ)) * (2 * rr d + (a0 d - 1))) + 1
        ≤ Cg - 4 * Real.log (d:ℝ) := by
      linarith [h6, hkey]
    linarith [hA, hB]
  linarith [hmain]


end

end Submission.Main
