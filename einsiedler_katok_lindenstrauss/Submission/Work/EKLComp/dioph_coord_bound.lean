import Mathlib
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLComp

open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

/-! ## Helper lemmas about `distToNearestInt`

The proof below uses the unqualified name; the theorem statement keeps the fully
qualified name from the problem statement. -/

lemma distToNearestInt_abs_mul_le (a u : ℝ) (z : ℤ) :
    distToNearestInt (|a| * u) ≤ |a * u + (z : ℝ)| := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    have h1 := round_le (a * u) (-z)
    rw [Int.cast_neg, sub_neg_eq_add] at h1
    simpa [distToNearestInt] using h1
  · rw [abs_of_neg (not_le.mp ha)]
    have h1 := round_le ((-a) * u) z
    have hru : (-a) * u = -(a * u) := by ring
    rw [hru] at h1
    have h2 : |-(a * u) - (z : ℝ)| = |a * u + (z : ℝ)| := by
      rw [show -(a * u) - (z : ℝ) = -(a * u + (z : ℝ)) by ring, abs_neg]
    rw [h2] at h1
    simpa [distToNearestInt] using h1

lemma int_eq_zero_of_exp_mul_abs_lt_one {c : ℝ} (hc : 0 ≤ c) {B : ℤ}
    (h : |Real.exp c * (B : ℝ)| < 1) : B = 0 := by
  have hpos : 0 < Real.exp c := Real.exp_pos c
  have hle : |(B : ℝ)| ≤ |Real.exp c * (B : ℝ)| := by
    rw [abs_mul, abs_of_pos hpos]
    simpa using mul_le_mul_of_nonneg_right (Real.one_le_exp hc) (abs_nonneg (B:ℝ))
  have hlt : |(B : ℝ)| < 1 := lt_of_le_of_lt hle h
  rw [← Int.cast_abs] at hlt
  have hltI : (|B| : ℤ) < 1 := by exact_mod_cast hlt
  exact Int.abs_lt_one_iff.mp hltI

lemma abs_lt_of_abs_exp_mul_lt {c m x : ℝ} (h : |Real.exp c * x| < m) :
    |x| < m * Real.exp (-c) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos c)] at h
  have h2 := mul_lt_mul_of_pos_right h (Real.exp_pos (-c))
  rw [mul_comm (Real.exp c) |x|, mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one] at h2
  exact h2

lemma exp_mul_lt_of_mul_exp_neg_lt {c m x : ℝ} (h : x * Real.exp (-c) < m) :
    x < m * Real.exp c := by
  have h2 := mul_lt_mul_of_pos_right h (Real.exp_pos c)
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h2
  exact h2

lemma dioph_numeric {ρ r s N d1 d2 : ℝ} (hρ : 0 < ρ)
    (hN0 : 0 ≤ N) (_hd1nn : 0 ≤ d1) (hd2nn : 0 ≤ d2)
    (hN : N < ρ * Real.exp (r + s))
    (hd1 : d1 ≤ ρ * Real.exp (-r)) (hd2 : d2 ≤ ρ * Real.exp (-s)) :
    N * d1 * d2 < ρ ^ 3 := by
  have s1 : N * d1 ≤ N * (ρ * Real.exp (-r)) := mul_le_mul_of_nonneg_left hd1 hN0
  have hmid : 0 ≤ N * (ρ * Real.exp (-r)) := by positivity
  have s2 : (N * d1) * d2 ≤ (N * (ρ * Real.exp (-r))) * d2 :=
    mul_le_mul_of_nonneg_right s1 hd2nn
  have s3 : (N * (ρ * Real.exp (-r))) * d2
      ≤ (N * (ρ * Real.exp (-r))) * (ρ * Real.exp (-s)) :=
    mul_le_mul_of_nonneg_left hd2 hmid
  have key : (N * (ρ * Real.exp (-r))) * (ρ * Real.exp (-s)) < ρ ^ 3 := by
    have hA1 : (N * (ρ * Real.exp (-r))) * (ρ * Real.exp (-s))
        = N * (ρ ^ 2 * Real.exp (-(r + s))) := by
      have ha : Real.exp (-r) * Real.exp (-s) = Real.exp (-(r + s)) := by
        rw [← Real.exp_add]; congr 1; ring
      linear_combination (N * ρ ^ 2) * ha
    rw [hA1]
    have hpos : 0 < ρ ^ 2 * Real.exp (-(r + s)) := by positivity
    have h1 := mul_lt_mul_of_pos_right hN hpos
    have h2 : (ρ * Real.exp (r + s)) * (ρ ^ 2 * Real.exp (-(r + s))) = ρ ^ 3 := by
      have hb : Real.exp (r + s) * Real.exp (-(r + s)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linear_combination (ρ ^ 3) * hb
    rw [h2] at h1
    exact h1
  calc N * d1 * d2 = (N * d1) * d2 := by ring
    _ ≤ (N * (ρ * Real.exp (-r))) * (ρ * Real.exp (-s)) := le_trans s2 s3
    _ < ρ ^ 3 := key

theorem dioph_coord_bound (u v ρ δ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hρδ : ρ ^ 3 ≤ δ)
    (hδ : ∀ n : ℕ, 1 ≤ n →
      δ ≤ (n : ℝ) * LeanEval.Dynamics.EinsiedlerKatokLindenstrauss.distToNearestInt (n * u)
        * LeanEval.Dynamics.EinsiedlerKatokLindenstrauss.distToNearestInt (n * v))
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (k : Fin 3 → ℤ) (hk : k ≠ 0)
    (h0 : |Real.exp (-r - s) * (k 0 : ℝ)| < ρ)
    (h1 : |Real.exp r * (u * (k 0 : ℝ) + (k 1 : ℝ))| < ρ)
    (h2 : |Real.exp s * (v * (k 0 : ℝ) + (k 2 : ℝ))| < ρ) : False := by
  have hAne : k 0 ≠ 0 := by
    intro hA0
    have hB0 : k 1 = 0 := by
      have h1' : |Real.exp r * (k 1 : ℝ)| < (1 : ℝ) := by
        have h := h1
        rw [hA0] at h
        simp only [Int.cast_zero, mul_zero, zero_add] at h
        linarith [h, hρ1]
      exact int_eq_zero_of_exp_mul_abs_lt_one hr h1'
    have hC0 : k 2 = 0 := by
      have h2' : |Real.exp s * (k 2 : ℝ)| < (1 : ℝ) := by
        have h := h2
        rw [hA0] at h
        simp only [Int.cast_zero, mul_zero, zero_add] at h
        linarith [h, hρ1]
      exact int_eq_zero_of_exp_mul_abs_lt_one hs h2'
    have hk0 : k = 0 := by
      funext i
      fin_cases i
      · exact hA0
      · exact hB0
      · exact hC0
    exact hk hk0
  have hnpos : 0 < (k 0).natAbs := Int.natAbs_pos.mpr hAne
  have hn1 : 1 ≤ (k 0).natAbs := by omega
  have hnabs : (((k 0).natAbs : ℕ) : ℝ) = |(k 0 : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp
  have h0n : Real.exp (-r - s) * (((k 0).natAbs : ℕ) : ℝ) < ρ := by
    have h := h0
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h
    rw [← hnabs] at h
    exact h
  have hnlt : (((k 0).natAbs : ℕ) : ℝ) < ρ * Real.exp (r + s) := by
    apply exp_mul_lt_of_mul_exp_neg_lt (c := r + s)
    have hcomm : Real.exp (-r - s) * (((k 0).natAbs : ℕ) : ℝ)
        = (((k 0).natAbs : ℕ) : ℝ) * Real.exp (-(r + s)) := by
      have harg : -r - s = -(r + s) := by ring
      rw [harg, mul_comm]
    rw [hcomm] at h0n
    exact h0n
  have hX1 : |(k 0 : ℝ) * u + (k 1 : ℝ)| < ρ * Real.exp (-r) := by
    have h1' : |Real.exp r * ((k 0 : ℝ) * u + (k 1 : ℝ))| < ρ := by
      have h := h1
      have hinner : u * (k 0 : ℝ) + (k 1 : ℝ) = (k 0 : ℝ) * u + (k 1 : ℝ) := by ring
      rwa [hinner] at h
    exact abs_lt_of_abs_exp_mul_lt h1'
  have hX2 : |(k 0 : ℝ) * v + (k 2 : ℝ)| < ρ * Real.exp (-s) := by
    have h2' : |Real.exp s * ((k 0 : ℝ) * v + (k 2 : ℝ))| < ρ := by
      have h := h2
      have hinner : v * (k 0 : ℝ) + (k 2 : ℝ) = (k 0 : ℝ) * v + (k 2 : ℝ) := by ring
      rwa [hinner] at h
    exact abs_lt_of_abs_exp_mul_lt h2'
  have hd1 : distToNearestInt ((((k 0).natAbs : ℕ) : ℝ) * u) ≤ ρ * Real.exp (-r) := by
    have hle := distToNearestInt_abs_mul_le (k 0 : ℝ) u (k 1)
    rw [← hnabs] at hle
    exact le_trans hle (le_of_lt hX1)
  have hd2 : distToNearestInt ((((k 0).natAbs : ℕ) : ℝ) * v) ≤ ρ * Real.exp (-s) := by
    have hle := distToNearestInt_abs_mul_le (k 0 : ℝ) v (k 2)
    rw [← hnabs] at hle
    exact le_trans hle (le_of_lt hX2)
  have hN0 : (0 : ℝ) ≤ (((k 0).natAbs : ℕ) : ℝ) := Nat.cast_nonneg _
  have hd1nn : (0 : ℝ) ≤ distToNearestInt ((((k 0).natAbs : ℕ) : ℝ) * u) :=
    abs_nonneg _
  have hd2nn : (0 : ℝ) ≤ distToNearestInt ((((k 0).natAbs : ℕ) : ℝ) * v) :=
    abs_nonneg _
  have hnum : (((k 0).natAbs : ℕ) : ℝ)
        * distToNearestInt ((((k 0).natAbs : ℕ) : ℝ) * u)
        * distToNearestInt ((((k 0).natAbs : ℕ) : ℝ) * v) < ρ ^ 3 :=
    dioph_numeric hρ hN0 hd1nn hd2nn hnlt hd1 hd2
  have hδn := hδ ((k 0).natAbs) hn1
  linarith [hnum, hρδ, hδn]

end Work.EKLComp
