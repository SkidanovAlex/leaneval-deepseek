/-
# `FIArea2/R6/KArithSelf` — the `K`-arithmetic of the round-6 pair bracket

With `K1 = ⌈(2N)^{1/4}⌉`, `K2 = ⌈(4πθN)^{1/4}⌉`, `K = max K1 K2` and `u = θ√N ≥ N^{3/8}`:
`1 ≤ K1, K2`, `K1, K2 ≤ K`, `K√K ≤ 8u`, `K² ≤ 16u²`, `log K + 2 ≤ 4(log N + 2)`.
(Independent of the `KArith6Self` stub, so that the path to `R6WProp` is `sorry`-free.)
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FIArea4.S15box

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

noncomputable section

/-- The four `rpow` comparisons behind `KArithSelf`, for `u ≥ N^{3/8}`, `u ≥ 1`, `N ≥ 1`. -/
private theorem u_aux {u N : ℝ} (hu : N ^ ((3 : ℝ) / 8) ≤ u) (hu1 : 1 ≤ u) (hN1 : 1 ≤ N) :
    N ^ ((1 : ℝ) / 4) ≤ u ^ ((2 : ℝ) / 3)
      ∧ (u * Real.sqrt N) ^ ((3 : ℝ) / 8) ≤ u
      ∧ Real.sqrt N ≤ u ^ (2 : ℝ)
      ∧ (u * Real.sqrt N) ^ ((1 : ℝ) / 2) ≤ u ^ (2 : ℝ) := by
  have hN0 : (0 : ℝ) ≤ N := by linarith only [hN1]
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu1
  have hu1' : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have h1 : N ^ ((1 : ℝ) / 4) ≤ u ^ ((2 : ℝ) / 3) := by
    have h : N ^ ((1 : ℝ) / 4) = (N ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_mul hN0]; norm_num
    rw [h]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hu (by norm_num)
  have h3 : N ^ ((3 : ℝ) / 10) ≤ u := by
    have h4 : ((3 : ℝ) / 10) ≤ ((3 : ℝ) / 8) := by norm_num
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1 h4) hu
  have h2 : (u * Real.sqrt N) ^ ((3 : ℝ) / 8) ≤ u := by
    have h : (u * Real.sqrt N) ^ ((3 : ℝ) / 8)
        = u ^ ((3 : ℝ) / 8) * N ^ ((3 : ℝ) / 16) := by
      rw [Real.mul_rpow hu0 (Real.sqrt_nonneg N), Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]
      norm_num
    have h5 : N ^ ((3 : ℝ) / 16) ≤ u ^ ((5 : ℝ) / 8) := by
      have h6 : N ^ ((3 : ℝ) / 16) = (N ^ ((3 : ℝ) / 10)) ^ ((5 : ℝ) / 8) := by
        rw [← Real.rpow_mul hN0]; norm_num
      rw [h6]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) h3 (by norm_num)
    rw [h]
    calc u ^ ((3 : ℝ) / 8) * N ^ ((3 : ℝ) / 16)
        ≤ u ^ ((3 : ℝ) / 8) * u ^ ((5 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hu0 _)
      _ = u ^ ((3 : ℝ) / 8 + (5 : ℝ) / 8) := (Real.rpow_add hu1' _ _).symm
      _ = u := by rw [show ((3 : ℝ) / 8 + (5 : ℝ) / 8) = 1 by norm_num, Real.rpow_one]
  have hsqN : Real.sqrt N ≤ u ^ (2 : ℝ) := by
    have h : Real.sqrt N = (N ^ ((3 : ℝ) / 8)) ^ ((4 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]; norm_num
    rw [h]
    exact le_trans (Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hu (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num))
  have h4 : (u * Real.sqrt N) ^ ((1 : ℝ) / 2) ≤ u ^ (2 : ℝ) := by
    have h : (u * Real.sqrt N) ^ ((1 : ℝ) / 2) = u ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4) := by
      rw [Real.mul_rpow hu0 (Real.sqrt_nonneg N), Real.sqrt_eq_rpow, ← Real.rpow_mul hN0]
      norm_num
    have h5 : N ^ ((1 : ℝ) / 4) ≤ u ^ ((3 : ℝ) / 2) := by
      have h6 : N ^ ((1 : ℝ) / 6) ≤ u := by
        have h7 : ((1 : ℝ) / 6) ≤ ((3 : ℝ) / 8) := by norm_num
        exact le_trans (Real.rpow_le_rpow_of_exponent_le hN1 h7) hu
      have h8 : N ^ ((1 : ℝ) / 4) = (N ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 2) := by
        rw [← Real.rpow_mul hN0]; norm_num
      rw [h8]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) h6 (by norm_num)
    rw [h]
    calc u ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4) ≤ u ^ ((1 : ℝ) / 2) * u ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hu0 _)
      _ = u ^ (2 : ℝ) := by
          rw [← Real.rpow_add hu1', show ((1 : ℝ) / 2 + (3 : ℝ) / 2) = 2 by norm_num]
  exact ⟨h1, h2, hsqN, h4⟩

/-- **The `K`-arithmetic of the round-6 pair bracket**: with `K1 = ⌈(2N)^{1/4}⌉`,
`K2 = ⌈(4πθN)^{1/4}⌉`, `K = max K1 K2` and `u = θ√N ≥ N^{3/8}`, one has `K√K ≤ 8u`,
`K² ≤ 16u²` and `log K + 2 ≤ 4(log N + 2)`. -/
theorem KArithSelf (Pa : Work.FITop.Params) (K1 K2 K : ℕ)
    (hK1 : K1 = ⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊)
    (hK2 : K2 = ⌈(4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊)
    (hK : K = max K1 K2)
    (hu : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N) :
    1 ≤ K1 ∧ 1 ≤ K2 ∧ K1 ≤ K ∧ K2 ≤ K ∧
      (K : ℝ) * Real.sqrt (K : ℝ) ≤ 8 * (Pa.θ * Real.sqrt Pa.N) ∧
      (K : ℝ) * (K : ℝ) ≤ 16 * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) ∧
      Real.log (K : ℝ) + 2 ≤ 4 * (Real.log Pa.N + 2) := by
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hN0 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith only [hN1]
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith only [hN1]
  have hθ0 : (0 : ℝ) < Pa.θ := Pa.hθ0
  have hθ0' : (0 : ℝ) ≤ Pa.θ := le_of_lt hθ0
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hsqN : Real.sqrt Pa.N * Real.sqrt Pa.N = Pa.N := Real.mul_self_sqrt hN0
  have hu1 : (1 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 8) := (Real.one_rpow _).symm
      _ ≤ (Pa.N : ℝ) ^ ((3 : ℝ) / 8) := Real.rpow_le_rpow (by norm_num) hN1 (by norm_num)
      _ ≤ Pa.θ * Real.sqrt Pa.N := hu
  have hu0 : (0 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N := le_trans zero_le_one hu1
  obtain ⟨h14, hK2a, h12, hK2b⟩ := u_aux hu hu1 hN1
  -- `u·√N = θN`, and the two elementary bounds on it
  have hθNu : (Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N = Pa.θ * (Pa.N : ℝ) := by
    rw [mul_assoc, hsqN]
  have hθN1 : (1 : ℝ) ≤ Pa.θ * (Pa.N : ℝ) := by
    have h1 : (1 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N := hu1
    have h2 : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N :=
          mul_le_mul h1 h2 (by norm_num) hu0
      _ = Pa.θ * (Pa.N : ℝ) := hθNu
  have hθNle : Pa.θ * (Pa.N : ℝ) ≤ (Pa.N : ℝ) := by nlinarith only [hθ1, hN0]
  have huN1 : (1 : ℝ) ≤ (Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N := by rw [hθNu]; exact hθN1
  have hx1 : (1 : ℝ) ≤ (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) := by
    have h2N1 : (1 : ℝ) ≤ 2 * (Pa.N : ℝ) := by linarith only [hN1]
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
      _ ≤ (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num) h2N1 (by norm_num)
  have hx2 : (1 : ℝ) ≤ (4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) := by
    have h1 : (1 : ℝ) ≤ 4 * Real.pi * Pa.θ * (Pa.N : ℝ) := by nlinarith only [hθN1, Real.pi_gt_three]
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
      _ ≤ (4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  -- the two ceiling bounds
  have hK1le : (K1 : ℝ) ≤ 4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := by
    have h2N0 : (0 : ℝ) ≤ 2 * (Pa.N : ℝ) := by linarith only [hN1]
    have hlt : (K1 : ℝ) ≤ (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) + 1 := by
      rw [hK1]; exact (Nat.ceil_lt_add_one (Real.rpow_nonneg h2N0 _)).le
    have h : (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)
        = (2 : ℝ) ^ ((1 : ℝ) / 4) * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hN0
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ (2 : ℝ) ^ ((1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hY1 : (1 : ℝ) ≤ (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hN1 (by norm_num)
    rw [h] at hlt
    nlinarith only [hlt, h2, hY1, Real.rpow_nonneg hN0 ((1 : ℝ) / 4)]
  have hK2le : (K2 : ℝ) ≤ 4 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4) := by
    have h2N0' : (0 : ℝ) ≤ 4 * Real.pi * Pa.θ * (Pa.N : ℝ) := by positivity
    have hlt : (K2 : ℝ) ≤ (4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) + 1 := by
      rw [hK2]; exact (Nat.ceil_lt_add_one (Real.rpow_nonneg h2N0' _)).le
    have h1 : (4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)
        = (4 * Real.pi) ^ ((1 : ℝ) / 4)
          * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4) := by
      have hθN : (Pa.θ * (Pa.N : ℝ)) = (Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N := hθNu.symm
      rw [show (4 * Real.pi * Pa.θ * (Pa.N : ℝ)) = (4 * Real.pi) * (Pa.θ * (Pa.N : ℝ)) by ring,
        Real.mul_rpow (by positivity) (by nlinarith only [hθ0', hN0]), hθN]
    have h2 : (4 * Real.pi) ^ ((1 : ℝ) / 4) ≤ 2 := by
      have h3 : (4 * Real.pi : ℝ) ≤ 16 := by nlinarith only [Real.pi_lt_four]
      calc (4 * Real.pi) ^ ((1 : ℝ) / 4) ≤ (16 : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) h3 (by norm_num)
        _ = 2 := by
            rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
              ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
    have hY1 : (1 : ℝ) ≤ ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4) :=
      Real.one_le_rpow huN1 (by norm_num)
    rw [h1] at hlt
    nlinarith only [hlt, h2, hY1,
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N * Real.sqrt Pa.N)
        ((1 : ℝ) / 4)]
  have hceil1 : 1 ≤ K1 := by
    by_contra hcon
    have h0 : K1 = 0 := by omega
    have h : (1 : ℝ) ≤ (K1 : ℝ) :=
      le_trans hx1 (by rw [hK1]; exact Nat.le_ceil _)
    rw [h0] at h
    norm_num at h
  have hceil2 : 1 ≤ K2 := by
    by_contra hcon
    have h0 : K2 = 0 := by omega
    have h : (1 : ℝ) ≤ (K2 : ℝ) :=
      le_trans hx2 (by rw [hK2]; exact Nat.le_ceil _)
    rw [h0] at h
    norm_num at h
  have hK1K : K1 ≤ K := by rw [hK]; exact Nat.le_max_left _ _
  have hK2K : K2 ≤ K := by rw [hK]; exact Nat.le_max_right _ _
  have hKmax : K = K1 ∨ K = K2 := by
    rcases le_total K1 K2 with h | h
    · right; rw [hK, max_eq_right h]
    · left; rw [hK, max_eq_left h]
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h : (1 : ℕ) ≤ K := le_trans hceil1 hK1K
    exact_mod_cast h
  have hpow3 : (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) ^ ((3 : ℝ) / 2) := by
    have h : (K : ℝ) ^ ((3 : ℝ) / 2)
        = (K : ℝ) ^ (1 : ℝ) * (K : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hKpos]; norm_num
    rw [h, Real.rpow_one, Real.sqrt_eq_rpow]
  have hpow2 : (K : ℝ) * (K : ℝ) = (K : ℝ) ^ (2 : ℝ) := by
    rw [show ((2 : ℝ)) = 1 + 1 by norm_num, Real.rpow_add hKpos, Real.rpow_one]
  have key3 : ∀ x : ℝ, 0 ≤ x → (4 * x) ^ ((3 : ℝ) / 2) = 8 * x ^ ((3 : ℝ) / 2) := by
    intro x hx
    have h4 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [Real.mul_rpow (by norm_num) hx, h4]
  have key2 : ∀ x : ℝ, 0 ≤ x → (4 * x) ^ (2 : ℝ) = 16 * x ^ (2 : ℝ) := by
    intro x hx
    have h4 : (4 : ℝ) ^ (2 : ℝ) = 16 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [Real.mul_rpow (by norm_num) hx, h4]
  have hx1pow : ((Pa.N : ℝ) ^ ((1 : ℝ) / 4)) ^ ((3 : ℝ) / 2) = (Pa.N : ℝ) ^ ((3 : ℝ) / 8) := by
    rw [← Real.rpow_mul hN0]; norm_num
  have hx1pow2 : ((Pa.N : ℝ) ^ ((1 : ℝ) / 4)) ^ (2 : ℝ) = Real.sqrt (Pa.N) := by
    rw [← Real.rpow_mul hN0, Real.sqrt_eq_rpow]; norm_num
  have hx2pow : (((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4)) ^ ((3 : ℝ) / 2)
      = ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((3 : ℝ) / 8) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N * Real.sqrt Pa.N)]
    norm_num
  have hx2pow2 : (((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4)) ^ (2 : ℝ)
      = ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N * Real.sqrt Pa.N)]
    norm_num
  refine ⟨hceil1, hceil2, hK1K, hK2K, ?_, ?_, ?_⟩
  · rcases hKmax with hKc | hKc
    · have h1 : (K : ℝ) ≤ 4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := by rw [hKc]; exact hK1le
      calc (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) ^ ((3 : ℝ) / 2) := hpow3
        _ ≤ (4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4)) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow hK0 h1 (by norm_num)
        _ = 8 * (Pa.N : ℝ) ^ ((3 : ℝ) / 8) := by
            rw [key3 _ (Real.rpow_nonneg hN0 _), hx1pow]
        _ ≤ 8 * (Pa.θ * Real.sqrt Pa.N) := by linarith only [hu]
    · have h1 : (K : ℝ) ≤ 4 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4) := by
        rw [hKc]; exact hK2le
      calc (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) ^ ((3 : ℝ) / 2) := hpow3
        _ ≤ (4 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4)) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow hK0 h1 (by norm_num)
        _ = 8 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((3 : ℝ) / 8) := by
            rw [key3 _ (by positivity), hx2pow]
        _ ≤ 8 * (Pa.θ * Real.sqrt Pa.N) := by linarith only [hK2a]
  · rcases hKmax with hKc | hKc
    · have h1 : (K : ℝ) ≤ 4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := by rw [hKc]; exact hK1le
      calc (K : ℝ) * (K : ℝ) = (K : ℝ) ^ (2 : ℝ) := hpow2
        _ ≤ (4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4)) ^ (2 : ℝ) :=
            Real.rpow_le_rpow hK0 h1 (by norm_num)
        _ = 16 * Real.sqrt (Pa.N) := by
            rw [key2 _ (Real.rpow_nonneg hN0 _), hx1pow2]
        _ ≤ 16 * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) := by
            rw [← Real.rpow_natCast (Pa.θ * Real.sqrt Pa.N) 2]
            exact mul_le_mul_of_nonneg_left h12 (by norm_num)
    · have h1 : (K : ℝ) ≤ 4 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4) := by
        rw [hKc]; exact hK2le
      calc (K : ℝ) * (K : ℝ) = (K : ℝ) ^ (2 : ℝ) := hpow2
        _ ≤ (4 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4)) ^ (2 : ℝ) :=
            Real.rpow_le_rpow hK0 h1 (by norm_num)
        _ = 16 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 2) := by
            rw [key2 _ (by positivity), hx2pow2]
        _ ≤ 16 * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) := by
            rw [← Real.rpow_natCast (Pa.θ * Real.sqrt Pa.N) 2]
            exact mul_le_mul_of_nonneg_left hK2b (by norm_num)
  · have hlogN0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg hN1
    have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
      have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
      linarith only [h, Real.log_two_lt_d9]
    have hlogN4 : Real.log ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ≤ Real.log (Pa.N : ℝ) := by
      apply Real.log_le_log (by positivity)
      rw [hθNu]
      exact hθNle
    rcases hKmax with hKc | hKc
    · have h1 : (K : ℝ) ≤ 4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := by rw [hKc]; exact hK1le
      have h2 := Real.log_le_log hKpos h1
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hNpos _)),
        Real.log_rpow hNpos] at h2
      have h3 : ((1 : ℝ) / 4) * Real.log (Pa.N : ℝ) ≤ Real.log (Pa.N : ℝ) := by
        nlinarith only [hlogN0]
      linarith only [h2, hlog4, hlogN0, h3]
    · have h1 : (K : ℝ) ≤ 4 * ((Pa.θ * Real.sqrt Pa.N) * Real.sqrt Pa.N) ^ ((1 : ℝ) / 4) := by
        rw [hKc]; exact hK2le
      have h2 := Real.log_le_log hKpos h1
      rw [Real.log_mul (by norm_num)
        (ne_of_gt (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < Pa.θ * Real.sqrt Pa.N * Real.sqrt Pa.N) _)),
        Real.log_rpow (by positivity : (0 : ℝ) < Pa.θ * Real.sqrt Pa.N * Real.sqrt Pa.N)] at h2
      have h4 : ((1 : ℝ) / 4) * Real.log (Pa.N : ℝ) ≤ Real.log (Pa.N : ℝ) := by
        nlinarith only [hlogN0]
      linarith only [h2, hlog4, hlogN0, hlogN4, h4]

end

end Work.FIArea2.R6
