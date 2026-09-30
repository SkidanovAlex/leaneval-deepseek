import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog
import Submission.Work.BMF.primeSum_le_theta_diff
import Submission.Work.BMF.Kf_primeSum_reduction_abs
import Submission.Work.BMF.integral_floor_div_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.halasz_Kbound`

The bound `‖Σ_{n ≤ x} f n log n‖ ≤ x ∫_1^x ‖Σ_{n ≤ t} f n‖ / t² + C x` for `f` multiplicative,
`f 1 = 1`, `‖f n‖ ≤ 1`, with an absolute constant `C`.

The proof is assembled from independent pieces (proved in sibling files):

* `Work.BMF.Kf_primeSum_reduction_abs` : the sum `Σ_{n ≤ x} f n log n` equals the
  "prime-weighted" sum `Σ_{p ≤ x} log p · f p · Σ_{m ≤ x/p} f m` up to `O(x)`;
* `Work.BMF.primeSum_le_integral_sharp` : for any nonnegative `1`-Lipschitz sequence `d` with
  `d 1 ≤ 1`, `Σ_{p ≤ x} log p · d ⌊x/p⌋ ≤ x ∫_1^x d ⌊t⌋ / t² + C x`.

The present file contains the assembly (`halasz_Kbound_of`), a self-contained verification that
the assembly is correct, and a fallback assembly (`primeSum_le_integral_assembled`) of the second
ingredient from the three pieces `Work.BMF.primeSum_le_theta_diff`,
`Work.BMF.sum_abs_theta_err_bound` and `Work.BMF.sum_div_le_integral`.
-/

namespace Work.BMF

open Finset MeasureTheory

/-! ### Basic facts about `Mf` -/

/-- `Mf f (n+1) = Mf f n + f (n+1)`. -/
lemma Mf_succ (f : ℕ → ℂ) (n : ℕ) : Mf f ((n : ℝ) + 1) = Mf f (n : ℝ) + f (n + 1) := by
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  unfold Mf
  rw [hcast, Nat.floor_natCast, Nat.floor_natCast]
  exact Finset.sum_Icc_succ_top (by omega) f

/-- `Mf f` is constant on `[n, n+1)`. -/
lemma Mf_eq_of_floor_eq {x y : ℝ} (f : ℕ → ℂ) (h : ⌊x⌋₊ = ⌊y⌋₊) : Mf f x = Mf f y := by
  unfold Mf
  rw [h]

/-! ### Assembly of the main result -/

/-- Assembly of the main result from its two ingredients; the constant is absolute. -/
theorem halasz_Kbound_of (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hA : ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x : ℝ, 2 ≤ x →
        ‖Kf f x - ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p)‖ ≤ C₁ * x)
    (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hB : ∀ (d : ℕ → ℝ), (∀ n, 0 ≤ d n) → d 1 ≤ 1 →
      (∀ n, |d (n + 1) - d n| ≤ 1) → ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊) ≤
        x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + C₂ * x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x : ℝ, 2 ≤ x →
        ‖Kf f x‖ ≤ x * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) + C * x := by
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro f hf1 hmul hb x hx
  set d : ℕ → ℝ := fun n => ‖Mf f (n : ℝ)‖ with hddef
  have hd_norm : ∀ y : ℝ, ‖Mf f y‖ = ‖Mf f ⌊y⌋₊‖ := by
    intro y
    exact Mf_eq_of_floor_eq f (Nat.floor_natCast ⌊y⌋₊).symm ▸ rfl
  have hd0 : ∀ n, 0 ≤ d n := fun n => norm_nonneg _
  have hd1 : d 1 ≤ 1 := by
    have hm : Mf f (1 : ℝ) = f 1 := by simp [Mf]
    simp only [hddef, Nat.cast_one, hm, hf1, norm_one, le_refl]
  have hstep : ∀ n, |d (n + 1) - d n| ≤ 1 := by
    intro n
    have hsub : Mf f ((n : ℝ) + 1) - Mf f (n : ℝ) = f (n + 1) := by rw [Mf_succ]; ring
    have hsub' : Mf f ((n + 1 : ℕ) : ℝ) - Mf f ((n : ℕ) : ℝ) = f (n + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hsub
    calc |d (n + 1) - d n| = |‖Mf f ((n + 1 : ℕ) : ℝ)‖ - ‖Mf f ((n : ℕ) : ℝ)‖| := by
          simp only [hddef]
      _ ≤ ‖Mf f ((n + 1 : ℕ) : ℝ) - Mf f ((n : ℕ) : ℝ)‖ := abs_norm_sub_norm_le _ _
      _ = ‖f (n + 1)‖ := by rw [hsub']
      _ ≤ 1 := hb _
  have hPnorm :
      ‖∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p)‖ ≤
        ∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨-, hpprime⟩ := Nat.mem_primesLE.mp hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hnorm : ‖Mf f (x / p)‖ = d ⌊x / p⌋₊ := by
      simpa only [hddef] using hd_norm (x / p)
    have h1 : Real.log p * ‖f p‖ ≤ Real.log p * 1 := mul_le_mul_of_nonneg_left (hb p) hlog
    have h2 : ‖Mf f (x / p)‖ ≤ d ⌊x / p⌋₊ := hnorm.le
    have h3 : (0 : ℝ) ≤ ‖Mf f (x / p)‖ := norm_nonneg _
    have h4 : (0 : ℝ) ≤ Real.log p * 1 := by rw [mul_one]; exact hlog
    calc ‖(Real.log p : ℂ) * f p * Mf f (x / p)‖
        = Real.log p * ‖f p‖ * ‖Mf f (x / p)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
      _ ≤ Real.log p * 1 * d ⌊x / p⌋₊ := mul_le_mul h1 h2 h3 h4
      _ = Real.log p * d ⌊x / p⌋₊ := by ring
  have hA' := hA f hf1 hmul hb x hx
  have hB' := hB d hd0 hd1 hstep x hx
  have hint : (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) = ∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hddef, hd_norm]
  have htri : ‖Kf f x‖ ≤ ‖Kf f x - ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p)‖
      + ‖∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p)‖ := by
    have h := norm_add_le (Kf f x - ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p))
      (∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p))
    simpa using h
  calc ‖Kf f x‖
      ≤ ‖Kf f x - ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p)‖
        + ‖∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p)‖ := htri
    _ ≤ C₁ * x + (x * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) + C₂ * x) := by
        refine add_le_add hA' ?_
        calc ‖∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p : ℂ) * f p * Mf f (x / p)‖
            ≤ ∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊ := hPnorm
          _ ≤ x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + C₂ * x := hB'
          _ = x * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) + C₂ * x := by rw [hint]
    _ = x * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) + (C₁ + C₂) * x := by ring

/-! ### Auxiliary material for a self-contained verification of STEP B -/

/-- Chebyshev: `|θ z - z| ≤ z` for `z ≥ 0`. -/
lemma abs_theta_sub_id_le (z : ℝ) (hz : 0 ≤ z) : |Chebyshev.theta z - z| ≤ z := by
  have h1 : Chebyshev.theta z ≤ Real.log 4 * z := Chebyshev.theta_le_log4_mul_x hz
  have h2 : 0 ≤ Chebyshev.theta z := Chebyshev.theta_nonneg z
  have h3 : Real.log 4 < 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ≠ 0 by norm_num)
      rw [show (4 : ℝ) = 2 * 2 by norm_num, h]; ring
    nlinarith [Real.log_two_lt_d9]
  rw [abs_le]
  exact ⟨by linarith, by nlinarith⟩

/-- The PNT with a log-square saving, in the form used below. -/
lemma exists_theta_error_ten :
    ∃ T : ℝ, 10 ≤ T ∧ ∀ z : ℝ, T ≤ z → |Chebyshev.theta z - z| ≤ z / (Real.log z) ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog 2 (by norm_num)
  refine ⟨max x₀ 10, le_max_right _ _, fun z hz => ?_⟩
  have h := hx₀ z (le_trans (le_max_left _ _) hz)
  have hrw : Real.log z ^ (2 : ℝ) = (Real.log z) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast (Real.log z) 2]
  rwa [hrw] at h

/-- A `1`-Lipschitz sequence with `d 1 ≤ 1` satisfies `d M ≤ M` for `M ≥ 1`. -/
lemma lip_le_self (d : ℕ → ℝ) (h1 : d 1 ≤ 1) (hlip : ∀ n, |d (n + 1) - d n| ≤ 1) :
    ∀ M, 1 ≤ M → d M ≤ M := by
  have hstep : ∀ n, d (n + 1) - d n ≤ 1 := fun n => (abs_le.mp (hlip n)).2
  have hbase : d 1 ≤ ((1 : ℕ) : ℝ) := by simpa using h1
  refine Nat.le_induction (m := 1) hbase ?_
  intro n hn ih
  have h := hstep n
  push_cast
  linarith

/-- Summation by parts (Abel) on `[1,M]`. -/
lemma abel_sum_sub (d f : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, d n * (f n - f (n + 1))) =
      d 1 * f 1 - d M * f (M + 1) + ∑ n ∈ Finset.Icc 2 M, (d n - d (n - 1)) * f n := by
  refine Nat.le_induction (m := 1) ?base ?step M hM
  · rw [Finset.Icc_self, Finset.sum_singleton]
    have hempty : (Finset.Icc 2 1 : Finset ℕ) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    ring
  · intro n hn ih
    have h1 : (∑ k ∈ Finset.Icc 1 (n + 1), d k * (f k - f (k + 1)))
        = (∑ k ∈ Finset.Icc 1 n, d k * (f k - f (k + 1)))
          + d (n + 1) * (f (n + 1) - f (n + 2)) :=
      Finset.sum_Icc_succ_top (by omega) _
    have h2 : (∑ k ∈ Finset.Icc 2 (n + 1), (d k - d (k - 1)) * f k)
        = (∑ k ∈ Finset.Icc 2 n, (d k - d (k - 1)) * f k)
          + (d (n + 1) - d n) * f (n + 1) := by
      have h := Finset.sum_Icc_succ_top (a := 2) (b := n) (by omega : 2 ≤ n + 1)
        (fun k => (d k - d (k - 1)) * f k)
      simpa using h
    rw [h1, h2, ih]
    ring

/-- Telescoping of consecutive differences: `Σ_{m=a}^{b} (g (m+1) - g m) = g (b+1) - g a`. -/
lemma sum_Icc_telescope (g : ℕ → ℝ) (a : ℕ) : ∀ b, a ≤ b →
    ∑ m ∈ Finset.Icc a b, (g (m + 1) - g m) = g (b + 1) - g a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ k + 1), ih]
    ring

/-- **Reciprocal-log-square bound.** For `x > 1` and `u m = log (x/m) > 0` for `1 ≤ m ≤ J + 1`,
`Σ_{m=1}^{J} 1/(m u m²) ≤ 2/u (J+1)`.  The pointwise inequality is
`1/(m u m²) ≤ 2 (1/u (m+1) - 1/u m)`: since `u m - u (m+1) = log (1 + 1/m) ≥ 1/(m+1)`
(`Real.one_sub_inv_le_log_of_pos` at `(m+1)/m`) and `u (m+1) ≤ u m`, the right-hand side is
`2 (u m - u (m+1))/(u m · u (m+1)) ≥ 2/((m+1) u m²) ≥ 1/(m u m²)`, and the sum telescopes. -/
lemma sum_inv_div_log_sq_le (x : ℝ) (J : ℕ) (hx : 1 < x)
    (hpos : ∀ m : ℕ, 1 ≤ m → m ≤ J + 1 → 0 < Real.log (x / (m : ℝ))) :
    ∑ m ∈ Finset.Icc 1 J, (1 / (m : ℝ)) / (Real.log (x / m)) ^ 2
      ≤ 2 / Real.log (x / (J + 1)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set g : ℕ → ℝ := fun m => (Real.log (x / (m : ℝ)))⁻¹ with hg
  have hterm : ∀ m ∈ Finset.Icc 1 J,
      (1 / (m : ℝ)) / (Real.log (x / m)) ^ 2 ≤ 2 * (g (m + 1) - g m) := by
    intro m hm
    have hmle : m ≤ J := (Finset.mem_Icc.mp hm).2
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hu : 0 < Real.log (x / (m : ℝ)) := hpos m hm1 (by omega)
    have hu' : 0 < Real.log (x / ((m : ℝ) + 1)) := by
      have := hpos (m + 1) (by omega) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using this
    simp only [hg]
    push_cast
    have h2 : Real.log (x / ((m : ℝ) + 1)) ≤ Real.log (x / (m : ℝ)) := by
      apply Real.log_le_log (by positivity)
      apply div_le_div_of_nonneg_left hx0.le hmp
      linarith
    have hge : 1 / ((m : ℝ) + 1) ≤ Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1)) := by
      have hsplit : Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1))
          = Real.log (((m : ℝ) + 1) / m) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [hsplit]
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((m : ℝ) + 1) / m by positivity)
      have hx' : 1 - (((m : ℝ) + 1) / m)⁻¹ = 1 / ((m : ℝ) + 1) := by
        rw [inv_div]
        have h1 : (m : ℝ) ≠ 0 := ne_of_gt hmp
        have h2' : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        try ring
      rw [hx'] at h
      exact h
    have h3 : 1 ≤ 2 * (m : ℝ) / ((m : ℝ) + 1) := by
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      linarith
    have hmain : Real.log (x / ((m : ℝ) + 1)) ≤ 2 * (m : ℝ) * Real.log (x / (m : ℝ))
        * (Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1))) := by
      have h4 : Real.log (x / (m : ℝ)) ≤ (2 * (m : ℝ) / ((m : ℝ) + 1)) * Real.log (x / (m : ℝ)) := by
        nlinarith [h3, hu]
      have h5 : (2 * (m : ℝ) / ((m : ℝ) + 1)) * Real.log (x / (m : ℝ))
          ≤ 2 * (m : ℝ) * Real.log (x / (m : ℝ))
            * (Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1))) := by
        have h6 : (2 * (m : ℝ) / ((m : ℝ) + 1)) * Real.log (x / (m : ℝ))
            = 2 * (m : ℝ) * Real.log (x / (m : ℝ)) * (1 / ((m : ℝ) + 1)) := by
          field_simp
          try ring
        rw [h6]
        have h7 : (0 : ℝ) < 2 * (m : ℝ) * Real.log (x / (m : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_left hge h7.le
      linarith [h2, h4, h5]
    have hkey : 2 * ((Real.log (x / ((m : ℝ) + 1)))⁻¹ - (Real.log (x / (m : ℝ)))⁻¹)
        = 2 * (Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1)))
          / (Real.log (x / (m : ℝ)) * Real.log (x / ((m : ℝ) + 1))) := by
      field_simp
      try ring
    rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
    have h10 : Real.log (x / ((m : ℝ) + 1)) / (m : ℝ)
        ≤ 2 * Real.log (x / (m : ℝ)) * (Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1))) := by
      rw [div_le_iff₀ hmp]
      nlinarith [hmain]
    have h9 : (1 / (m : ℝ)) * (Real.log (x / (m : ℝ)) * Real.log (x / ((m : ℝ) + 1)))
        ≤ (2 * (Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1)))) * (Real.log (x / (m : ℝ))) ^ 2 := by
      calc (1 / (m : ℝ)) * (Real.log (x / (m : ℝ)) * Real.log (x / ((m : ℝ) + 1)))
          = (Real.log (x / ((m : ℝ) + 1)) / (m : ℝ)) * Real.log (x / (m : ℝ)) := by ring
        _ ≤ (2 * Real.log (x / (m : ℝ)) * (Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1))))
              * Real.log (x / (m : ℝ)) := mul_le_mul_of_nonneg_right h10 hu.le
        _ = (2 * (Real.log (x / (m : ℝ)) - Real.log (x / ((m : ℝ) + 1)))) * (Real.log (x / (m : ℝ))) ^ 2 := by
            ring
    exact h9
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · rw [hJ0]
    have hempty : (Finset.Icc 1 0 : Finset ℕ) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    refine div_nonneg (by norm_num) ?_
    have h := (hpos 1 le_rfl (by omega)).le
    simpa only [Nat.cast_zero, zero_add, Nat.cast_one] using h
  · calc ∑ m ∈ Finset.Icc 1 J, (1 / (m : ℝ)) / (Real.log (x / m)) ^ 2
        ≤ ∑ m ∈ Finset.Icc 1 J, 2 * (g (m + 1) - g m) := Finset.sum_le_sum hterm
      _ = 2 * ∑ m ∈ Finset.Icc 1 J, (g (m + 1) - g m) := by rw [Finset.mul_sum]
      _ = 2 * (g (J + 1) - g 1) := by rw [sum_Icc_telescope g 1 J hJpos]
      _ ≤ 2 / Real.log (x / (J + 1)) := by
        have hJ1 : 0 < Real.log (x / ((J : ℝ) + 1)) := by
          have := hpos (J + 1) (by omega) le_rfl
          simpa only [Nat.cast_add, Nat.cast_one] using this
        have h1 : 0 < Real.log (x / (1 : ℝ)) := by
          have := hpos 1 le_rfl (by omega)
          simpa only [Nat.cast_one] using this
        have hgJ : g (J + 1) = (Real.log (x / ((J : ℝ) + 1)))⁻¹ := by
          simp only [hg, Nat.cast_add, Nat.cast_one]
        have hg1 : g 1 = (Real.log (x / (1 : ℝ)))⁻¹ := by
          simp only [hg, Nat.cast_one]
        rw [hgJ, hg1]
        have hle2 : (Real.log (x / ((J : ℝ) + 1)))⁻¹ - (Real.log (x / (1 : ℝ)))⁻¹
            ≤ (Real.log (x / ((J : ℝ) + 1)))⁻¹ := by
          have : 0 ≤ (Real.log (x / (1 : ℝ)))⁻¹ := inv_nonneg.mpr h1.le
          linarith
        calc 2 * ((Real.log (x / ((J : ℝ) + 1)))⁻¹ - (Real.log (x / (1 : ℝ)))⁻¹)
            ≤ 2 * (Real.log (x / ((J : ℝ) + 1)))⁻¹ := by linarith
          _ = 2 / Real.log (x / ((J : ℝ) + 1)) := by ring

/-- **Error-sum bound.** If `E z = θ z - z` satisfies `|E z| ≤ z / log²z` for `z ≥ T` (`T ≥ 10`),
then `Σ_{2 ≤ m ≤ x} |E (x/m)| ≤ C x`.  Uses `|E z| ≤ z` (Chebyshev) for `x/m < T`, the PNT
hypothesis for `x/m ≥ T`, the reciprocal-log-square bound above for the "good" part and
`Σ_{J+1 ≤ m ≤ M} 1/m ≤ (M-J)/(J+1) ≤ 2T` for the "bad" part. -/
lemma theta_err_sum_le (T : ℝ) (hT : 10 ≤ T)
    (hθ : ∀ z : ℝ, T ≤ z → |Chebyshev.theta z - z| ≤ z / (Real.log z) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ∑ m ∈ Finset.Icc 2 ⌊x⌋₊, |Chebyshev.theta (x / m) - x / m| ≤ C * x := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT2 : 0 < Real.log (T / 2) := Real.log_pos (by linarith)
  refine ⟨2 / Real.log (T / 2) + 4 * T + 1, ?_, ?_⟩
  · positivity
  · intro x hx
    set M : ℕ := ⌊x⌋₊ with hMdef
    set J : ℕ := ⌊x / T⌋₊ with hJdef
    set gg : ℕ → ℝ := fun m => if T ≤ x / (m : ℝ) then 1 / (Real.log (x / m)) ^ 2 else 1 with hgg
    have hMx : (M : ℝ) ≤ x := by rw [hMdef]; exact Nat.floor_le (by linarith)
    have hx0 : (0 : ℝ) < x := by linarith
    by_cases hsmall : x ≤ 4 * T
    · -- crude bound for bounded `x`
      have h1 : (∑ m ∈ Finset.Icc 2 M, |Chebyshev.theta (x / m) - x / m|)
          ≤ ∑ m ∈ Finset.Icc 2 M, x / 2 := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have hz : 0 ≤ x / (m : ℝ) := by positivity
        have hb := abs_theta_sub_id_le (x / (m : ℝ)) hz
        have hc : x / (m : ℝ) ≤ x / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hm2
        linarith
      have h2 : (∑ m ∈ Finset.Icc 2 M, x / 2) = ((Finset.Icc 2 M).card : ℝ) * (x / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc 2 M).card : ℝ) ≤ (M : ℝ) := by
        have hc : (Finset.Icc 2 M).card = M - 1 := by rw [Nat.card_Icc]; omega
        rw [hc]
        exact_mod_cast (Nat.sub_le M 1)
      have hfinal : (4 * T) * (x / 2) ≤ (2 / Real.log (T / 2) + 4 * T + 1) * x := by
        have h1 : 2 * T ≤ 2 / Real.log (T / 2) + 4 * T + 1 := by
          have h2 : 0 ≤ 2 / Real.log (T / 2) := div_nonneg (by norm_num) hlogT2.le
          linarith
        calc (4 * T) * (x / 2) = (2 * T) * x := by ring
          _ ≤ (2 / Real.log (T / 2) + 4 * T + 1) * x := mul_le_mul_of_nonneg_right h1 (by linarith)
      calc (∑ m ∈ Finset.Icc 2 M, |Chebyshev.theta (x / m) - x / m|)
          ≤ ∑ m ∈ Finset.Icc 2 M, x / 2 := h1
        _ = ((Finset.Icc 2 M).card : ℝ) * (x / 2) := h2
        _ ≤ (M : ℝ) * (x / 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ (4 * T) * (x / 2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (2 / Real.log (T / 2) + 4 * T + 1) * x := hfinal
    · -- main case
      push_neg at hsmall
      have hJ1 : 1 ≤ J := by
        rw [hJdef]
        apply Nat.le_floor
        push_cast
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < T)]
        linarith
      have hJM : J ≤ M := by
        rw [hJdef, hMdef]
        apply Nat.floor_mono
        exact div_le_self (by linarith) (by linarith)
      have hJfloor : (J : ℝ) ≤ x / T := by rw [hJdef]; exact Nat.floor_le (by positivity)
      have hJx : (J : ℝ) + 1 ≤ 5 * x / (4 * T) := by
        have h2 : 1 ≤ x / (4 * T) := by
          rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * T)]
          linarith
        have h3 : x / T + x / (4 * T) = 5 * x / (4 * T) := by
          have hxne : x ≠ 0 := ne_of_gt hx0
          have hTne : T ≠ 0 := ne_of_gt hT0
          field_simp
          ring
        linarith [hJfloor, h2, h3]
      have h4T5 : 4 * T / 5 ≤ x / ((J : ℝ) + 1) := by
        have h3 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
        have h4 : x / (5 * x / (4 * T)) = 4 * T / 5 := by
          have hxne : x ≠ 0 := ne_of_gt hx0
          have hTne : T ≠ 0 := ne_of_gt hT0
          field_simp
          try ring
        calc 4 * T / 5 = x / (5 * x / (4 * T)) := h4.symm
          _ ≤ x / ((J : ℝ) + 1) := div_le_div_of_nonneg_left hx0.le h3 hJx
      have hxT_gt : T < x := by linarith
      -- the pointwise bound
      have hpoint : ∀ m ∈ Finset.Icc 2 M,
          |Chebyshev.theta (x / m) - x / m| ≤ (x / m) * gg m := by
        intro m hm
        by_cases hc : T ≤ x / (m : ℝ)
        · rw [hgg]
          simp only [hc, if_true]
          have hb : |Chebyshev.theta (x / m) - x / m| ≤ (x / m) / (Real.log (x / m)) ^ 2 := hθ _ hc
          calc |Chebyshev.theta (x / m) - x / m| ≤ (x / m) / (Real.log (x / m)) ^ 2 := hb
            _ = (x / m) * (1 / (Real.log (x / m)) ^ 2) := by ring_nf
        · rw [hgg]
          simp only [hc, if_false, mul_one]
          have hz : 0 ≤ x / (m : ℝ) := by positivity
          exact abs_theta_sub_id_le (x / (m : ℝ)) hz
      -- split the index range at `J`
      have hunion : (Finset.Icc 2 M : Finset ℕ) = Finset.Icc 2 J ∪ Finset.Icc (J + 1) M := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_union]
        omega
      have hdisj : Disjoint (Finset.Icc 2 J : Finset ℕ) (Finset.Icc (J + 1) M) := by
        rw [Finset.disjoint_left]
        intro m hm1 hm2
        simp only [Finset.mem_Icc] at hm1 hm2
        omega
      have hgood : (∑ m ∈ Finset.Icc 2 J, (1 / (m : ℝ)) * gg m) ≤ 2 / Real.log (T / 2) := by
        have h1 : (∑ m ∈ Finset.Icc 2 J, (1 / (m : ℝ)) * gg m)
            = ∑ m ∈ Finset.Icc 2 J, (1 / (m : ℝ)) / (Real.log (x / m)) ^ 2 := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hmJ : m ≤ J := (Finset.mem_Icc.mp hm).2
          have hmr : (m : ℝ) ≤ x / T := le_trans (by exact_mod_cast hmJ) hJfloor
          have hm0 : (0 : ℝ) < (m : ℝ) := by
            have : 1 ≤ m := le_trans (by norm_num) (Finset.mem_Icc.mp hm).1
            exact_mod_cast this
          have hxT : T ≤ x / (m : ℝ) := by
            rw [le_div_iff₀ hm0]
            rw [le_div_iff₀ hT0] at hmr
            linarith
          rw [hgg]
          simp only [hxT, ite_true]
          ring
        rw [h1]
        have h2 : (∑ m ∈ Finset.Icc 2 J, (1 / (m : ℝ)) / (Real.log (x / m)) ^ 2)
            ≤ ∑ m ∈ Finset.Icc 1 J, (1 / (m : ℝ)) / (Real.log (x / m)) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro m hm
            exact Finset.mem_Icc.mpr ⟨le_trans (by norm_num) (Finset.mem_Icc.mp hm).1,
              (Finset.mem_Icc.mp hm).2⟩
          · intro m hm _
            have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
            have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
            have : (0 : ℝ) ≤ (Real.log (x / (m : ℝ))) ^ 2 := sq_nonneg _
            positivity
        have h3 := sum_inv_div_log_sq_le x J (by linarith : (1 : ℝ) < x) (fun m hm1 hmJ1 => by
          have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
          have hmJ' : (m : ℝ) ≤ (J : ℝ) + 1 := by exact_mod_cast hmJ1
          have hle : x / ((J : ℝ) + 1) ≤ x / m :=
            div_le_div_of_nonneg_left hx0.le hm0 (by linarith)
          exact Real.log_pos (lt_of_lt_of_le (by linarith [h4T5]) hle))
        have h4 : 2 / Real.log (x / ((J : ℝ) + 1)) ≤ 2 / Real.log (T / 2) := by
          refine div_le_div_of_nonneg_left (by norm_num) hlogT2 ?_
          exact Real.log_le_log (by linarith)
            (le_trans (by linarith : T / 2 ≤ 4 * T / 5) h4T5)
        linarith [h2, h3, h4]
      have hbad : (∑ m ∈ Finset.Icc (J + 1) M, (1 / (m : ℝ)) * gg m) ≤ 2 * T := by
        have h1 : (∑ m ∈ Finset.Icc (J + 1) M, (1 / (m : ℝ)) * gg m)
            = ∑ m ∈ Finset.Icc (J + 1) M, (1 / (m : ℝ)) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hmge : J + 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm0 : (0 : ℝ) < (m : ℝ) := by
            have : 1 ≤ m := le_trans (by omega) hmge
            exact_mod_cast this
          have hlt : x / (m : ℝ) < T := by
            have hJp : x / T < (J : ℝ) + 1 := by
              have := Nat.lt_floor_add_one (x / T)
              simpa [hJdef] using this
            rw [div_lt_iff₀ hT0] at hJp
            have hm' : ((J : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hmge
            rw [div_lt_iff₀ hm0]
            nlinarith [hJp, hm', hT0]
          rw [hgg]
          simp only [if_neg (not_le.mpr hlt), mul_one]
        rw [h1]
        have h2 : (∑ m ∈ Finset.Icc (J + 1) M, (1 / (m : ℝ)))
            ≤ ((Finset.Icc (J + 1) M).card : ℝ) * (1 / ((J + 1 : ℕ) : ℝ)) := by
          have hc : ∑ _m ∈ Finset.Icc (J + 1) M, (1 / (((J + 1 : ℕ)) : ℝ))
              = ((Finset.Icc (J + 1) M).card : ℝ) * (1 / ((J + 1 : ℕ) : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          rw [← hc]
          refine Finset.sum_le_sum fun m hm => ?_
          have hmge : J + 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have h1 : (0 : ℝ) < ((J + 1 : ℕ) : ℝ) := by positivity
          have h2 : ((J + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmge
          exact one_div_le_one_div_of_le h1 h2
        have hcard : ((Finset.Icc (J + 1) M).card : ℝ) ≤ (M : ℝ) := by
          have hc : (Finset.Icc (J + 1) M).card = M - J := by rw [Nat.card_Icc]; omega
          rw [hc]
          exact_mod_cast (Nat.sub_le M J)
        have hJlow2 : x / (2 * T) ≤ (J : ℝ) := by
          have hJp1 : x / T - 1 < (J : ℝ) := by
            have h := Nat.lt_floor_add_one (x / T)
            rw [← hJdef] at h
            push_cast at h
            linarith
          have hkey : x / (2 * T) ≤ x / T - 1 := by
            have hxne : x ≠ 0 := ne_of_gt hx0
            have hTne : T ≠ 0 := ne_of_gt hT0
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * T)]
            have h2 : (x / T - 1) * (2 * T) = 2 * x - 2 * T := by
              field_simp
              try ring
            rw [h2]
            linarith [hsmall]
          linarith [hkey, hJp1]
        have hmain2 : ((Finset.Icc (J + 1) M).card : ℝ) * (1 / ((J + 1 : ℕ) : ℝ)) ≤ 2 * T := by
          have hMle : ((Finset.Icc (J + 1) M).card : ℝ) ≤ x := le_trans hcard hMx
          have hJp : (1 : ℝ) / ((J + 1 : ℕ) : ℝ) ≤ 1 / (J : ℝ) := by
            have h1 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
            have h2 : (J : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by push_cast; linarith
            exact one_div_le_one_div_of_le h1 h2
          have hx2 : x * (1 / (J : ℝ)) ≤ 2 * T := by
            have h1 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
            rw [mul_one_div, div_le_iff₀ h1]
            have h3 : x ≤ 2 * T * (J : ℝ) := by
              rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * T)] at hJlow2
              linarith
            linarith
          calc ((Finset.Icc (J + 1) M).card : ℝ) * (1 / ((J + 1 : ℕ) : ℝ))
              ≤ ((Finset.Icc (J + 1) M).card : ℝ) * (1 / (J : ℝ)) :=
                mul_le_mul_of_nonneg_left hJp (by positivity)
            _ ≤ x * (1 / (J : ℝ)) := by
                refine mul_le_mul_of_nonneg_right hMle ?_
                positivity
            _ ≤ 2 * T := hx2
        linarith [h2, hmain2]
      calc (∑ m ∈ Finset.Icc 2 M, |Chebyshev.theta (x / m) - x / m|)
          ≤ ∑ m ∈ Finset.Icc 2 M, (x / m) * gg m := Finset.sum_le_sum hpoint
        _ = x * ∑ m ∈ Finset.Icc 2 M, (1 / (m : ℝ)) * gg m := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
        _ = x * ((∑ m ∈ Finset.Icc 2 J, (1 / (m : ℝ)) * gg m)
              + (∑ m ∈ Finset.Icc (J + 1) M, (1 / (m : ℝ)) * gg m)) := by
            rw [hunion, Finset.sum_union hdisj]
        _ ≤ x * (2 / Real.log (T / 2) + 2 * T) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            linarith [hgood, hbad]
        _ ≤ (2 / Real.log (T / 2) + 4 * T + 1) * x := by
            have h1 : 2 / Real.log (T / 2) + 2 * T
                ≤ 2 / Real.log (T / 2) + 4 * T + 1 := by linarith
            calc x * (2 / Real.log (T / 2) + 2 * T)
                ≤ x * (2 / Real.log (T / 2) + 4 * T + 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
              _ = (2 / Real.log (T / 2) + 4 * T + 1) * x := by ring

/-- The step function `t ↦ d ⌊t⌋₊ / t²` is interval integrable on `[1, M]` for `M ≥ 1`. -/
lemma intervalIntegrable_floor_div_sq (d : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) :
    IntervalIntegrable (fun t : ℝ => d ⌊t⌋₊ / t ^ 2) volume 1 (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => simpa using IntervalIntegrable.refl (f := fun t : ℝ => d ⌊t⌋₊ / t ^ 2) (μ := volume) (a := (1 : ℝ))
  | succ k hk ih =>
    have hk' : IntervalIntegrable (fun t : ℝ => d ⌊t⌋₊ / t ^ 2) volume (k : ℝ)
        ((k : ℝ) + 1) := floor_div_sq_step_int d k hk
    have h := ih.trans hk'
    simpa [Nat.cast_add, Nat.cast_one] using h

/-- The same step function is interval integrable on `[M, x]` for `M ≤ x ≤ M+1`, `M ≥ 1`. -/
lemma intervalIntegrable_floor_div_sq_tail (d : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) {x : ℝ}
    (hx : (M : ℝ) ≤ x) (hx1 : x ≤ (M : ℝ) + 1) :
    IntervalIntegrable (fun t : ℝ => d ⌊t⌋₊ / t ^ 2) volume (M : ℝ) x :=
  (floor_div_sq_step_int d M hM).mono_set (by
    intro y hy
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at hy
    rw [Set.uIcc_of_le (by linarith : (M : ℝ) ≤ (M : ℝ) + 1), Set.mem_Icc]
    exact ⟨hy.1, hy.2.trans hx1⟩)

/-- **Main-term comparison.** For a nonnegative `1`-Lipschitz `d` with `d 1 ≤ 1`,
`Σ_{n ≤ x} d n (x/n - x/(n+1)) ≤ x ∫_1^x d⌊t⌋/t² + x`.  The coefficient of the integral is
exactly `1`; the identity `∫_n^{n+1} d⌊t⌋₊/t² = d n (1/n - 1/(n+1))`
(`Work.BMF.integral_floor_div_sq`) makes the main terms match with no loss. -/
lemma theta_main_le_integral (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (hd1 : d 1 ≤ 1)
    (hlip : ∀ n, |d (n + 1) - d n| ≤ 1) (x : ℝ) (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, d n * (x / (n : ℝ) - x / ((n : ℝ) + 1)))
      ≤ x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + x := by
  set M := ⌊x⌋₊ with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    apply Nat.le_floor
    push_cast
    linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hMle : (M : ℝ) ≤ x := by rw [hMdef]; exact Nat.floor_le (by linarith)
  have hMlt : x ≤ (M : ℝ) + 1 := le_of_lt (by rw [hMdef]; exact Nat.lt_floor_add_one x)
  have hId := integral_floor_div_sq d M hM1
  have hsum_eq : (∑ n ∈ Finset.Icc 1 M, d n * (x / (n : ℝ) - x / ((n : ℝ) + 1)))
      = x * (∑ n ∈ Finset.Icc 1 M, d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hsplit : (∑ n ∈ Finset.Icc 1 M, d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
      = (∑ n ∈ Finset.Icc 1 (M - 1), d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
        + d M * (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) := by
    have h := Finset.sum_Icc_succ_top (a := 1) (b := M - 1) (by omega : 1 ≤ M - 1 + 1)
      (fun n => d n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
    simp only [Nat.sub_add_cancel hM1] at h
    exact h
  have hbdry : d M * (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) ≤ 1 := by
    have hdM : d M ≤ (M : ℝ) := lip_le_self d hd1 hlip M hM1
    have hnn : (0 : ℝ) ≤ d M := hd M
    have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMpos
    have hM0' : (M : ℝ) + 1 ≠ 0 := by positivity
    have hval : (1 / (M : ℝ) - 1 / ((M : ℝ) + 1)) = 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by
      rw [div_sub_div 1 1 hM0 hM0']
      ring_nf
    rw [hval, mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) * ((M : ℝ) + 1))]
    nlinarith
  rw [hsum_eq, hsplit, ← hId]
  have hInt1 : IntervalIntegrable (fun t : ℝ => d ⌊t⌋₊ / t ^ 2) volume (1 : ℝ) (M : ℝ) :=
    intervalIntegrable_floor_div_sq d M hM1
  have hInt2 : IntervalIntegrable (fun t : ℝ => d ⌊t⌋₊ / t ^ 2) volume (M : ℝ) x :=
    intervalIntegrable_floor_div_sq_tail d M hM1 hMle hMlt
  have hadd := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
  have htail : 0 ≤ ∫ t in (M : ℝ)..x, d ⌊t⌋₊ / t ^ 2 :=
    intervalIntegral.integral_nonneg hMle fun t _ => div_nonneg (hd _) (by positivity)
  have hcmp : (∫ t in (1 : ℝ)..(M : ℝ), d ⌊t⌋₊ / t ^ 2) ≤ ∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2 := by
    linarith
  nlinarith [hcmp, hbdry]

/-- **STEP B** (`Work.BMF.primeSum_le_integral_sharp`), proved here from
`Work.BMF.primeSum_le_theta_diff` (reindexing + Chebyshev step bound), the main-term comparison
`Work.BMF.theta_main_le_integral` and the error bound `Work.BMF.theta_err_sum_le`. -/
theorem primeSum_le_integral_self :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ → ℝ), (∀ n, 0 ≤ d n) → d 1 ≤ 1 →
      (∀ n, |d (n + 1) - d n| ≤ 1) → ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊) ≤
        x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + C * x := by
  obtain ⟨T, hT, hθT⟩ := exists_theta_error_ten
  obtain ⟨C₀, hC₀pos, hC₀⟩ := theta_err_sum_le T hT hθT
  refine ⟨C₀ + 3, by linarith, ?_⟩
  intro d hd0 hd1 hlip x hx
  set M : ℕ := ⌊x⌋₊ with hMdef
  set f : ℕ → ℝ := fun n => Chebyshev.theta (x / (n : ℝ)) - x / (n : ℝ) with hf
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    apply Nat.le_floor
    push_cast
    linarith
  have h1 := primeSum_le_theta_diff d hd0 x hx
  have hsplit : (∑ n ∈ Finset.Icc 1 M,
        d n * (Chebyshev.theta (x / n) - Chebyshev.theta (x / ((n : ℝ) + 1))))
      = (∑ n ∈ Finset.Icc 1 M, d n * (x / (n : ℝ) - x / ((n : ℝ) + 1)))
        + (∑ n ∈ Finset.Icc 1 M, d n * (f n - f (n + 1))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hf]
    push_cast
    ring
  have hmain := theta_main_le_integral d hd0 hd1 hlip x hx
  have hE : (∑ n ∈ Finset.Icc 1 M, d n * (f n - f (n + 1))) ≤ (C₀ + 2) * x := by
    have habel := abel_sum_sub d f M hM1
    have hf1 : f 1 = Chebyshev.theta x - x := by simp only [hf, Nat.cast_one, div_one]
    have hb1 : d 1 * f 1 ≤ x := by
      have hd1' : (0 : ℝ) ≤ d 1 := hd0 1
      have hf1' : |f 1| ≤ x := by
        rw [hf1]
        exact abs_theta_sub_id_le x (by linarith)
      calc d 1 * f 1 ≤ d 1 * |f 1| := mul_le_mul_of_nonneg_left (le_abs_self _) hd1'
        _ ≤ 1 * |f 1| := mul_le_mul_of_nonneg_right hd1 (abs_nonneg _)
        _ = |f 1| := one_mul _
        _ ≤ x := hf1'
    have hb2 : -(d M * f (M + 1)) ≤ x := by
      have hdM : d M ≤ (M : ℝ) := lip_le_self d hd1 hlip M hM1
      have hz : 0 ≤ x / ((M : ℝ) + 1) := by positivity
      have hfM : |f (M + 1)| ≤ x / ((M : ℝ) + 1) := by
        have h := abs_theta_sub_id_le (x / ((M : ℝ) + 1)) hz
        have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        simpa only [hf, hcast] using h
      have hdM0 : (0 : ℝ) ≤ d M := hd0 M
      have habs : |d M * f (M + 1)| ≤ x := by
        rw [abs_mul, abs_of_nonneg hdM0]
        calc d M * |f (M + 1)| ≤ (M : ℝ) * (x / ((M : ℝ) + 1)) :=
              mul_le_mul hdM hfM (abs_nonneg _) (by positivity)
          _ ≤ x := by
              rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
              nlinarith [Nat.floor_le (show (0 : ℝ) ≤ x by linarith)]
      linarith [neg_le_abs (d M * f (M + 1)), habs]
    have hb3 : (∑ n ∈ Finset.Icc 2 M, (d n - d (n - 1)) * f n) ≤ C₀ * x := by
      have h2 : ∀ n ∈ Finset.Icc 2 M, |(d n - d (n - 1)) * f n| ≤ |f n| := by
        intro n hn
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hle : |d n - d (n - 1)| ≤ 1 := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simpa using hlip m
        calc |(d n - d (n - 1)) * f n| = |d n - d (n - 1)| * |f n| := abs_mul _ _
          _ ≤ 1 * |f n| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
          _ = |f n| := one_mul _
      have h3 : (∑ n ∈ Finset.Icc 2 M, |f n|) ≤ C₀ * x := by
        have := hC₀ x hx
        simpa only [hf] using this
      calc (∑ n ∈ Finset.Icc 2 M, (d n - d (n - 1)) * f n)
          ≤ ∑ n ∈ Finset.Icc 2 M, |(d n - d (n - 1)) * f n| :=
            Finset.sum_le_sum fun n _ => le_abs_self _
        _ ≤ ∑ n ∈ Finset.Icc 2 M, |f n| := Finset.sum_le_sum h2
        _ ≤ C₀ * x := h3
    rw [habel]
    linarith [hb1, hb2, hb3]
  calc (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊)
      ≤ ∑ n ∈ Finset.Icc 1 M,
          d n * (Chebyshev.theta (x / n) - Chebyshev.theta (x / ((n : ℝ) + 1))) := h1
    _ = _ := hsplit
    _ ≤ (x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + x) + (C₀ + 2) * x := add_le_add hmain hE
    _ = x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + (C₀ + 3) * x := by ring

/-- Fallback assembly of `Work.BMF.primeSum_le_integral_sharp` from three pieces
(taken as hypotheses so that the assembly is checked independently). -/
theorem primeSum_le_integral_assembled
    (hS1 : ∀ (d : ℕ → ℝ), (∀ n, 0 ≤ d n) → ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊) ≤
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          d n * (Chebyshev.theta (x / n) - Chebyshev.theta (x / ((n : ℝ) + 1))))
    (T : ℝ) (hT : 10 ≤ T)
    (hS2 : ∀ e : ℝ → ℝ, (∀ z : ℝ, 0 ≤ z → |e z| ≤ z) →
      (∀ z : ℝ, T ≤ z → |e z| ≤ z / (Real.log z) ^ 2) →
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ x : ℝ, 2 ≤ x → ∑ m ∈ Finset.Icc 2 ⌊x⌋₊, |e (x / m)| ≤ C₀ * x)
    (hS3 : ∀ (d : ℕ → ℝ), (∀ n, 0 ≤ d n) → d 1 ≤ 1 → (∀ n, |d (n + 1) - d n| ≤ 1) →
      ∀ x : ℝ, 2 ≤ x →
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, d n * (x / (n : ℝ) - x / ((n : ℝ) + 1))) ≤
        x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + x)
    (hθT : ∀ z : ℝ, T ≤ z → |Chebyshev.theta z - z| ≤ z / (Real.log z) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ → ℝ), (∀ n, 0 ≤ d n) → d 1 ≤ 1 →
      (∀ n, |d (n + 1) - d n| ≤ 1) → ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊) ≤
        x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + C * x := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hS2 (fun z => Chebyshev.theta z - z)
    (fun z hz => abs_theta_sub_id_le z hz) hθT
  refine ⟨C₀ + 3, by linarith, ?_⟩
  intro d hd0 hd1 hlip x hx
  have hM1 : 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  set f : ℕ → ℝ := fun n => Chebyshev.theta (x / n) - x / n with hf
  have hθ := hS1 d hd0 x hx
  have hsplit :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          d n * (Chebyshev.theta (x / n) - Chebyshev.theta (x / ((n : ℝ) + 1))))
        = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, d n * (x / (n : ℝ) - x / ((n : ℝ) + 1)))
          + (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, d n * (f n - f (n + 1))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hf]
    push_cast
    ring
  have habel := abel_sum_sub d f ⌊x⌋₊ hM1
  have hf1 : f 1 = Chebyshev.theta x - x := by
    simp only [hf]
    norm_num
  have hb1 : d 1 * f 1 ≤ x := by
    have h1' : (0 : ℝ) ≤ d 1 := hd0 1
    have h3' : |f 1| ≤ x := by
      rw [hf1]
      exact abs_theta_sub_id_le x (by linarith)
    calc d 1 * f 1 ≤ d 1 * |f 1| := mul_le_mul_of_nonneg_left (le_abs_self _) h1'
      _ ≤ 1 * |f 1| := mul_le_mul_of_nonneg_right hd1 (abs_nonneg _)
      _ = |f 1| := one_mul _
      _ ≤ x := h3'
  have hb2 : -(d ⌊x⌋₊ * f (⌊x⌋₊ + 1)) ≤ x := by
    have hle : d ⌊x⌋₊ ≤ (⌊x⌋₊ : ℝ) := lip_le_self d hd1 hlip _ hM1
    have hdnn : 0 ≤ d ⌊x⌋₊ := hd0 _
    have hz : 0 ≤ x / ((⌊x⌋₊ : ℝ) + 1) := by positivity
    have hE : |f (⌊x⌋₊ + 1)| ≤ x / ((⌊x⌋₊ : ℝ) + 1) := by
      have h := abs_theta_sub_id_le (x / ((⌊x⌋₊ : ℝ) + 1)) hz
      have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) + 1 := by push_cast; ring
      simpa only [hf, hcast] using h
    have habs : |d ⌊x⌋₊ * f (⌊x⌋₊ + 1)| ≤ x := by
      rw [abs_mul, abs_of_nonneg hdnn]
      calc d ⌊x⌋₊ * |f (⌊x⌋₊ + 1)| ≤ (⌊x⌋₊ : ℝ) * (x / ((⌊x⌋₊ : ℝ) + 1)) :=
            mul_le_mul hle hE (abs_nonneg _) (by positivity)
        _ ≤ x := by
            rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < (⌊x⌋₊ : ℝ) + 1)]
            nlinarith
    linarith [neg_le_abs (d ⌊x⌋₊ * f (⌊x⌋₊ + 1)), habs]
  have hb3 : (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, |f n|) ≤ C₀ * x := by
    have := hC₀ x hx
    simpa only [hf] using this
  have hT1 : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, d n * (f n - f (n + 1))) ≤ (C₀ + 2) * x := by
    have h2 : ∀ n ∈ Finset.Icc 2 ⌊x⌋₊, |(d n - d (n - 1)) * f n| ≤ |f n| := by
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hle : |d n - d (n - 1)| ≤ 1 := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simpa using hlip m
      calc |(d n - d (n - 1)) * f n| = |d n - d (n - 1)| * |f n| := abs_mul _ _
        _ ≤ 1 * |f n| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
        _ = |f n| := one_mul _
    have h3 : (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (d n - d (n - 1)) * f n) ≤ C₀ * x := by
      refine (Finset.sum_le_sum fun n _ => le_abs_self _).trans ?_
      exact (Finset.sum_le_sum h2).trans hb3
    rw [habel]
    linarith [hb1, hb2, h3]
  have h3 := hS3 d hd0 hd1 hlip x hx
  calc (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊)
      ≤ _ := hθ
    _ = _ := hsplit
    _ ≤ (x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + x) + (C₀ + 2) * x :=
        add_le_add h3 hT1
    _ = x * (∫ t in (1 : ℝ)..x, d ⌊t⌋₊ / t ^ 2) + (C₀ + 3) * x := by ring

/-- `Kf f x = Σ_{n ≤ x} f n log n` is bounded by the logarithmic average of `‖Mf f t‖`
(Halász identity `f · log = f * Λ_f`, followed by partial summation against `θ(t) = Σ_{p ≤ t} log p`),
with an ABSOLUTE constant. -/
theorem halasz_Kbound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x : ℝ, 2 ≤ x →
        ‖Work.BMF.Kf f x‖ ≤ x * (∫ t in (1 : ℝ)..x, ‖Work.BMF.Mf f t‖ / t ^ 2) + C * x := by
  obtain ⟨C₁, hC₁, hA⟩ := Work.BMF.Kf_primeSum_reduction_abs
  obtain ⟨C₂, hC₂, hB⟩ := primeSum_le_integral_self
  exact halasz_Kbound_of C₁ hC₁ hA C₂ hC₂ hB


end Work.BMF
