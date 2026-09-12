import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.NumberTheory.NumberField

/-- For `n ≠ 0`, `(Nat.log 2 n : ℝ) * log 2 ≤ log n`. -/
private lemma log_two_mul_natLog2_le {n : ℕ} (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have h := Nat.pow_log_le_self 2 hn
  have h' : ((2 : ℕ) ^ Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have h2 : ((2 : ℕ) ^ Nat.log 2 n : ℝ) = (2 : ℝ) ^ Nat.log 2 n := by push_cast; ring
  rw [h2] at h'
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n := by positivity
  have hlog := Real.log_le_log hpos h'
  simpa [Real.log_pow] using hlog

/-- For `n ≠ 0`, `(Nat.log 2 n : ℝ) ≤ (3/2) * log n`. -/
private lemma natLog2_cast_le {n : ℕ} (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) ≤ (3 : ℝ) / 2 * Real.log n := by
  have hmul := log_two_mul_natLog2_le hn
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hk0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have h1 : (Nat.log 2 n : ℝ) * (2 / 3) ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hk0
  have h2 : (Nat.log 2 n : ℝ) * (2 / 3) ≤ Real.log n := le_trans h1 hmul
  calc (Nat.log 2 n : ℝ) = (3 : ℝ) / 2 * ((Nat.log 2 n : ℝ) * (2 / 3)) := by ring
    _ ≤ (3 : ℝ) / 2 * Real.log n := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- `1 ≤ a → 1 ≤ b → 1 ≤ a * b` for reals. -/
private lemma one_le_mul_real {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ a)
  simpa using this

theorem coefficient_bound_estimate (n r : ℕ) (hn : 100 ≤ n) (δ : ℝ) (hδ : 1 ≤ δ)
    (hr4 : r ≤ 2 * (Nat.log 2 n) + 12) :
    ((n : ℝ) * (r + 1) * r * ((r : ℝ) * n * (r + 1) * ((n : ℝ) ^ 2000 * δ ^ 2000) + 1))
      ^ (r + r + 10) ≤ ((n : ℝ) * δ) ^ (10 ^ 7 * Real.log n) := by
  have hn0 : n ≠ 0 := by omega
  have hn100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hδpos : (0 : ℝ) < δ := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log n := by
    have hexp : Real.exp 1 ≤ (n : ℝ) := by
      have := Real.exp_one_lt_three; linarith
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hD0 : (0 : ℝ) ≤ Real.log δ := Real.log_nonneg hδ
  let B : ℝ := (n : ℝ) * (r + 1) * r * ((r : ℝ) * n * (r + 1) * ((n : ℝ) ^ 2000 * δ ^ 2000) + 1)
  change B ^ (r + r + 10) ≤ ((n : ℝ) * δ) ^ (10 ^ 7 * Real.log n)
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- r = 0
    have hB0 : B = 0 := by simp [B, hr0]
    rw [hB0, zero_pow (by omega : r + r + 10 ≠ 0)]
    exact Real.rpow_nonneg (by positivity) _
  · -- r ≥ 1
    have hR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
    have hr_le_3n : (r : ℝ) ≤ 3 * (n : ℝ) := by
      have h1 : r ≤ 2 * n + 12 := by
        have := Nat.log_le_self 2 n; omega
      have h2 : (r : ℝ) ≤ 2 * (n : ℝ) + 12 := by exact_mod_cast h1
      nlinarith [hn100]
    have hA_le : (r : ℝ) + 1 ≤ 4 * (n : ℝ) := by nlinarith [hr_le_3n, hn100]
    have hx1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have hA1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
    have hun : (0 : ℝ) ≤ (n : ℝ) ^ 2000 * δ ^ 2000 := by positivity
    -- inner bound
    have hinner : (r : ℝ) * (n : ℝ) * ((r : ℝ) + 1) * ((n : ℝ) ^ 2000 * δ ^ 2000) + 1
        ≤ 13 * ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2000 * δ ^ 2000)) := by
      have hRxA : (r : ℝ) * (n : ℝ) * ((r : ℝ) + 1) ≤ 12 * (n : ℝ) ^ 3 := by
        calc (r : ℝ) * (n : ℝ) * ((r : ℝ) + 1) ≤ (3 * (n : ℝ)) * (n : ℝ) * (4 * (n : ℝ)) := by
              gcongr
            _ = 12 * (n : ℝ) ^ 3 := by ring
      have h1 : (r : ℝ) * (n : ℝ) * ((r : ℝ) + 1) * ((n : ℝ) ^ 2000 * δ ^ 2000)
          ≤ (12 * (n : ℝ) ^ 3) * ((n : ℝ) ^ 2000 * δ ^ 2000) :=
        mul_le_mul_of_nonneg_right hRxA hun
      have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 3 * ((n : ℝ) ^ 2000 * δ ^ 2000) :=
        one_le_mul_real (one_le_pow₀ hx1) (one_le_mul_real (one_le_pow₀ hx1) (one_le_pow₀ hδ))
      nlinarith [h1, h2]
    have houter : (n : ℝ) * ((r : ℝ) + 1) * (r : ℝ) ≤ 12 * (n : ℝ) ^ 3 := by
      calc (n : ℝ) * ((r : ℝ) + 1) * (r : ℝ) ≤ (n : ℝ) * (4 * (n : ℝ)) * (3 * (n : ℝ)) := by
            gcongr
          _ = 12 * (n : ℝ) ^ 3 := by ring
    have hB_le : B ≤ 156 * (n : ℝ) ^ 2006 * δ ^ 2000 := by
      have hthis : B ≤ (12 * (n : ℝ) ^ 3) * (13 * ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2000 * δ ^ 2000))) := by
        simp only [B]
        exact mul_le_mul houter hinner (by positivity) (by positivity)
      have hkey : (12 * (n : ℝ) ^ 3) * (13 * ((n : ℝ) ^ 3 * ((n : ℝ) ^ 2000 * δ ^ 2000)))
          = 156 * (n : ℝ) ^ 2006 * δ ^ 2000 := by
        have e : (n : ℝ) ^ 2006 = (n : ℝ) ^ 2000 * ((n : ℝ) ^ 3 * (n : ℝ) ^ 3) := by
          rw [show (2006 : ℕ) = 2000 + (3 + 3) by norm_num, pow_add, pow_add]
        rw [e, show (156 : ℝ) = 12 * 13 by norm_num]
        ac_rfl
      rw [hkey] at hthis
      exact hthis
    have hBpos : (0 : ℝ) < B := by positivity
    have hBge1 : (1 : ℝ) ≤ B := by
      have h4 : (1 : ℝ) ≤ (r : ℝ) * (n : ℝ) * ((r : ℝ) + 1) * ((n : ℝ) ^ 2000 * δ ^ 2000) + 1 := by
        have : (0 : ℝ) ≤ (r : ℝ) * (n : ℝ) * ((r : ℝ) + 1) * ((n : ℝ) ^ 2000 * δ ^ 2000) := by positivity
        linarith
      simp only [B]
      exact one_le_mul_real (one_le_mul_real (one_le_mul_real hx1 hA1) hR1) h4
    have hlogB : Real.log B ≤ 155 + 2006 * Real.log n + 2000 * Real.log δ := by
      have hlog_eq : Real.log (156 * (n : ℝ) ^ 2006 * δ ^ 2000)
          = Real.log 156 + 2006 * Real.log n + 2000 * Real.log δ := by
        rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
        norm_num
      have h156 : Real.log 156 ≤ 155 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 156)
        linarith
      calc Real.log B ≤ Real.log (156 * (n : ℝ) ^ 2006 * δ ^ 2000) := Real.log_le_log hBpos hB_le
        _ = Real.log 156 + 2006 * Real.log n + 2000 * Real.log δ := hlog_eq
        _ ≤ 155 + 2006 * Real.log n + 2000 * Real.log δ := by linarith
    have hm : ((r + r + 10 : ℕ) : ℝ) ≤ 6 * Real.log n + 34 := by
      have hlog2 := natLog2_cast_le hn0
      have hrr : (r : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) + 12 := by
        have hccc : (r : ℝ) ≤ (2 * (Nat.log 2 n) + 12 : ℕ) := by exact_mod_cast hr4
        push_cast at hccc ⊢
        linarith
      push_cast
      nlinarith [hlog2, hrr]
    have hstep1 : ((r + r + 10 : ℕ) : ℝ) * Real.log B
        ≤ (6 * Real.log n + 34) * (155 + 2006 * Real.log n + 2000 * Real.log δ) := by
      have h1 : ((r + r + 10 : ℕ) : ℝ) * Real.log B ≤ (6 * Real.log n + 34) * Real.log B :=
        mul_le_mul_of_nonneg_right hm (Real.log_nonneg hBge1)
      have h2 : (6 * Real.log n + 34) * Real.log B
          ≤ (6 * Real.log n + 34) * (155 + 2006 * Real.log n + 2000 * Real.log δ) :=
        mul_le_mul_of_nonneg_left hlogB (by linarith)
      linarith [h1, h2]
    have hnum : (6 * Real.log n + 34) * (155 + 2006 * Real.log n + 2000 * Real.log δ)
        ≤ (10 : ℝ) ^ 7 * Real.log n * (Real.log n + Real.log δ) := by
      nlinarith [hL1, hD0]
    have hlogc : Real.log ((n : ℝ) * δ) = Real.log n + Real.log δ :=
      Real.log_mul (by positivity) (by positivity)
    have hLHS : B ^ (r + r + 10)
        = Real.exp (Real.log B * ((r + r + 10 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hBpos]
    have hRHS : ((n : ℝ) * δ) ^ (10 ^ 7 * Real.log n)
        = Real.exp (Real.log ((n : ℝ) * δ) * ((10 : ℝ) ^ 7 * Real.log n)) := by
      rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n : ℝ) * δ)]
    rw [hLHS, hRHS]
    apply Real.exp_le_exp.mpr
    calc Real.log B * ((r + r + 10 : ℕ) : ℝ)
        = ((r + r + 10 : ℕ) : ℝ) * Real.log B := by ring
      _ ≤ (6 * Real.log n + 34) * (155 + 2006 * Real.log n + 2000 * Real.log δ) := hstep1
      _ ≤ (10 : ℝ) ^ 7 * Real.log n * (Real.log n + Real.log δ) := hnum
      _ = Real.log ((n : ℝ) * δ) * ((10 : ℝ) ^ 7 * Real.log n) := by rw [hlogc]; ring

end Commons.NumberTheory.NumberField