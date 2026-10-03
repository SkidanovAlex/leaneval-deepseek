import Mathlib
import Submission.Work.FIArea6Road.sum_tau_sq_window_le
import Submission.Work.FITop.Defs

namespace Work.FIArea6.TauCore

/-- The window sum of `τ(n)²` over `(N, (1+θ)N]` is bounded by the uniform window bound for
`[a,b]`, at the cost of the factors `8` and `4` coming from `b - a + 1 ≤ θN + 1` and
`log(b+2) ≤ 2 log N` (the latter because `N ≥ 3` gives `b + 2 ≤ N²`). -/
theorem tau_window_tau_sq_le
    (C0 : ℝ) (hC0 : 0 < C0)
    (hC0b : ∀ a b : ℕ, a ≤ b →
      ∑ n ∈ Finset.Icc a b, ((n.divisors.card : ℝ)) ^ 2
        ≤ C0 * ((b : ℝ) - (a : ℝ) + 1) * (Real.log ((b : ℝ) + 2)) ^ (3 : ℕ)
          + C0 * (b : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((b : ℝ) + 2)) ^ (2 : ℕ))
    (Pa : Work.FITop.Params)
    (hN1 : 1 ≤ Pa.N) (hN3 : 3 ≤ Pa.N) (hθ0 : 0 < Pa.θ) (hθ1 : Pa.θ < 1) :
    ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊, ((n.divisors.card : ℝ)) ^ 2
      ≤ 8 * C0 * (Pa.θ * Pa.N + 1) * (Real.log Pa.N) ^ (3 : ℕ)
        + 4 * C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log Pa.N) ^ (2 : ℕ) := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hNle : (0 : ℝ) ≤ Pa.N := le_of_lt hNpos
  have hθ0le : (0 : ℝ) ≤ Pa.θ := le_of_lt hθ0
  have hlogN0 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hfacA : (0 : ℝ) ≤ Pa.θ * Pa.N + 1 := by
    have : (0 : ℝ) ≤ Pa.θ * Pa.N := mul_nonneg hθ0le hNle
    linarith
  by_cases hab : ⌊Pa.N⌋₊ + 1 ≤ ⌊(1 + Pa.θ) * Pa.N⌋₊
  · have hbound := hC0b (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊ hab
    -- the floor of the right end, as a real, is ≤ (1+θ)N
    have hbM : ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N :=
      Nat.floor_le (mul_nonneg (by linarith) hNle)
    -- the left end, as a real, is > N
    have haM : Pa.N < (((⌊Pa.N⌋₊ + 1 : ℕ)) : ℝ) := by
      have h := Nat.lt_floor_add_one (R := ℝ) Pa.N
      simpa using h
    -- number of terms bound
    have hA :
        ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) - (((⌊Pa.N⌋₊ + 1 : ℕ)) : ℝ) + 1
          ≤ Pa.θ * Pa.N + 1 := by
      linarith
    -- the right end is at most 2N
    have hb2N : ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) ≤ 2 * Pa.N := by
      have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [hθ1, hNpos]
      linarith
    -- b + 2 ≤ N²
    have hb2 : ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2 ≤ Pa.N * Pa.N := by
      have hfac : (0 : ℝ) ≤ (Pa.N - 3) * (Pa.N + 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hfac, hb2N]
    have hlogb : Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2) ≤ 2 * Real.log Pa.N := by
      have hpos : (0 : ℝ) < ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2 := by
        have : (0 : ℝ) ≤ ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have h := Real.log_le_log hpos hb2
      have hmul : Real.log (Pa.N * Pa.N) = 2 * Real.log Pa.N := by
        rw [Real.log_mul (ne_of_gt hNpos) (ne_of_gt hNpos)]
        ring
      linarith [h, hmul]
    have hlogb0 : (0 : ℝ) ≤ Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hlogpow3 :
        (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ)
          ≤ 8 * (Real.log Pa.N) ^ (3 : ℕ) := by
      calc (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ)
          ≤ (2 * Real.log Pa.N) ^ (3 : ℕ) := pow_le_pow_left₀ hlogb0 hlogb 3
        _ = 8 * (Real.log Pa.N) ^ (3 : ℕ) := by ring
    have hlogpow2 :
        (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ)
          ≤ 4 * (Real.log Pa.N) ^ (2 : ℕ) := by
      calc (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ)
          ≤ (2 * Real.log Pa.N) ^ (2 : ℕ) := pow_le_pow_left₀ hlogb0 hlogb 2
        _ = 4 * (Real.log Pa.N) ^ (2 : ℕ) := by ring
    have hbpow :
        ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) ^ ((3 : ℝ) / 4)
          ≤ (2 * Pa.N) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hb2N (by norm_num)
    -- first term
    have hT1 :
        C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) - (((⌊Pa.N⌋₊ + 1 : ℕ)) : ℝ) + 1)
            * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ)
          ≤ 8 * C0 * (Pa.θ * Pa.N + 1) * (Real.log Pa.N) ^ (3 : ℕ) := by
      have h1 :
          C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) - (((⌊Pa.N⌋₊ + 1 : ℕ)) : ℝ) + 1)
            ≤ C0 * (Pa.θ * Pa.N + 1) := mul_le_mul_of_nonneg_left hA hC0.le
      have h2 :
          C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) - (((⌊Pa.N⌋₊ + 1 : ℕ)) : ℝ) + 1)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ)
            ≤ C0 * (Pa.θ * Pa.N + 1)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hlogb0 3)
      have h3 :
          C0 * (Pa.θ * Pa.N + 1)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ)
            ≤ C0 * (Pa.θ * Pa.N + 1) * (8 * (Real.log Pa.N) ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left hlogpow3 (mul_nonneg hC0.le hfacA)
      calc
        C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) - (((⌊Pa.N⌋₊ + 1 : ℕ)) : ℝ) + 1)
            * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ)
            ≤ C0 * (Pa.θ * Pa.N + 1)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ) := h2
        _ ≤ C0 * (Pa.θ * Pa.N + 1) * (8 * (Real.log Pa.N) ^ (3 : ℕ)) := h3
        _ = 8 * C0 * (Pa.θ * Pa.N + 1) * (Real.log Pa.N) ^ (3 : ℕ) := by ring
    -- second term
    have hT2 :
        C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
            * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ)
          ≤ 4 * C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log Pa.N) ^ (2 : ℕ) := by
      have h1 :
          C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
            ≤ C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_left hbpow hC0.le
      have h2 :
          C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ)
            ≤ C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hlogb0 2)
      have h3 :
          C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ)
            ≤ C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (4 * (Real.log Pa.N) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hlogpow2
          (mul_nonneg hC0.le (Real.rpow_nonneg (by linarith) ((3 : ℝ) / 4)))
      calc
        C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
            * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ)
            ≤ C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ) := h2
        _ ≤ C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (4 * (Real.log Pa.N) ^ (2 : ℕ)) := h3
        _ = 4 * C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log Pa.N) ^ (2 : ℕ) := by ring
    calc
      ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊, ((n.divisors.card : ℝ)) ^ 2
          ≤ C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) - (((⌊Pa.N⌋₊ + 1 : ℕ)) : ℝ) + 1)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (3 : ℕ)
            + C0 * (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
              * (Real.log (((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 2)) ^ (2 : ℕ) := hbound
      _ ≤ 8 * C0 * (Pa.θ * Pa.N + 1) * (Real.log Pa.N) ^ (3 : ℕ)
            + 4 * C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log Pa.N) ^ (2 : ℕ) :=
          add_le_add hT1 hT2
  · have hempty : Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊ = ∅ :=
      Finset.Icc_eq_empty_iff.mpr hab
    rw [hempty, Finset.sum_empty]
    have h1 : (0 : ℝ) ≤ 8 * C0 * (Pa.θ * Pa.N + 1) * (Real.log Pa.N) ^ (3 : ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0.le) hfacA) (pow_nonneg hlogN0 3)
    have h2 : (0 : ℝ) ≤ 4 * C0 * (2 * Pa.N) ^ ((3 : ℝ) / 4) * (Real.log Pa.N) ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0.le)
        (Real.rpow_nonneg (by linarith) ((3 : ℝ) / 4))) (pow_nonneg hlogN0 2)
    linarith

end Work.FIArea6.TauCore
