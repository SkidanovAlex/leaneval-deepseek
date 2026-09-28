import Mathlib

namespace Work.ClassCount

/-- The key term-wise comparison: for `a ≥ 1` and `n ≥ 1`,
`(1/(a+1))^(n+1) ≤ (1/n) * ((1/a)^n - (1/(a+1))^n)`,
which exhibits the summand as (essentially) the tail of a telescoping series. -/
lemma key_term (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 1 ≤ a) :
    (1 / (a + 1)) ^ (n + 1) ≤ (1 / (n : ℝ)) * ((1 / a) ^ n - (1 / (a + 1)) ^ n) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hbern : 1 + (n:ℝ) * (1/a) ≤ (1 + 1/a)^n := by
    have hb : (-2:ℝ) ≤ (1:ℝ)/a := by
      have : (0:ℝ) ≤ (1:ℝ)/a := by positivity
      linarith
    have h := one_add_mul_le_pow (R := ℝ) (a := (1:ℝ)/a) hb n
    simpa using h
  have hfac : a * (1 + 1/a) = a + 1 := by field_simp
  have h3 : a^n * (1/a) = a^(n-1) := by
    rw [one_div, pow_sub₀ a ha0.ne' hn, pow_one]
  have hmain : a^n + (n:ℝ) * a^(n-1) ≤ (a+1)^n := by
    have h2 : a^n * (1 + (n:ℝ)*(1/a)) ≤ a^n * (1 + 1/a)^n :=
      mul_le_mul_of_nonneg_left hbern (by positivity)
    have h4 : a^n * (1 + (n:ℝ)*(1/a)) = a^n + (n:ℝ)*a^(n-1) := by
      have hm : a^n * ((n:ℝ) * (1/a)) = (n:ℝ) * (a^n * (1/a)) := by ring
      rw [mul_add, mul_one, hm, h3]
    calc a^n + (n:ℝ)*a^(n-1)
        = a^n * (1 + (n:ℝ)*(1/a)) := h4.symm
      _ ≤ a^n * (1+1/a)^n := h2
      _ = (a+1)^n := by rw [← mul_pow, hfac]
  have hcore : (n:ℝ) * a^n ≤ (a+1) * ((a+1)^n - a^n) := by
    have hpow : a^(n-1) * a = a^n := by
      rw [← pow_succ a (n-1), Nat.sub_add_cancel hn]
    have h5 : (n:ℝ) * a^n ≤ (a+1) * ((n:ℝ) * a^(n-1)) := by
      nlinarith [hpow, ha0, pow_nonneg (le_of_lt ha0) (n-1), hn0]
    have h6 : (a+1) * ((n:ℝ) * a^(n-1)) ≤ (a+1) * ((a+1)^n - a^n) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith [hmain]
    linarith [h5, h6]
  rw [one_div_pow (a+1) (n+1), one_div_pow a n, one_div_pow (a+1) n]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (a+1)^(n+1)), pow_succ]
  have hAn : (a:ℝ)^n ≠ 0 := by positivity
  have hBn : ((a+1):ℝ)^n ≠ 0 := by positivity
  have hnn : (n:ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hcore]

theorem harmonic_tail_inv_pow (K N n : ℕ) (hK : 1 ≤ K) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc (K + 1) N, ((1 : ℝ) / (k : ℝ)) ^ (n + 1)
      ≤ (1 / (K : ℝ)) ^ n / (n : ℝ) := by
  have aux : ∀ N, K ≤ N →
      ∑ k ∈ Finset.Icc (K + 1) N, ((1 : ℝ) / (k : ℝ)) ^ (n + 1)
        ≤ (1 / (n : ℝ)) * ((1 / (K : ℝ)) ^ n - (1 / (N : ℝ)) ^ n) := by
    intro N hKN
    induction N, hKN using Nat.le_induction with
    | base =>
      rw [Finset.Icc_eq_empty (by omega : ¬ K + 1 ≤ K)]
      simp
    | succ N hKN ih =>
      rw [Finset.sum_Icc_succ_top (by omega : K + 1 ≤ N + 1)]
      simp only [Nat.cast_add, Nat.cast_one]
      have hN1 : (1 : ℕ) ≤ N := le_trans hK hKN
      have hkey := key_term n hn (N : ℝ) (by exact_mod_cast hN1)
      calc (∑ k ∈ Finset.Icc (K + 1) N, ((1 : ℝ) / (k : ℝ)) ^ (n + 1))
              + (1 / ((N : ℝ) + 1)) ^ (n + 1)
          ≤ (1 / (n : ℝ)) * ((1 / (K : ℝ)) ^ n - (1 / (N : ℝ)) ^ n)
              + (1 / (n : ℝ)) * ((1 / (N : ℝ)) ^ n - (1 / ((N : ℝ) + 1)) ^ n) :=
            add_le_add ih hkey
        _ = (1 / (n : ℝ)) * ((1 / (K : ℝ)) ^ n - (1 / ((N : ℝ) + 1)) ^ n) := by ring
  rcases lt_or_ge K N with hKN | hNK
  · have h1 := aux N (le_of_lt hKN)
    refine le_trans h1 ?_
    have h2 : (0:ℝ) ≤ (1 / (N : ℝ)) ^ n := by positivity
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have h3 : (0:ℝ) ≤ (1 : ℝ) / (n : ℝ) := div_nonneg zero_le_one (le_of_lt hnpos)
    calc (1 / (n : ℝ)) * ((1 / (K : ℝ)) ^ n - (1 / (N : ℝ)) ^ n)
        ≤ (1 / (n : ℝ)) * ((1 / (K : ℝ)) ^ n - 0) := by
          apply mul_le_mul_of_nonneg_left _ h3
          linarith
      _ = (1 / (K : ℝ)) ^ n / (n : ℝ) := by ring
  · rw [Finset.Icc_eq_empty (by omega : ¬ K + 1 ≤ N)]
    simp only [Finset.sum_empty]
    positivity

end Work.ClassCount
