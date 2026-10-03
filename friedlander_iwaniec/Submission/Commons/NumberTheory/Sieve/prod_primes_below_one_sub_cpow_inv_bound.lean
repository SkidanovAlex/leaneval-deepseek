import Mathlib
import Submission.Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog

namespace Commons.NumberTheory.Sieve

open scoped BigOperators

noncomputable section

/-- For `a ≤ 1/2`, `1/(1-a) ≤ exp (a + 2a²)`. -/
private lemma one_div_one_sub_le_exp {a : ℝ} (ha : a ≤ 1/2) :
    1 / (1 - a) ≤ Real.exp (a + 2 * a ^ 2) := by
  have h1a : 0 < 1 - a := by linarith
  have hx : 0 < 1 / (1 - a) := by positivity
  have h1 : Real.log (1 / (1 - a)) ≤ a / (1 - a) := by
    have h := Real.log_le_sub_one_of_pos hx
    have heq : 1 / (1 - a) - 1 = a / (1 - a) := by field_simp; ring
    rw [heq] at h
    exact h
  have h2 : a / (1 - a) ≤ a + 2 * a ^ 2 := by
    rw [div_le_iff₀ h1a]
    nlinarith [sq_nonneg a]
  exact (Real.log_le_iff_le_exp hx).mp (le_trans h1 h2)

/-- For `w : ℂ` with `‖w‖ < 1`, `‖(1 - w)⁻¹‖ ≤ 1/(1 - ‖w‖)`. -/
private lemma norm_inv_one_sub_le (w : ℂ) (hw : ‖w‖ < 1) :
    ‖(1 - w)⁻¹‖ ≤ 1 / (1 - ‖w‖) := by
  have h1 : 0 < 1 - ‖w‖ := by linarith
  have h2 : (1 : ℝ) - ‖w‖ ≤ ‖(1 : ℂ) - w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) w
    simpa using h
  rw [norm_inv, one_div]
  exact inv_anti₀ h1 h2

/-- `‖p ^ (-u)‖ = p ^ (-u.re)` for a positive natural `p`. -/
private lemma norm_natCast_cpow_neg (p : ℕ) (hp : 0 < p) (u : ℂ) :
    ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-u.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp

/-- For a prime `p ≤ z` and `u.re ≥ 1 - 1/log z`, `‖p^(-u)‖ ≤ e/p`. -/
private lemma norm_natCast_cpow_le {p : ℕ} (hp : 2 ≤ p) {z : ℝ} (hz : 3 ≤ z)
    (hpz : (p : ℝ) ≤ z) (u : ℂ) (hσ : 1 - 1 / Real.log z ≤ u.re) :
    ‖(p : ℂ) ^ (-u)‖ ≤ Real.exp 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp0n : 0 < p := by omega
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [norm_natCast_cpow_neg p hp0n]
  have hexp : -u.re ≤ 1 / Real.log z - 1 := by linarith
  have h1 : (p : ℝ) ^ (-u.re) ≤ (p : ℝ) ^ (1 / Real.log z - 1) :=
    Real.rpow_le_rpow_of_exponent_le hp1 hexp
  have h2 : (p : ℝ) ^ (1 / Real.log z - 1) = (p : ℝ) ^ (1 / Real.log z) / (p : ℝ) := by
    rw [show (1 / Real.log z - 1 : ℝ) = 1 / Real.log z + (-1) by ring,
      Real.rpow_add (by positivity), Real.rpow_neg_one]
    ring
  have h3 : (p : ℝ) ^ (1 / Real.log z) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.mpr
    have hlp : Real.log (p : ℝ) ≤ Real.log z := Real.log_le_log hp0 hpz
    have hmul : (1 / Real.log z) * Real.log (p : ℝ) ≤ (1 / Real.log z) * Real.log z :=
      mul_le_mul_of_nonneg_left hlp (by positivity)
    have hzz : (1 / Real.log z) * Real.log z = 1 := by field_simp
    linarith
  calc (p : ℝ) ^ (-u.re) ≤ (p : ℝ) ^ (1 / Real.log z - 1) := h1
    _ = (p : ℝ) ^ (1 / Real.log z) / (p : ℝ) := h2
    _ ≤ Real.exp 1 / (p : ℝ) := by gcongr

/-- For `z ≥ 3` and `u.re ≥ 1 - 1/log z`, `‖2^(-u)‖ ≤ 0.99`. -/
private lemma two_cpow_norm_le {z : ℝ} (hz : 3 ≤ z) (u : ℂ)
    (hσ : 1 - 1 / Real.log z ≤ u.re) :
    ‖(2 : ℂ) ^ (-u)‖ ≤ 0.99 := by
  have hlog3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hlogz : Real.log 3 ≤ Real.log z := Real.log_le_log (by norm_num) hz
  have hlogzpos : 0 < Real.log z := by linarith
  have hinv : 1 / Real.log z ≤ 33 / 34 := by
    rw [div_le_iff₀ hlogzpos]
    nlinarith
  have hexp : -u.re ≤ -(1 / 34 : ℝ) := by linarith
  have h1 : (2 : ℝ) ^ (-u.re) ≤ (2 : ℝ) ^ (-(1 / 34 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have h2 : (2 : ℝ) ^ (-(1 / 34 : ℝ)) ≤ 0.99 := by
    have hnn : 0 ≤ (2 : ℝ) ^ (-(1 / 34 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hpoweq : ((2 : ℝ) ^ (-(1 / 34 : ℝ))) ^ (34 : ℕ) = 1 / 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hle : ((2 : ℝ) ^ (-(1 / 34 : ℝ))) ^ (34 : ℕ) ≤ (0.99 : ℝ) ^ 34 := by
      rw [hpoweq]; norm_num
    exact (pow_le_pow_iff_left₀ hnn (by norm_num) (by norm_num : (34 : ℕ) ≠ 0)).mp hle
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, norm_natCast_cpow_neg 2 (by norm_num)]
  linarith

/-- Factor bound for large primes `p ≥ 7`: when `‖p^(-u)‖ ≤ e/p ≤ 1/2`,
`‖(1 - p^(-u))⁻¹‖ ≤ exp (e/p + 2e²/p²)`. -/
private lemma factor_le_exp {p : ℕ} (hp : 7 ≤ p) {u : ℂ}
    (hw : ‖(p : ℂ) ^ (-u)‖ ≤ Real.exp 1 / (p : ℝ)) :
    ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ ≤
      Real.exp (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1) ^ 2 / (p : ℝ) ^ 2) := by
  have hp7 : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hEp : Real.exp 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hp0]; nlinarith [Real.exp_one_lt_three]
  have ha : ‖(p : ℂ) ^ (-u)‖ ≤ 1 / 2 := le_trans hw hEp
  have hsq : ‖(p : ℂ) ^ (-u)‖ ^ 2 ≤ (Real.exp 1 / (p : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hw 2
  calc ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ ≤ 1 / (1 - ‖(p : ℂ) ^ (-u)‖) :=
        norm_inv_one_sub_le _ (by linarith)
    _ ≤ Real.exp (‖(p : ℂ) ^ (-u)‖ + 2 * ‖(p : ℂ) ^ (-u)‖ ^ 2) :=
        one_div_one_sub_le_exp ha
    _ ≤ Real.exp (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1 / (p : ℝ)) ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [hw, hsq, norm_nonneg ((p : ℂ) ^ (-u))])
    _ = Real.exp (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1) ^ 2 / (p : ℝ) ^ 2) := by
        congr 1
        field_simp

/-- Factor bound for the small primes: `‖(1 - p^(-u))⁻¹‖ ≤ 100` for `p = 2` and
`≤ 12` for `p ∈ {3,5}`. -/
private lemma factor_small_le {p : ℕ} (hp2 : 2 ≤ p) (hp5 : p ≤ 5) (hpp : p.Prime)
    {z : ℝ} (hz : 3 ≤ z) (hpz : (p : ℝ) ≤ z) (u : ℂ)
    (hσ : 1 - 1 / Real.log z ≤ u.re) :
    ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ ≤ (if p = 2 then 100 else 12) := by
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl]
    have hw : ‖(2 : ℂ) ^ (-u)‖ ≤ 0.99 := two_cpow_norm_le hz u hσ
    have h1 : ‖(1 - (2 : ℂ) ^ (-u))⁻¹‖ ≤ 1 / (1 - ‖(2 : ℂ) ^ (-u)‖) :=
      norm_inv_one_sub_le _ (by linarith)
    have h2' : 1 / (1 - ‖(2 : ℂ) ^ (-u)‖) ≤ 100 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  · rw [if_neg h2]
    have hp3 : 3 ≤ p := by omega
    have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
    have hw : ‖(p : ℂ) ^ (-u)‖ ≤ Real.exp 1 / (p : ℝ) :=
      norm_natCast_cpow_le hp2 hz hpz u hσ
    have hw1 : ‖(p : ℂ) ^ (-u)‖ ≤ Real.exp 1 / 3 := by
      have hle : Real.exp 1 / (p : ℝ) ≤ Real.exp 1 / 3 :=
        div_le_div_of_nonneg_left (Real.exp_pos 1).le (by norm_num) hp3r
      linarith
    have hE : Real.exp 1 / 3 ≤ 11 / 12 := by
      have h := Real.exp_one_lt_d9
      nlinarith
    have h1 : ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ ≤ 1 / (1 - ‖(p : ℂ) ^ (-u)‖) :=
      norm_inv_one_sub_le _ (by linarith)
    have h2' : 1 / (1 - ‖(p : ℂ) ^ (-u)‖) ≤ 1 / (1 - Real.exp 1 / 3) := by
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    have h3 : 1 / (1 - Real.exp 1 / 3) ≤ 12 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith

/-- **Bound for the truncated Euler product just left of the line `Re s = 1`.**

For every `z ≥ 3` and every `u : ℂ` with `Re u ≥ 1 - 1/log z` (and `Re u ≤ 2`),
`∏_{p < ⌈z⌉} (1 - p^{-u})⁻¹ = O((log z)^3)`, uniformly in `u`.

Route.  For a prime `p ≤ z` we have `‖p^{-u}‖ = p^{-Re u} ≤ p^{1/log z - 1} = p^{-1}·p^{1/log z} ≤ e/p`
because `p ≤ z` gives `log p ≤ log z`.  So `‖(1 - p^{-u})⁻¹‖ ≤ 1/(1 - ‖p^{-u}‖)`.

* For `p ≥ 7` we have `‖p^{-u}‖ ≤ e/p ≤ 3/7 < 1/2`, hence `-log(1 - a) ≤ a + 2a²` gives
  `‖(1 - p^{-u})⁻¹‖ ≤ exp(e/p + 2e²/p²)`.
* The primes `2, 3, 5` contribute the absolute constant `100·12·12`.

Multiplying and taking logarithms gives
`log (∏ ‖·‖) ≤ e·Σ_{p<z} 1/p + 2e²·Σ_{p<z} 1/p² ≤ e·(log log z + O(1)) + O(1)`, using the
Euler–Mertens bound `Σ_{p<z} 1/p ≤ log log z + C` and `Σ_{p<z} 1/p² ≤ 1`.  Since the exponent
`e < 3`, this is `≤ O(1)·(log z)^3`. -/
theorem prod_primes_below_one_sub_cpow_inv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 3 ≤ z → ∀ u : ℂ,
      1 - 1 / Real.log z ≤ u.re → u.re ≤ 2 →
        ‖∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u))⁻¹‖ ≤
          C * (Real.log z) ^ 3 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog
  refine ⟨14400 * 8 * Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2), ?_, ?_⟩
  · positivity
  intro z hz u hσ _
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogz1 : 1 ≤ Real.log z := by
    have h3 : Real.log 3 ≤ Real.log z := Real.log_le_log (by norm_num) hz
    linarith [Real.log_three_gt_d9, h3]
  have hN2 : 2 ≤ ⌈z⌉₊ := by
    have h : (2 : ℝ) ≤ ((⌈z⌉₊ : ℕ) : ℝ) := by
      have hle := Nat.le_ceil z
      linarith
    exact_mod_cast h
  have hple : ∀ p ∈ Nat.primesBelow ⌈z⌉₊, (p : ℝ) ≤ z := by
    intro p hp
    have hpc : p < ⌈z⌉₊ := Nat.lt_of_mem_primesBelow hp
    by_contra hcon
    rw [not_le] at hcon
    have hce : ⌈z⌉₊ ≤ p := Nat.ceil_le.mpr (le_of_lt hcon)
    omega
  have hnormprod : ‖∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u))⁻¹‖
      = ∏ p ∈ Nat.primesBelow ⌈z⌉₊, ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ := norm_prod _ _
  -- the small-prime part
  have hsmall : ∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => p ≤ 5),
        ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ ≤ 14400 := by
    have hsub : (Nat.primesBelow ⌈z⌉₊).filter (fun p => p ≤ 5) ⊆ ({2, 3, 5} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hp5⟩ := hp
      have hpp : p.Prime := Nat.prime_of_mem_primesBelow hpS
      have hp2 : 2 ≤ p := hpp.two_le
      interval_cases p
      · simp
      · simp
      · exact absurd hpp (by norm_num [Nat.Prime])
      · simp
    have hfac : ∀ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => p ≤ 5),
        ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ ≤ (if p = 2 then 100 else 12) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hp5⟩ := hp
      exact factor_small_le (Nat.two_le_of_mem_primesBelow hpS) hp5
        (Nat.prime_of_mem_primesBelow hpS) hz (hple p hpS) u hσ
    calc ∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => p ≤ 5), ‖(1 - (p : ℂ) ^ (-u))⁻¹‖
        ≤ ∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => p ≤ 5),
            (if p = 2 then 100 else 12) :=
          Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) hfac
      _ ≤ ∏ p ∈ ({2, 3, 5} : Finset ℕ), (if p = 2 then 100 else 12) :=
          Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun x _ => by positivity)
            (by intro x hx _; fin_cases hx <;> norm_num)
      _ = 14400 := by norm_num [Finset.prod_insert]
  -- the large-prime part
  have hlarge : ∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => ¬ p ≤ 5),
        ‖(1 - (p : ℂ) ^ (-u))⁻¹‖
      ≤ Real.exp (Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
          + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2)) := by
    have hfac : ∀ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => ¬ p ≤ 5),
        ‖(1 - (p : ℂ) ^ (-u))⁻¹‖
          ≤ Real.exp (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1) ^ 2 / (p : ℝ) ^ 2) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hp5⟩ := hp
      have hpp : p.Prime := Nat.prime_of_mem_primesBelow hpS
      have hp2 : 2 ≤ p := hpp.two_le
      have hp7 : 7 ≤ p := by
        have h6 : 6 ≤ p := by omega
        rcases eq_or_lt_of_le h6 with h | h
        · rw [← h] at hpp; norm_num [Nat.Prime] at hpp
        · omega
      exact factor_le_exp hp7 (norm_natCast_cpow_le hp2 hz (hple p hpS) u hσ)
    calc ∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => ¬ p ≤ 5),
            ‖(1 - (p : ℂ) ^ (-u))⁻¹‖
        ≤ ∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => ¬ p ≤ 5),
            Real.exp (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1) ^ 2 / (p : ℝ) ^ 2) :=
          Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) hfac
      _ = Real.exp (∑ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => ¬ p ≤ 5),
            (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1) ^ 2 / (p : ℝ) ^ 2)) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
          + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          calc ∑ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => ¬ p ≤ 5),
                (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1) ^ 2 / (p : ℝ) ^ 2)
              ≤ ∑ p ∈ Nat.primesBelow ⌈z⌉₊,
                (Real.exp 1 / (p : ℝ) + 2 * (Real.exp 1) ^ 2 / (p : ℝ) ^ 2) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun p _ _ => by positivity)
            _ = Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
                + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
                congr 1
                · exact Finset.sum_congr rfl (fun p _ => by rw [div_eq_mul_inv, one_div])
                · exact Finset.sum_congr rfl (fun p _ => by rw [div_eq_mul_inv, one_div])
  -- the harmonic-sum and squared-reciprocal bounds
  have hM : (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
      ≤ Real.log (Real.log ((⌈z⌉₊ : ℕ) : ℝ)) + C₀ := hC₀ ⌈z⌉₊ hN2
  have hSq : (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2) ≤ 1 := by
    have hsub : Nat.primesBelow ⌈z⌉₊ ⊆ Finset.Ioo 1 ⌈z⌉₊ := by
      intro p hp
      have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
      have hpN : p < ⌈z⌉₊ := Nat.lt_of_mem_primesBelow hp
      exact Finset.mem_Ioo.mpr ⟨by omega, hpN⟩
    calc ∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Ioo 1 ⌈z⌉₊, 1 / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      _ = ∑ n ∈ Finset.Ioo 1 ⌈z⌉₊, (((n : ℝ)) ^ 2)⁻¹ := by
          exact Finset.sum_congr rfl (fun n _ => by rw [one_div])
      _ ≤ 2 / (((1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le 1 ⌈z⌉₊
      _ = 1 := by norm_num
  have hceil : ((⌈z⌉₊ : ℕ) : ℝ) < z + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlogN : Real.log ((⌈z⌉₊ : ℕ) : ℝ) ≤ 2 * Real.log z := by
    have hp : (0 : ℝ) < ((⌈z⌉₊ : ℕ) : ℝ) := by positivity
    have h1 : Real.log ((⌈z⌉₊ : ℕ) : ℝ) ≤ Real.log (z + 1) :=
      Real.log_le_log hp (le_of_lt hceil)
    have h2 : Real.log (z + 1) ≤ Real.log (2 * z) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (2 * z) = Real.log 2 + Real.log z :=
      Real.log_mul (by norm_num) (ne_of_gt (by linarith))
    have h4 : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hllog : Real.log (Real.log ((⌈z⌉₊ : ℕ) : ℝ)) ≤ Real.log 2 + Real.log (Real.log z) := by
    have hpos : 0 < Real.log ((⌈z⌉₊ : ℕ) : ℝ) := by
      have h1 : Real.log 1 < Real.log ((⌈z⌉₊ : ℕ) : ℝ) := by
        apply Real.log_lt_log (by norm_num)
        have : (1 : ℝ) < ((⌈z⌉₊ : ℕ) : ℝ) := by
          have h2 : (2 : ℕ) ≤ ⌈z⌉₊ := hN2
          exact_mod_cast (by omega : 1 < ⌈z⌉₊)
        exact this
      simpa using h1
    have h1 : Real.log (Real.log ((⌈z⌉₊ : ℕ) : ℝ)) ≤ Real.log (2 * Real.log z) :=
      Real.log_le_log hpos hlogN
    have h2 : Real.log (2 * Real.log z) = Real.log 2 + Real.log (Real.log z) :=
      Real.log_mul (by norm_num) (ne_of_gt hlogz)
    linarith
  -- put the exponential bound together
  have hexp : Real.exp (Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
        + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2))
      ≤ Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2) * (8 * (Real.log z) ^ 3) := by
    have hE1 : 0 < Real.exp 1 := Real.exp_pos 1
    have hA : Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
        + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2)
        ≤ Real.exp 1 * Real.log 2 + Real.exp 1 * Real.log (Real.log z)
          + (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2) := by
      have h1 : Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
          ≤ Real.exp 1 * (Real.log (Real.log ((⌈z⌉₊ : ℕ) : ℝ)) + C₀) :=
        mul_le_mul_of_nonneg_left hM hE1.le
      have h2 : 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2)
          ≤ 2 * (Real.exp 1) ^ 2 := by
        have h2pos : 0 ≤ 2 * (Real.exp 1) ^ 2 := by positivity
        nlinarith [hSq, h2pos]
      nlinarith [h1, h2, hllog, hE1]
    have hE3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    have h2E : (2 : ℝ) ^ (Real.exp 1) ≤ 8 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hE3
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
      norm_num at h
      exact h
    have hlogE : (Real.log z) ^ (Real.exp 1) ≤ (Real.log z) ^ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le hlogz1 hE3
      rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have hexpand : Real.exp (Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
          + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2))
        ≤ Real.exp (Real.exp 1 * Real.log 2 + Real.exp 1 * Real.log (Real.log z)
          + (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2)) :=
      Real.exp_le_exp.mpr hA
    have hsplit : Real.exp (Real.exp 1 * Real.log 2 + Real.exp 1 * Real.log (Real.log z)
          + (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2))
        = (2 : ℝ) ^ (Real.exp 1) * (Real.log z) ^ (Real.exp 1)
          * Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2) := by
      have h2r : (2 : ℝ) ^ (Real.exp 1) = Real.exp (Real.exp 1 * Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (Real.exp 1), mul_comm]
      have hlogr : (Real.log z) ^ (Real.exp 1)
          = Real.exp (Real.exp 1 * Real.log (Real.log z)) := by
        rw [Real.rpow_def_of_pos hlogz (Real.exp 1), mul_comm]
      rw [Real.exp_add, Real.exp_add, ← h2r, ← hlogr]
    have hmono : (2 : ℝ) ^ (Real.exp 1) * (Real.log z) ^ (Real.exp 1)
        ≤ 8 * (Real.log z) ^ 3 :=
      mul_le_mul h2E hlogE (Real.rpow_nonneg hlogz.le (Real.exp 1)) (by norm_num)
    calc Real.exp (Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
          + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2))
        ≤ Real.exp (Real.exp 1 * Real.log 2 + Real.exp 1 * Real.log (Real.log z)
          + (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2)) := hexpand
      _ = (2 : ℝ) ^ (Real.exp 1) * (Real.log z) ^ (Real.exp 1)
          * Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2) := hsplit
      _ ≤ (8 * (Real.log z) ^ 3) * Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
      _ = Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2) * (8 * (Real.log z) ^ 3) := by
          ring
  calc ‖∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u))⁻¹‖
      = ∏ p ∈ Nat.primesBelow ⌈z⌉₊, ‖(1 - (p : ℂ) ^ (-u))⁻¹‖ := hnormprod
    _ = (∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => p ≤ 5),
            ‖(1 - (p : ℂ) ^ (-u))⁻¹‖)
        * (∏ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => ¬ p ≤ 5),
            ‖(1 - (p : ℂ) ^ (-u))⁻¹‖) := by
        rw [Finset.prod_filter_mul_prod_filter_not]
    _ ≤ 14400 * Real.exp (Real.exp 1 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ))
          + 2 * (Real.exp 1) ^ 2 * (∑ p ∈ Nat.primesBelow ⌈z⌉₊, 1 / (p : ℝ) ^ 2)) :=
        mul_le_mul hsmall hlarge (by positivity) (by norm_num)
    _ ≤ 14400 * (Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2)
          * (8 * (Real.log z) ^ 3)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = (14400 * 8 * Real.exp (Real.exp 1 * C₀ + 2 * (Real.exp 1) ^ 2)) * (Real.log z) ^ 3 := by
        ring

end

end Commons.NumberTheory.Sieve
