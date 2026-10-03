import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_eq_prod_factorization
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_le_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_eq_one
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_two_pow_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The average of the number of square roots of `-1` modulo `d`

We bound the Dirichlet-series average
`∑_{d ≤ x} ρ(d) / d`, where `ρ(d)` is the number of solutions of `α ^ 2 = -1` in
`ZMod d`, by a power of `log x`.

The two ingredients are

* `ρ(d) ≤ τ(d)` (the number of square roots of `-1` modulo `d` is at most the
  number of divisors of `d`), obtained from `ρ(d) = ∏_{p ∣ d} ρ(p ^ v_p(d))` and
  the fact that each factor is at most `2`; and
* the elementary bound `∑_{d ≤ x} τ(d) / d ≤ (1 + log x) ^ 2`.
-/

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The number of square roots of `-1` in `ZMod (p ^ e)`, for a prime `p` and
`e ≥ 1`, is at most `2`: there are two (resp. no) solutions for odd `p`, one for
`2 ^ 1`, and none for `2 ^ e` with `e ≥ 2`. -/
lemma ncard_sq_roots_neg_one_prime_pow_le_two {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    ({α : ZMod (p ^ e) | α ^ 2 = -1}.ncard) ≤ 2 := by
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    rcases eq_or_lt_of_le he with h1 | hgt
    · subst h1
      have h1' : ({α : ZMod (2 ^ 1) | α ^ 2 = -1}.ncard) = 1 := by
        rw [pow_one]; exact sq_roots_neg_one_mod_two_eq_one
      rw [h1']; norm_num
    · have hz : ({α : ZMod (2 ^ e) | α ^ 2 = -1}.ncard) = 0 :=
        sq_roots_neg_one_mod_two_pow_eq_zero (show 2 ≤ e by omega)
      rw [hz]; norm_num
  · have hpodd : p ≠ 2 := by
      intro h
      rw [h] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
    exact sq_roots_neg_one_mod_prime_pow_le_two hp hpodd he

/-- The number of square roots of `-1` modulo `d` is at most the number of
divisors of `d`.  Indeed it equals the product over the primes `p ∣ d` of the
number of roots modulo `p ^ v_p(d)`, and each factor is at most `2 ≤ v_p(d) + 1`. -/
lemma rho_le_divisor_count {d : ℕ} (hd : 1 ≤ d) :
    ({α : ZMod d | α ^ 2 = -1}.ncard) ≤ (Nat.divisors d).card := by
  have hd0 : d ≠ 0 := by omega
  have hpos : 0 < d := by omega
  rw [sq_roots_neg_one_eq_prod_factorization hpos, Nat.card_divisors hd0]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfac : 1 ≤ d.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hpp hd0 (Nat.dvd_of_mem_primeFactors hp)
    calc ({α : ZMod (p ^ d.factorization p) | α ^ 2 = -1}.ncard)
        ≤ 2 := ncard_sq_roots_neg_one_prime_pow_le_two hpp hfac
      _ ≤ d.factorization p + 1 := by omega

/-- The elementary summatory bound for the divisor-counting function
`τ(d) = (Nat.divisors d).card`: for `x ≥ 1`,
`∑_{d ≤ x} τ(d) / d ≤ (1 + log x) ^ 2`.

Double counting the pairs `(e, m)` with `e * m = d ≤ x` gives
`∑_{d ≤ x} τ(d)/d = ∑_{e ≤ x} (1/e) ∑_{m ≤ x/e} 1/m`, and the harmonic bound
`H_n ≤ 1 + log n` bounds the inner sums by `1 + log x`. -/
lemma sum_divisor_count_div_le (x : ℕ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 x, ((Nat.divisors d).card : ℝ) / (d : ℝ)) ≤ (1 + Real.log x) ^ 2 := by
  classical
  set s : Finset (Sigma (fun _ : ℕ => ℕ)) := (Finset.Icc 1 x).sigma (fun d => Nat.divisors d) with hs
  set t : Finset (Sigma (fun _ : ℕ => ℕ)) := (Finset.Icc 1 x).sigma (fun e => Finset.Icc 1 (x / e)) with ht
  -- Step 1: expand `τ(d)` as the cardinality of the divisor set and pass to a sigma-sum.
  have step1 : (∑ d ∈ Finset.Icc 1 x, ((Nat.divisors d).card : ℝ) / (d : ℝ))
      = ∑ σ ∈ s, (1 : ℝ) / (σ.1 : ℝ) := by
    have h1 : (∑ d ∈ Finset.Icc 1 x, ((Nat.divisors d).card : ℝ) / (d : ℝ))
        = ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Nat.divisors d, (1 : ℝ) / (d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_div]
      congr 1
      simp
    rw [h1, hs]
    exact (Finset.sum_sigma (Finset.Icc 1 x) (fun d => Nat.divisors d)
      (fun σ : Sigma (fun _ : ℕ => ℕ) => (1 : ℝ) / (σ.1 : ℝ))).symm
  -- Step 2: reindex the sigma-sum along the bijection `(d, e) ↦ (e, d / e)`.
  have step2 : (∑ σ ∈ s, (1 : ℝ) / (σ.1 : ℝ))
      = ∑ τ ∈ t, (1 : ℝ) / ((τ.1 : ℝ) * (τ.2 : ℝ)) := by
    refine Finset.sum_nbij' (fun σ => (⟨σ.2, σ.1 / σ.2⟩ : Sigma (fun _ : ℕ => ℕ)))
      (fun τ => (⟨τ.1 * τ.2, τ.1⟩ : Sigma (fun _ : ℕ => ℕ))) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [hs] at hσ; rw [ht]
      rw [Finset.mem_sigma] at hσ ⊢
      obtain ⟨h1, h2⟩ := hσ
      obtain ⟨h1low, h1high⟩ := Finset.mem_Icc.mp h1
      obtain ⟨h2dvd, h2ne⟩ := Nat.mem_divisors.mp h2
      have hσ1pos : 0 < σ.1 := by omega
      have hσ2pos : 0 < σ.2 := Nat.pos_of_dvd_of_pos h2dvd hσ1pos
      have hσ2le : σ.2 ≤ σ.1 := Nat.le_of_dvd hσ1pos h2dvd
      refine ⟨?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨hσ2pos, le_trans hσ2le h1high⟩
      · refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · rw [Nat.le_div_iff_mul_le hσ2pos]; omega
        · exact Nat.div_le_div_right h1high
    · intro τ hτ
      rw [ht] at hτ; rw [hs]
      rw [Finset.mem_sigma] at hτ ⊢
      obtain ⟨h1, h2⟩ := hτ
      obtain ⟨h1low, h1high⟩ := Finset.mem_Icc.mp h1
      obtain ⟨h2low, h2high⟩ := Finset.mem_Icc.mp h2
      have h1p : 0 < τ.1 := by omega
      have h2p : 0 < τ.2 := by omega
      have hmul : τ.1 * τ.2 ≤ x := le_trans (Nat.mul_le_mul_left τ.1 h2high) (Nat.mul_div_le x τ.1)
      refine ⟨?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), hmul⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_mul_right τ.1 τ.2, by positivity⟩
    · intro σ hσ
      rw [hs] at hσ
      rw [Finset.mem_sigma] at hσ
      obtain ⟨h1, h2⟩ := hσ
      have h2dvd := (Nat.mem_divisors.mp h2).1
      rw [Nat.mul_div_cancel' h2dvd]
    · intro τ hτ
      rw [ht] at hτ
      rw [Finset.mem_sigma] at hτ
      obtain ⟨h1, h2⟩ := hτ
      have h1pos : 0 < τ.1 := by have := (Finset.mem_Icc.mp h1).1; omega
      rw [Nat.mul_div_cancel_left _ h1pos]
    · intro σ hσ
      rw [hs] at hσ
      rw [Finset.mem_sigma] at hσ
      obtain ⟨h1, h2⟩ := hσ
      have h2dvd := (Nat.mem_divisors.mp h2).1
      have hmul : σ.2 * (σ.1 / σ.2) = σ.1 := Nat.mul_div_cancel' h2dvd
      congr 1
      rw [← Nat.cast_mul, hmul]
  -- Step 3: expand the reindexed sigma-sum.
  have step3 : (∑ τ ∈ t, (1 : ℝ) / ((τ.1 : ℝ) * (τ.2 : ℝ)))
      = ∑ e ∈ Finset.Icc 1 x, ∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / ((e : ℝ) * (m : ℝ)) := by
    rw [ht, Finset.sum_sigma]
  -- Step 4: bound each inner harmonic sum.
  have step4 : (∑ e ∈ Finset.Icc 1 x, ∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / ((e : ℝ) * (m : ℝ)))
      ≤ (1 + Real.log x) ^ 2 := by
    have hterm : ∀ e ∈ Finset.Icc 1 x,
        (∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / ((e : ℝ) * (m : ℝ)))
          ≤ (1 / (e : ℝ)) * (1 + Real.log x) := by
      intro e he
      obtain ⟨helow, hehigh⟩ := Finset.mem_Icc.mp he
      have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
      have hfac : (∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / ((e : ℝ) * (m : ℝ)))
          = (1 / (e : ℝ)) * (∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / (m : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hmpos : (0 : ℝ) < (m : ℝ) := by
          exact_mod_cast (by have := (Finset.mem_Icc.mp hm).1; omega : 0 < m)
        field_simp
      rw [hfac]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hMdef : (∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / (m : ℝ)) = (harmonic (x / e) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        apply Finset.sum_congr rfl
        intro m hm
        rw [one_div]
      rw [hMdef]
      calc (harmonic (x / e) : ℝ)
          ≤ 1 + Real.log ((x / e : ℕ) : ℝ) := harmonic_le_one_add_log (x / e)
        _ ≤ 1 + Real.log (x : ℝ) := by
            have hxepos : (0 : ℝ) < ((x / e : ℕ) : ℝ) := by
              exact_mod_cast (Nat.div_pos hehigh (by omega : 0 < e))
            have hxele : ((x / e : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Nat.div_le_self x e)
            have := Real.log_le_log hxepos hxele
            linarith
    calc (∑ e ∈ Finset.Icc 1 x, ∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / ((e : ℝ) * (m : ℝ)))
        ≤ ∑ e ∈ Finset.Icc 1 x, (1 / (e : ℝ)) * (1 + Real.log x) := Finset.sum_le_sum hterm
      _ = (∑ e ∈ Finset.Icc 1 x, (1 / (e : ℝ))) * (1 + Real.log x) := by rw [← Finset.sum_mul]
      _ ≤ (1 + Real.log x) * (1 + Real.log x) := by
          apply mul_le_mul_of_nonneg_right _ (by
            have : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
            linarith)
          have hsumx : (∑ e ∈ Finset.Icc 1 x, (1 : ℝ) / (e : ℝ)) = (harmonic x : ℝ) := by
            rw [harmonic_eq_sum_Icc]
            push_cast
            apply Finset.sum_congr rfl
            intro e he
            rw [one_div]
          rw [hsumx]
          exact harmonic_le_one_add_log x
      _ = (1 + Real.log x) ^ 2 := by ring
  calc (∑ d ∈ Finset.Icc 1 x, ((Nat.divisors d).card : ℝ) / (d : ℝ))
      = ∑ σ ∈ s, (1 : ℝ) / (σ.1 : ℝ) := step1
    _ = ∑ τ ∈ t, (1 : ℝ) / ((τ.1 : ℝ) * (τ.2 : ℝ)) := step2
    _ = ∑ e ∈ Finset.Icc 1 x, ∑ m ∈ Finset.Icc 1 (x / e), (1 : ℝ) / ((e : ℝ) * (m : ℝ)) := step3
    _ ≤ (1 + Real.log x) ^ 2 := step4

/-- **The average number of square roots of `-1` is bounded by a power of
`log x`.**  Since `ρ(d) ≤ τ(d)` and `∑_{d ≤ x} τ(d)/d ≤ (1 + log x)^2`, the sum
`∑_{d ≤ x} ρ(d)/d` is bounded by `(1 + 1 / log 2)^2 (log x)^2` for `x ≥ 2`. -/
lemma sum_rho_div_polylog :
    ∃ K : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      (∑ d ∈ Finset.Icc 1 x, (({α : ZMod d | α ^ 2 = -1}.ncard : ℕ) : ℝ) / (d : ℝ))
        ≤ C * (Real.log x) ^ K := by
  refine ⟨2, (1 + 1 / Real.log 2) ^ 2, ?_, ?_⟩
  · have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro x hx
    have hx1 : 1 ≤ x := by omega
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have h1 : (∑ d ∈ Finset.Icc 1 x, (({α : ZMod d | α ^ 2 = -1}.ncard : ℕ) : ℝ) / (d : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 x, ((Nat.divisors d).card : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hle : (({α : ZMod d | α ^ 2 = -1}.ncard : ℕ) : ℝ) ≤ ((Nat.divisors d).card : ℝ) := by
        exact_mod_cast rho_le_divisor_count hd1
      have hdpos : (0:ℝ) < (d:ℝ) := by
        have : 0 < d := by omega
        exact_mod_cast this
      exact div_le_div_of_nonneg_right hle hdpos.le
    have h2 := sum_divisor_count_div_le x hx1
    have h3 : (1 + Real.log x) ^ 2 ≤ (1 + 1 / Real.log 2) ^ 2 * (Real.log x) ^ 2 := by
      have hstep : 1 + Real.log x ≤ (1 + 1 / Real.log 2) * Real.log x := by
        have hdiv : 1 ≤ Real.log x / Real.log 2 := (one_le_div hlog2).mpr hlogx
        have : Real.log x + 1 ≤ Real.log x + Real.log x / Real.log 2 := by linarith
        calc (1:ℝ) + Real.log x = Real.log x + 1 := by ring
          _ ≤ Real.log x + Real.log x / Real.log 2 := this
          _ = (1 + 1 / Real.log 2) * Real.log x := by ring
      have hnonneg : (0:ℝ) ≤ 1 + Real.log x := by linarith
      calc (1 + Real.log x)^2 ≤ ((1 + 1/Real.log 2) * Real.log x)^2 :=
             pow_le_pow_left₀ hnonneg hstep 2
        _ = (1 + 1/Real.log 2)^2 * (Real.log x)^2 := by ring
    have hgoal : (∑ d ∈ Finset.Icc 1 x, (({α : ZMod d | α ^ 2 = -1}.ncard : ℕ) : ℝ) / (d : ℝ))
        ≤ (1 + 1 / Real.log 2)^2 * (Real.log x)^2 := le_trans (le_trans h1 h2) h3
    simpa using hgoal

end Commons.NumberTheory.FriedlanderIwaniec
