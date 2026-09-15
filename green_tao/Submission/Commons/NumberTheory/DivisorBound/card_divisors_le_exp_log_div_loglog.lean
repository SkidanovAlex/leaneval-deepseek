import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Commons.NumberTheory.DivisorBound

open Finset

/-- The logarithm of the number of divisors of `n ≠ 0`, expanded over the
prime factorization of `n`. -/
lemma log_card_divisors_eq_sum {n : ℕ} (hn : n ≠ 0) :
    Real.log ((n.divisors.card : ℕ) : ℝ) =
      ∑ p ∈ n.primeFactors, Real.log ((n.factorization p + 1 : ℕ) : ℝ) := by
  have hcast : ((n.divisors.card : ℕ) : ℝ)
      = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    conv_lhs => rw [Nat.card_divisors hn]
    rw [Nat.cast_prod]
  rw [hcast, Real.log_prod]
  intro p hp
  positivity

/-- `Real.log n` expanded over the prime factorization of `n ≠ 0`. -/
lemma log_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ)
      = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℕ) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_pow]
  rw [hcast, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_pow]
  · intro p hp
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)

/-- `1/2 ≤ log 2`. -/
lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/2 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  linarith

/-- For `x ≥ 64`, `log x ≤ x / 4`. -/
lemma log_le_div_four {x : ℝ} (hx : 64 ≤ x) : Real.log x ≤ x / 4 := by
  have hxpos : 0 < x := by linarith
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs8 : 8 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hxpos)]
    norm_num
    linarith
  have h1 : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_self hsx
    rw [Real.log_sqrt (le_of_lt hxpos)] at h
    linarith
  have h2 : 2 * Real.sqrt x ≤ x / 4 := by
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (le_of_lt hxpos)
    nlinarith [hs8, hsx, hsq]
  linarith

theorem card_divisors_le_exp_log_div_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      ((n.divisors.card : ℕ) : ℝ)
        ≤ Real.exp (C * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) := by
  refine ⟨100, by norm_num, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  set L : ℝ := Real.log (n : ℝ) with hLdef
  set Ll : ℝ := Real.log L with hLldef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos h1n
  have hLgt1 : 1 < L := by
    have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3L : Real.log 3 ≤ L := by rw [hLdef]; exact Real.log_le_log (by norm_num) h3n
    have h13 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    linarith
  have hLlpos : 0 < Ll := by rw [hLldef]; exact Real.log_pos hLgt1
  have hLl_nonneg : 0 ≤ Ll := le_of_lt hLlpos
  have hdpos : 0 < ((n.divisors.card : ℕ) : ℝ) := by
    have hmem : 1 ∈ n.divisors := by rw [Nat.mem_divisors]; exact ⟨one_dvd n, hn0⟩
    have : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, hmem⟩
    exact_mod_cast this
  rw [← Real.log_le_iff_le_exp hdpos]
  -- goal : Real.log ((n.divisors.card : ℕ) : ℝ) ≤ 100 * L / Ll
  have hLl_sq : Ll ^ 2 ≤ 4 * L := by
    have hsx : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
    have h1 : Real.log L ≤ 2 * Real.sqrt L := by
      have h := Real.log_le_self hsx
      rw [Real.log_sqrt (le_of_lt hLpos)] at h
      linarith
    have h2 : Ll ≤ 2 * Real.sqrt L := by rw [hLldef]; exact h1
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hLpos)
    calc Ll ^ 2 ≤ (2 * Real.sqrt L) ^ 2 := pow_le_pow_left₀ hLl_nonneg h2 2
      _ = 4 * L := by nlinarith [hsq]
  have h2Ll : 2 * Ll ≤ 8 * L / Ll := by
    rw [le_div_iff₀ hLlpos]
    nlinarith [hLl_sq]
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  by_cases hcase : (64 : ℝ) ≤ Ll
  · -- analytic case
    set y : ℝ := L / Ll ^ 2 with hydef
    have hypos : 0 < y := by rw [hydef]; positivity
    have hlogy : Real.log y = Ll - 2 * Real.log Ll := by
      have h1 : Real.log y = Real.log L - Real.log (Ll ^ 2) := by
        rw [hydef, Real.log_div (ne_of_gt hLpos) (pow_ne_zero 2 (ne_of_gt hLlpos))]
      rw [h1, ← hLldef, Real.log_pow]
      ring
    have hlogLlle : Real.log Ll ≤ Ll / 4 := log_le_div_four hcase
    have hlogy_ge : Ll / 2 ≤ Real.log y := by rw [hlogy]; linarith
    have hlogy_pos : 0 < Real.log y := by linarith
    have hAcard : ((n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).card : ℝ) ≤ y + 1 := by
      have hsub : n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y) ⊆ Finset.range (Nat.floor y + 1) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_range]
        have : p ≤ Nat.floor y := Nat.le_floor hp.2
        omega
      have hc := Finset.card_le_card hsub
      rw [Finset.card_range] at hc
      have hfloor : (Nat.floor y : ℝ) ≤ y := Nat.floor_le (le_of_lt hypos)
      have hcR : ((n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).card : ℝ) ≤ (Nat.floor y : ℝ) + 1 := by
        have h2 : ((n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).card : ℝ) ≤ ((Nat.floor y + 1 : ℕ) : ℝ) := by
          exact_mod_cast hc
        simpa using h2
      linarith
    have hlog3L : Real.log (3 * L) ≤ 2 * Ll := by
      have h3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
      rw [Real.log_mul (by norm_num) (ne_of_gt hLpos), ← hLldef]
      linarith
    -- bound on the small-prime part
    have hA_bound : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)),
        Real.log ((n.factorization p + 1 : ℕ) : ℝ) ≤ 50 * L / Ll := by
      have hstep1 : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)),
          Real.log ((n.factorization p + 1 : ℕ) : ℝ)
          ≤ ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)), Real.log (3 * L) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        have hpf : p ∈ n.primeFactors := hp.1
        have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpf).1
        have hdiv : p ^ n.factorization p ∣ n := by
          conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
          exact Finset.dvd_prod_of_mem (fun q : ℕ => q ^ n.factorization q) hpf
        have hle : p ^ n.factorization p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdiv
        have hleR : (p:ℝ) ^ (n.factorization p : ℕ) ≤ (n:ℝ) := by exact_mod_cast hle
        have hlog : (n.factorization p : ℝ) * Real.log (p:ℝ) ≤ L := by
          have := Real.log_le_log (pow_pos (by exact_mod_cast hpprime.pos) _) hleR
          rw [Real.log_pow, ← hLdef] at this
          exact this
        have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlog2le : Real.log 2 ≤ Real.log (p:ℝ) := by
          apply Real.log_le_log (by norm_num)
          exact_mod_cast hpprime.two_le
        have hep_le : (n.factorization p : ℝ) ≤ L / Real.log 2 := by
          rw [le_div_iff₀ hlog2pos]
          nlinarith [hlog, hlog2le, (by positivity : (0:ℝ) ≤ (n.factorization p : ℝ))]
        have hep1 : ((n.factorization p + 1 : ℕ) : ℝ) ≤ 3 * L := by
          have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := half_le_log_two
          have hLd : L / Real.log 2 ≤ 2 * L := by
            rw [div_le_iff₀ hlog2pos]
            nlinarith [hlog2half, hLpos]
          push_cast
          linarith
        exact Real.log_le_log (by positivity) hep1
      have hstep2 : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)), Real.log (3 * L)
          = (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).card * Real.log (3 * L) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hstep3 : (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).card * Real.log (3 * L)
          ≤ (y + 1) * (2 * Ll) := by
        have hnn : 0 ≤ Real.log (3 * L) := Real.log_nonneg (by linarith [hLgt1])
        exact mul_le_mul hAcard hlog3L hnn (by linarith)
      have hstep4 : (y + 1) * (2 * Ll) ≤ 50 * L / Ll := by
        have hyeq : (y + 1) * (2 * Ll) = 2 * L / Ll + 2 * Ll := by
          rw [hydef]; field_simp
        rw [hyeq, le_div_iff₀ hLlpos]
        have hmul : (2 * L / Ll + 2 * Ll) * Ll = 2 * L + 2 * Ll ^ 2 := by field_simp
        rw [hmul]
        nlinarith [hLl_sq, hLpos]
      linarith [hstep1, hstep2, hstep3, hstep4]
    -- bound on the large-prime part
    have hB_bound : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)),
        Real.log ((n.factorization p + 1 : ℕ) : ℝ) ≤ 50 * L / Ll := by
      have hstep1 : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)),
          Real.log ((n.factorization p + 1 : ℕ) : ℝ)
          ≤ ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)),
              (n.factorization p : ℝ) * Real.log 2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        have hsucc : ((n.factorization p + 1 : ℕ) : ℝ) ≤ (2:ℝ) ^ (n.factorization p : ℕ) := by
          have hnat : (n.factorization p + 1 : ℕ) ≤ 2 ^ n.factorization p := by
            have := Nat.lt_two_pow_self (n := n.factorization p); omega
          exact_mod_cast hnat
        have h := Real.log_le_log (by positivity : (0:ℝ) < ((n.factorization p + 1 : ℕ) : ℝ)) hsucc
        rwa [Real.log_pow] at h
      have hstep2 : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)),
            (n.factorization p : ℝ) * Real.log 2
          = (∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ)) * Real.log 2 := by
        rw [Finset.sum_mul]
      have hBsum : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) ≤ 2 * L / Ll := by
        have hstep : Real.log y * (∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)),
            (n.factorization p : ℝ)) ≤ L := by
          have h1 : Real.log y * (∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ))
              = ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) * Real.log y := by
            rw [mul_comm (Real.log y), Finset.sum_mul]
          rw [h1]
          have h2 : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) * Real.log y
              ≤ ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) * Real.log (p:ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            rw [Finset.mem_filter] at hp
            have hpf : p ∈ n.primeFactors := hp.1
            have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpf).1
            have hppos : 0 < (p:ℝ) := by exact_mod_cast hpprime.pos
            have hpy : y ≤ (p:ℝ) := le_of_lt (not_le.mp hp.2)
            exact mul_le_mul_of_nonneg_left (Real.log_le_log hypos hpy) (by positivity)
          have h3 : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) * Real.log (p:ℝ)
              ≤ ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p:ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp; exact (Finset.mem_filter.mp hp).1
            · intro p hp hnot; positivity
          calc ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) * Real.log y
              ≤ ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) * Real.log (p:ℝ) := h2
            _ ≤ ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p:ℝ) := h3
            _ = L := (log_eq_sum_factorization hn0).symm
        have hA : ∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ) ≤ L / Real.log y := by
          rw [le_div_iff₀ hlogy_pos, mul_comm]
          exact hstep
        have hB : L / Real.log y ≤ 2 * L / Ll := by
          rw [div_le_iff₀ hlogy_pos]
          calc L = (2 * L / Ll) * (Ll / 2) := by field_simp
            _ ≤ (2 * L / Ll) * Real.log y := by
                apply mul_le_mul_of_nonneg_left hlogy_ge
                exact div_nonneg (by positivity) (le_of_lt hLlpos)
        exact le_trans hA hB
      have hfinal : (∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ)) * Real.log 2
          ≤ 50 * L / Ll := by
        have hX : 0 ≤ L / Ll := div_nonneg (le_of_lt hLpos) (le_of_lt hLlpos)
        have h2L : (∑ p ∈ (n.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)), (n.factorization p : ℝ)) * Real.log 2
            ≤ (2 * L / Ll) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right hBsum (le_of_lt (Real.log_pos (by norm_num)))
        have h3 : (2 * L / Ll) * Real.log 2 ≤ 50 * L / Ll := by
          have : (2 * L / Ll) * Real.log 2 = (2 * Real.log 2) * (L / Ll) := by ring
          rw [this, show 50 * L / Ll = 50 * (L / Ll) by ring]
          apply mul_le_mul_of_nonneg_right _ hX
          linarith [hlog2le1]
        linarith [h2L, h3]
      linarith [hstep1, hstep2, hfinal]
    rw [log_card_divisors_eq_sum hn0, ← Finset.sum_filter_add_sum_filter_not n.primeFactors
      (fun p : ℕ => (p:ℝ) ≤ y) (fun p => Real.log ((n.factorization p + 1 : ℕ) : ℝ))]
    have hsum := add_le_add hA_bound hB_bound
    have h2s : 50 * L / Ll + 50 * L / Ll = 100 * L / Ll := by ring
    rw [← h2s]
    exact hsum
  · -- crude case
    push Not at hcase
    have hlogle : Real.log ((n.divisors.card : ℕ) : ℝ) ≤ L := by
      have hle : ((n.divisors.card : ℕ) : ℝ) ≤ (n:ℝ) := by
        exact_mod_cast Nat.card_divisors_le_self n
      rw [hLdef]
      exact Real.log_le_log hdpos hle
    have hLl100 : Ll ≤ 100 := by linarith
    have hbound : L ≤ 100 * L / Ll := by
      rw [le_div_iff₀ hLlpos]
      nlinarith [hLl100, hLpos]
    linarith [hlogle, hbound]

end Commons.NumberTheory.DivisorBound