import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.DivisorBound

open Finset

/-- For every `eps > 0` there is a constant `C ≥ 1` with `a + 1 ≤ C * 2 ^ (eps * a)`
for all natural `a`.  (This is the only place where the elementary bound
`a + 1 ≤ 2 ^ a` is upgraded to an arbitrarily small exponential gain.) -/
lemma exists_const_one_add_le_mul_rpow_two (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℕ, (a : ℝ) + 1 ≤ C * (2 : ℝ) ^ (eps * (a : ℝ)) := by
  refine ⟨max 1 (2 / (eps * Real.log 2)), le_max_left _ _, ?_⟩
  intro a
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : eps * Real.log 2 ≠ 0 := ne_of_gt (mul_pos heps hlog2)
  have hCnn : 0 ≤ max 1 (2 / (eps * Real.log 2)) := le_trans zero_le_one (le_max_left _ _)
  have hCge : 2 / (eps * Real.log 2) ≤ max 1 (2 / (eps * Real.log 2)) := le_max_right _ _
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [show eps * ((0 : ℕ) : ℝ) = 0 by simp, Real.rpow_zero, mul_one]
    simp only [Nat.cast_zero, zero_add]
    exact le_max_left _ _
  · have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    set X : ℝ := eps * (a : ℝ) with hX
    have hXnn : 0 ≤ X := by rw [hX]; positivity
    have hexp : (2 : ℝ) ^ X = Real.exp (X * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
    have hexp_ge : X * Real.log 2 + 1 ≤ (2 : ℝ) ^ X := by
      rw [hexp]; exact Real.add_one_le_exp _
    have hkey : (2 / (eps * Real.log 2)) * (X * Real.log 2) = 2 * (a : ℝ) := by
      rw [hX]; field_simp
    calc (a : ℝ) + 1 ≤ 2 * (a : ℝ) := by linarith
      _ = (2 / (eps * Real.log 2)) * (X * Real.log 2) := hkey.symm
      _ ≤ max 1 (2 / (eps * Real.log 2)) * (X * Real.log 2) :=
            mul_le_mul_of_nonneg_right hCge (by positivity)
      _ ≤ max 1 (2 / (eps * Real.log 2)) * (X * Real.log 2 + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hCnn
      _ ≤ max 1 (2 / (eps * Real.log 2)) * (2 : ℝ) ^ X :=
            mul_le_mul_of_nonneg_left hexp_ge hCnn
      _ = max 1 (2 / (eps * Real.log 2)) * (2 : ℝ) ^ (eps * (a : ℝ)) := by rw [hX]

/-- The prime-factorization expansion of `n ^ r` as a product of prime powers. -/
lemma rpow_eq_prod_primeFactors_factorization (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    (n : ℝ) ^ r = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (r * (n.factorization p : ℝ)) := by
  have hnat : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rfl
  rw [hnat, ← Real.finsetProd_rpow n.primeFactors (fun p => (p : ℝ) ^ (n.factorization p))
        (fun p _ => by positivity) r]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Real.rpow_natCast (p : ℝ) (n.factorization p),
      ← Real.rpow_mul (show (0 : ℝ) ≤ (p : ℝ) by positivity),
      mul_comm ((n.factorization p : ℕ) : ℝ) r]

/-- **The divisor bound.**  For every `eps > 0` there is a constant `C` with
`d(n) ≤ C * n ^ eps` for all `n`, where `d(n)` is the number of divisors of `n`.

The proof is elementary and quantitative.  Write `d(n) = ∏_{p | n} (e_p + 1)`.
Pick `M` with `M * eps ≥ 1` and split the primes dividing `n` at the threshold
`A = 2 ^ M`:
* for `p ≥ A` we have `p ^ eps ≥ 2`, hence `e + 1 ≤ 2 ^ e ≤ (p ^ eps) ^ e = p ^ (eps * e)`;
* for `p < A` we use `e + 1 ≤ C₀ * 2 ^ (eps * e) ≤ C₀ * p ^ (eps * e)`, where
  `C₀ = max 1 (2 / (eps * log 2))` comes from `2 ^ x ≥ x * log 2 + 1`; this costs
  only the fixed factor `C₀ ^ (#{p < A})` because there are at most `A` such primes.
Multiplying the two estimators and using `∏_{p | n} p ^ (eps * e_p) = n ^ eps`
gives `d(n) ≤ C₀ ^ A * n ^ eps`, and `C = max 1 (C₀ ^ A)` also covers `n = 0, 1`. -/
theorem card_divisors_le_rpow (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ eps := by
  obtain ⟨C₀, hC₀one, hC₀⟩ := exists_const_one_add_le_mul_rpow_two eps heps
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀one
  -- choose the threshold `A = 2 ^ M` with `M * eps ≥ 1`
  set M : ℕ := Nat.floor ((1 : ℝ) / eps) + 1 with hMdef
  have hMeps : (1 : ℝ) ≤ (M : ℝ) * eps := by
    have hlt : (1 : ℝ) / eps < (M : ℝ) := by
      have h := Nat.lt_floor_add_one ((1 : ℝ) / eps)
      simpa [hMdef] using h
    have h2 : (1 : ℝ) < (M : ℝ) * eps := by
      have h3 := mul_lt_mul_of_pos_right hlt heps
      rwa [div_mul_cancel₀ (1 : ℝ) (ne_of_gt heps)] at h3
    exact le_of_lt h2
  set A : ℕ := 2 ^ M with hAdef
  have hApow : (A : ℝ) = (2 : ℝ) ^ M := by rw [hAdef]; push_cast; rfl
  -- a prime `p ≥ A` gives the clean bound `e + 1 ≤ p ^ (eps * e)`
  have hlarge : ∀ {p e : ℕ}, Nat.Prime p → A ≤ p →
      ((e + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (eps * (e : ℝ)) := by
    intro p e hpp hAp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hpm : (2 : ℝ) ^ M ≤ (p : ℝ) := by
      have h : (A : ℝ) ≤ (p : ℝ) := by exact_mod_cast hAp
      rwa [hApow] at h
    have hpeps : (2 : ℝ) ≤ (p : ℝ) ^ eps := by
      have h1 : (2 : ℝ) ^ ((M : ℝ) * eps) = ((2 : ℝ) ^ M) ^ eps := by
        rw [← Real.rpow_natCast (2 : ℝ) M, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) * eps) := by
        have h3 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) * eps) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hMeps
        simpa using h3
      calc (2 : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) * eps) := h2
        _ = ((2 : ℝ) ^ M) ^ eps := h1
        _ ≤ (p : ℝ) ^ eps := Real.rpow_le_rpow (by positivity) hpm heps.le
    calc ((e + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ e := by
          have h : ((e + 1 : ℕ) : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := e))
          simpa using h
      _ ≤ ((p : ℝ) ^ eps) ^ e := pow_le_pow_left₀ (by positivity) hpeps e
      _ = (p : ℝ) ^ (eps * (e : ℝ)) := by
          rw [← Real.rpow_natCast ((p : ℝ) ^ eps) e,
              ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  -- a prime `p < A` costs only a fixed multiplicative constant
  have hsmall : ∀ {p e : ℕ}, Nat.Prime p → p < A →
      ((e + 1 : ℕ) : ℝ) ≤ C₀ * (p : ℝ) ^ (eps * (e : ℝ)) := by
    intro p e hpp _
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have h1 : (2 : ℝ) ^ (eps * (e : ℝ)) ≤ (p : ℝ) ^ (eps * (e : ℝ)) :=
      Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    calc ((e + 1 : ℕ) : ℝ) ≤ C₀ * (2 : ℝ) ^ (eps * (e : ℝ)) := by simpa using hC₀ e
      _ ≤ C₀ * (p : ℝ) ^ (eps * (e : ℝ)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hC₀pos)
  refine ⟨max 1 (C₀ ^ A), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, Real.zero_rpow (ne_of_gt heps)]
    simp
  · obtain ⟨hcard, hsplit, hfull⟩ :
        ((Nat.divisors n).card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) ∧
        (∏ p ∈ n.primeFactors.filter (fun p => p < A), ((n.factorization p + 1 : ℕ) : ℝ)) *
          (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < A), ((n.factorization p + 1 : ℕ) : ℝ))
            = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) ∧
        (∏ p ∈ n.primeFactors, (p : ℝ) ^ (eps * (n.factorization p : ℝ))) = (n : ℝ) ^ eps := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.card_divisors hn, Nat.cast_prod]
      · exact Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p < A)
          (fun p => ((n.factorization p + 1 : ℕ) : ℝ))
      · exact (rpow_eq_prod_primeFactors_factorization n hn eps).symm
    set g : ℕ → ℝ := fun p => (p : ℝ) ^ (eps * (n.factorization p : ℝ)) with hgdef
    have hg_nonneg : ∀ p, 0 ≤ g p := by intro p; rw [hgdef]; positivity
    have hScard : (n.primeFactors.filter (fun p => p < A)).card ≤ A := by
      have hsub : n.primeFactors.filter (fun p => p < A) ⊆ Finset.range A := by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      calc (n.primeFactors.filter (fun p => p < A)).card ≤ (Finset.range A).card :=
            Finset.card_le_card hsub
        _ = A := Finset.card_range A
    have hSstep : (∏ p ∈ n.primeFactors.filter (fun p => p < A),
            ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ C₀ ^ (n.primeFactors.filter (fun p => p < A)).card *
            ∏ p ∈ n.primeFactors.filter (fun p => p < A), g p := by
      calc (∏ p ∈ n.primeFactors.filter (fun p => p < A), ((n.factorization p + 1 : ℕ) : ℝ))
          ≤ ∏ p ∈ n.primeFactors.filter (fun p => p < A), C₀ * g p := by
            apply Finset.prod_le_prod₀
            · intro p _
              exact Nat.cast_nonneg _
            · intro p hp
              have hpf : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
              have hpA : p < A := (Finset.mem_filter.mp hp).2
              exact hsmall (Nat.mem_primeFactors.mp hpf).1 hpA
        _ = C₀ ^ (n.primeFactors.filter (fun p => p < A)).card *
              ∏ p ∈ n.primeFactors.filter (fun p => p < A), g p := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hLstep : (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < A),
            ((n.factorization p + 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p < A), g p := by
      apply Finset.prod_le_prod₀
      · intro p _; exact Nat.cast_nonneg _
      · intro p hp
        have hpf : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
        have hpA : A ≤ p := by
          have := (Finset.mem_filter.mp hp).2
          omega
        exact hlarge (Nat.mem_primeFactors.mp hpf).1 hpA
    have hgsplit : (∏ p ∈ n.primeFactors.filter (fun p => p < A), g p) *
          (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < A), g p)
        = ∏ p ∈ n.primeFactors, g p :=
      Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p < A) g
    calc ((Nat.divisors n).card : ℝ)
        = (∏ p ∈ n.primeFactors.filter (fun p => p < A), ((n.factorization p + 1 : ℕ) : ℝ)) *
          (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < A),
            ((n.factorization p + 1 : ℕ) : ℝ)) := by rw [hcard, hsplit]
      _ ≤ (C₀ ^ (n.primeFactors.filter (fun p => p < A)).card *
            ∏ p ∈ n.primeFactors.filter (fun p => p < A), g p) *
          (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < A), g p) :=
            mul_le_mul hSstep hLstep
              (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _))
              (mul_nonneg (pow_nonneg (le_of_lt hC₀pos) _)
                (Finset.prod_nonneg (fun p _ => hg_nonneg p)))
      _ = C₀ ^ (n.primeFactors.filter (fun p => p < A)).card *
            ((∏ p ∈ n.primeFactors.filter (fun p => p < A), g p) *
              (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < A), g p)) := by ring
      _ = C₀ ^ (n.primeFactors.filter (fun p => p < A)).card * (n : ℝ) ^ eps := by
            rw [hgsplit, hfull]
      _ ≤ C₀ ^ A * (n : ℝ) ^ eps :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC₀one hScard) (by positivity)
      _ ≤ max 1 (C₀ ^ A) * (n : ℝ) ^ eps :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Commons.NumberTheory.DivisorBound