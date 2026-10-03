/-
# `Work.FIArea7.P231M.prodInvSqLeRad`

The "local factor" estimate attached to Prop. 23.1 of *FI*: the product over the
primes dividing `n` of the reciprocal square `(1 - p^{-11/12})^{-2}` is bounded,
for every `ε > 0`, by a constant times the `ε`-th power of the radical
`∏_{p | n} p`.

The proof is purely multiplicative and needs no input about the size of `n`:

* for every `ε > 0` there is a threshold `N` with
  `(1 - p^{-11/12})^{-2} ≤ p^ε` for all primes `p ≥ N` (the left side tends to
  `1`, the right side to `∞`; concretely `p ≥ max 4 4^{1/ε}` works, since then
  `p^{-11/12} ≤ 4^{-11/12} ≤ 1/2` gives a factor `≤ 4 ≤ p^ε`);
* the finitely many primes below the threshold are absorbed into the constant
  `C = ∏_{p < N, p prime} (1 - p^{-11/12})^{-2}`, every factor of which is `≥ 1`.
-/
import Mathlib

namespace Work.FIArea7.P231M

/-- Each factor `(1 - p^{-11/12})^{-2}` is strictly positive for a prime `p`. -/
private lemma factor_invSq_pos (p : ℕ) (hp : Nat.Prime p) :
    0 < ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hxlt : (p : ℝ) ^ (-(11 / 12 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hpos : 0 < 1 - (p : ℝ) ^ (-(11 / 12 : ℝ)) := by linarith
  exact inv_pos.mpr (pow_pos hpos 2)

/-- Each factor `(1 - p^{-11/12})^{-2}` is at least `1` for a prime `p`. -/
private lemma factor_invSq_ge_one (p : ℕ) (hp : Nat.Prime p) :
    1 ≤ ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hxlt : (p : ℝ) ^ (-(11 / 12 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hxnn : 0 ≤ (p : ℝ) ^ (-(11 / 12 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hpos : 0 < 1 - (p : ℝ) ^ (-(11 / 12 : ℝ)) := by linarith
  have hle1 : (1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2 ≤ 1 := by nlinarith [hpos, hxlt, hxnn]
  exact (one_le_inv₀ (pow_pos hpos 2)).mpr hle1

/-- Threshold form of the analytic input: for every `ε > 0` all primes `p`
beyond some `N` satisfy `(1 - p^{-11/12})^{-2} ≤ p^ε`. -/
private lemma invSq_factor_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → N ≤ p →
      ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ ≤ (p : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max 4 ((4 : ℝ) ^ (1 / ε)))
  refine ⟨N, ?_⟩
  intro p hp hNp
  have hNpR : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hNp
  have hp4 : (4 : ℝ) ≤ (p : ℝ) := le_trans (le_trans (le_max_left _ _) hN) hNpR
  have hx12 : (p : ℝ) ^ (-(11 / 12 : ℝ)) ≤ 1 / 2 := by
    have h1 : (p : ℝ) ^ (-(11 / 12 : ℝ)) ≤ (4 : ℝ) ^ (-(11 / 12 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 4) hp4 (by norm_num : (-(11 / 12 : ℝ)) ≤ 0)
    have h2 : (4 : ℝ) ^ (-(11 / 12 : ℝ)) ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : -(11 / 12 : ℝ) ≤ -(1 / 2 : ℝ))
      have h3 : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
        norm_num
      linarith
    linarith
  have hsmall : ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ ≤ 4 := by
    have hsq : (1 / 4 : ℝ) ≤ (1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2 := by nlinarith [hx12]
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hsq
    norm_num at h
    linarith
  have hle4 : (4 : ℝ) ≤ (p : ℝ) ^ ε := by
    have h1 : (4 : ℝ) ^ (1 / ε) ≤ (p : ℝ) :=
      le_trans (le_trans (le_max_right _ _) hN) hNpR
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (1 / ε)) h1 (le_of_lt hε)
    have h3 : ((4 : ℝ) ^ (1 / ε)) ^ ε = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
    linarith
  linarith

/-- **Friedlander–Iwaniec, local factor estimate.** For every `ε > 0` the product
`∏_{p | n} (1 - p^{-11/12})^{-2}` is bounded by a constant times `(∏_{p | n} p)^ε`. -/
theorem prodInvSqLeRad (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∏ p ∈ n.primeFactors, ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹)
        ≤ C * (∏ p ∈ n.primeFactors, (p : ℝ)) ^ ε := by
  classical
  obtain ⟨N, hthr⟩ := invSq_factor_le_rpow ε hε
  set f : ℕ → ℝ := fun p => ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ with hf
  set t : Finset ℕ := (Finset.range N).filter Nat.Prime with ht
  set C : ℝ := ∏ p ∈ t, f p with hC
  have hfpos : ∀ p, Nat.Prime p → 0 < f p := by
    intro p hp; rw [hf]; exact factor_invSq_pos p hp
  have hfge1 : ∀ p, Nat.Prime p → 1 ≤ f p := by
    intro p hp; rw [hf]; exact factor_invSq_ge_one p hp
  have hCpos : 0 < C := by
    rw [hC]
    exact Finset.prod_pos (fun p hp => hfpos p (Finset.mem_filter.mp (ht ▸ hp)).2)
  refine ⟨C, hCpos, ?_⟩
  intro n _
  rw [← Finset.prod_filter_mul_prod_filter_not (n.primeFactors) (fun p => p < N) f]
  have hsmall : (∏ x ∈ n.primeFactors with x < N, f x) ≤ C := by
    rw [hC]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact le_of_lt (hfpos p (Nat.prime_of_mem_primeFactors hp.1))
    · intro p hp _
      exact hfge1 p (Finset.mem_filter.mp (ht ▸ hp)).2
  have hlarge : (∏ x ∈ n.primeFactors with ¬ x < N, f x)
      ≤ (∏ p ∈ n.primeFactors, (p : ℝ)) ^ ε := by
    have step1 : (∏ x ∈ n.primeFactors with ¬ x < N, f x)
        ≤ (∏ x ∈ n.primeFactors with ¬ x < N, (x : ℝ) ^ ε) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        rw [Finset.mem_filter] at hp
        exact le_of_lt (hfpos p (Nat.prime_of_mem_primeFactors hp.1))
      · intro p hp
        rw [Finset.mem_filter] at hp
        exact hthr p (Nat.prime_of_mem_primeFactors hp.1) (not_lt.mp hp.2)
    have step2 : (∏ x ∈ n.primeFactors with ¬ x < N, (x : ℝ) ^ ε)
        ≤ (∏ x ∈ n.primeFactors, (x : ℝ) ^ ε) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
      · intro p hp
        exact Real.rpow_nonneg (Nat.cast_nonneg p) ε
      · intro p hp _
        exact Real.one_le_rpow (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le) (le_of_lt hε)
    have step3 : (∏ p ∈ n.primeFactors, (p : ℝ) ^ ε) = (∏ p ∈ n.primeFactors, (p : ℝ)) ^ ε :=
      Real.finsetProd_rpow n.primeFactors (fun p => (p : ℝ)) (fun p _ => Nat.cast_nonneg p) ε
    linarith [step1, step2]
  exact mul_le_mul hsmall hlarge
    (Finset.prod_nonneg (fun p hp => le_of_lt (hfpos p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))))
    (le_of_lt hCpos)

end Work.FIArea7.P231M
