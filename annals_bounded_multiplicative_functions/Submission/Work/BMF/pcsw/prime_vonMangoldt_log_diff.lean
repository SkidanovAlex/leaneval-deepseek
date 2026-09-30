import Mathlib
import Submission.Work.BMF.pcsw.card_primepow_not_prime_le
import Submission.Work.BMF.pcsw.norm_inv_log_mul_vonMangoldt_mul_chi_mul_cpow_le_one
import Submission.Work.BMF.pcsw.prime_part_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

/-- **The `1/log`-weighted von Mangoldt sum agrees with the prime sum up to `O(√M log M)`.** At a
prime `p` one has `Λ p / log p = 1`, so the two sums differ exactly by the contribution of the
proper prime powers, `Σ_{p^k ∈ [N,M], k ≥ 2} χ(p^k) (p^k)^{it} / k`, whose terms have modulus
`1/k ≤ 1/2`.

Route. Split `Icc N M` into primes and non-primes (`Finset.sum_filter_add_sum_filter_not`) and
show each non-prime `n` with `Λ n ≠ 0` is a prime power `p^k`, `k ≥ 2`
(`ArithmeticFunction.vonMangoldt_ne_zero_iff` together with
`exists_prime_pow_of_isPrimePow_not_prime` from
`Submission/Work/BMF/liouville/sum_prime_pow_le_rect_sum.lean`), where the summand equals
`χ(p^k) (p^k)^{it}/k`, of modulus `1/k ≤ 1/2` (cf.
`Submission/Work/BMF/liouville/prime_power_twist_diff.lean`, which does the same comparison for
the weight `1/(n log n)`, and
`Submission/Work/BMF/liouville/weighted_vonMangoldt_decomp.lean` for the prime-power
decomposition of the von Mangoldt sum). Then count the surviving `n`: `p^k ≤ M` with `k ≥ 2`
forces `p ≤ √M`, and for each prime `p ≤ √M` there are at most `log₂ M` exponents `k`, so there
are at most `π(√M) · log₂ M ≤ √M · log M / log 2` of them. The difference is therefore at most
`(1/2)·√M·log M / log 2 ≤ √M · log M` since `1/(2 log 2) < 1`; so `C := 1` works. -/
theorem prime_vonMangoldt_log_diff :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (N M : ℕ),
      2 ≤ N → N ≤ M →
      ‖(∑ n ∈ Finset.Icc N M, ((Real.log n : ℝ) : ℂ)⁻¹ *
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (Complex.I * t)))
        - (∑ n ∈ (Finset.Icc N M).filter Nat.Prime, χ n * (n : ℂ) ^ (Complex.I * t))‖
        ≤ C * Real.sqrt (M : ℝ) * Real.log M := by
  -- The prime part of the weighted von Mangoldt sum is the prime sum, term by term; the
  -- surviving non-prime part is a sum of at most `2√M log M` terms of norm `≤ 1`.
  refine ⟨2, by norm_num, ?_⟩
  intro q _ χ t N M hN _
  classical
  set F : ℕ → ℂ := fun n => ((Real.log n : ℝ) : ℂ)⁻¹ *
      (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (Complex.I * t)) with hF
  set G : ℕ → ℂ := fun n => χ n * (n : ℂ) ^ (Complex.I * t) with hG
  -- The `1/log`-weight of a prime is cancelled by `Λ p = log p`.
  have hprime : ∑ n ∈ (Finset.Icc N M).filter Nat.Prime, F n
      = ∑ n ∈ (Finset.Icc N M).filter Nat.Prime, G n := by
    simpa only [hF, hG] using prime_part_eq q χ t N M
  -- The non-prime part is bounded by the pointwise bound `≤ 1` and the cardinality of the set
  -- of proper prime powers up to `M`.
  have hrest : ‖∑ n ∈ (Finset.Icc N M).filter (fun n => ¬ Nat.Prime n), F n‖
      ≤ 2 * Real.sqrt M * Real.log M := by
    have h1 : ‖∑ n ∈ (Finset.Icc N M).filter (fun n => ¬ Nat.Prime n), F n‖
        ≤ ∑ n ∈ (Finset.Icc N M).filter (fun n => ¬ Nat.Prime n), ‖F n‖ := norm_sum_le _ _
    -- only prime powers contribute, `Λ` vanishing elsewhere
    have h2 : ∑ n ∈ (Finset.Icc N M).filter (fun n => ¬ Nat.Prime n), ‖F n‖
        = ∑ n ∈ (Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n), ‖F n‖ := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro x hx
        obtain ⟨hxI, -, hxNP⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxI, hxNP⟩
      · intro x hx hxn
        obtain ⟨hxI, hxNP⟩ := Finset.mem_filter.mp hx
        have hΛ : ArithmeticFunction.vonMangoldt x = 0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun hpp =>
            hxn (Finset.mem_filter.mpr ⟨hxI, hpp, hxNP⟩))
        simp [F, hΛ]
    have h3 : ∑ n ∈ (Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n), ‖F n‖
        ≤ ∑ n ∈ (Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnI, -⟩ := Finset.mem_filter.mp hn
      exact norm_inv_log_mul_vonMangoldt_mul_chi_mul_cpow_le_one q χ t
        (le_trans hN (Finset.mem_Icc.mp hnI).1)
    have h4 : ∑ n ∈ (Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n), (1 : ℝ)
        = (((Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card : ℝ) := by
      simp
    have h5 : (((Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card : ℝ)
        ≤ (((Finset.Icc 2 M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card : ℝ) := by
      have hcard : ((Finset.Icc N M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card
          ≤ ((Finset.Icc 2 M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card :=
        Finset.card_le_card (fun x hx => by
          obtain ⟨hxI, hxP⟩ := Finset.mem_filter.mp hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hxI
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_trans hN hx1, hx2⟩, hxP⟩)
      exact_mod_cast hcard
    exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 (le_trans (le_of_eq h4)
      (le_trans h5 (card_primepow_not_prime_le M)))))
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.Icc N M)
    (p := fun n => Nat.Prime n) (f := F)
  have key : (∑ n ∈ Finset.Icc N M, F n) - (∑ n ∈ (Finset.Icc N M).filter Nat.Prime, G n)
      = ∑ n ∈ (Finset.Icc N M).filter (fun n => ¬ Nat.Prime n), F n := by
    rw [← hprime, ← hsplit]
    exact add_sub_cancel_left _ _
  calc ‖(∑ n ∈ Finset.Icc N M, F n) - (∑ n ∈ (Finset.Icc N M).filter Nat.Prime, G n)‖
      = ‖∑ n ∈ (Finset.Icc N M).filter (fun n => ¬ Nat.Prime n), F n‖ := by rw [key]
    _ ≤ 2 * Real.sqrt M * Real.log M := hrest

end Work.BMF.pcsw
