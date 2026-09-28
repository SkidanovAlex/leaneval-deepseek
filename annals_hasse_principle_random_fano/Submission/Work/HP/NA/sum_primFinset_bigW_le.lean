import Mathlib
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.sum_primFinset_prod
import Submission.Work.HP.NA.prod_prime_bound
import Submission.Work.HP.bigW_le_pow

/-!
# The `-κ`-moment of `σ(·; W)` is bounded by `W^{N} · exp (5 C₁)`

Let `W = bigW w = ∏_{p ≤ w} p^{r_p(w)}` with `r_p(w) = ⌈log_p w⌉ + 1`, the non-Archimedean
modulus.  Assuming that at every prime `p` and every `r ≥ 1` the `-κ`-moment of `σ(·; p^r)` is at
most `p^{r N} (1 + C₁ / p^{5/4})` (`N = NN d n`), we show that the corresponding moment over `W`
is at most `W^N · exp (5 C₁)`.

The proof is the Euler product.  Writing `W = ∏ᵢ Qᵢ` with `Qᵢ = pᵢ^{r_{pᵢ}}` (pairwise coprime
prime powers) and applying the Chinese-remainder multiplicativity of `σ`
(`sum_primFinset_prod`), the moment over `W` factorises as the product over the primes of the
individual moments.  Bounding each factor with the hypothesis gives a factor
`∏_{p ≤ w} p^{r_p N} = W^N` and a factor `∏_{p ≤ w} (1 + C₁/p^{5/4}) ≤ exp (5 C₁)`
(`prod_prime_bound`).
-/

open Finset
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.HP.NA

theorem sum_primFinset_bigW_le (d n : ℕ) (C₁ : ℝ) (hC₁ : 0 < C₁) (w : ℝ) [NeZero (Work.HP.bigW w)] (κ : ℝ) (hκ : 0 < κ)
    (hper : ∀ (p r : ℕ) [NeZero (p ^ r)], p.Prime → 1 ≤ r →
      (∑ a ∈ Work.HP.NA.primFinset d n (p ^ r), (Work.HP.NA.sigQ d n (p ^ r) a) ^ (-κ))
        ≤ (p : ℝ) ^ (r * Work.HP.NN d n) * (1 + C₁ / (p : ℝ) ^ ((5:ℝ)/4))) :
    (∑ a ∈ Work.HP.NA.primFinset d n (Work.HP.bigW w), (Work.HP.NA.sigQ d n (Work.HP.bigW w) a) ^ (-κ))
      ≤ (Work.HP.bigW w : ℝ) ^ (Work.HP.NN d n) * Real.exp (5 * C₁) := by
  classical
  set s : Finset ℕ := (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime with hs
  -- `σ` is a density, hence nonnegative.
  have hsigQnn : ∀ (q : ℕ) (a : Mon d n → ZMod q), 0 ≤ sigQ d n q a := by
    intro q a; rw [sigQ]; exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  -- Every factor `p^{r_p(w)}` occurring in `W` is nonzero (`p` prime, `r_p(w) ≥ 1`).
  have hpow_ne : ∀ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w ≠ 0 := fun i =>
    (pow_pos (Nat.Prime.pos (Finset.mem_filter.mp i.2).2) _).ne'
  haveI hNe : ∀ i : {p : ℕ // p ∈ s}, NeZero (i.1 ^ rOf i.1 w) := fun i => ⟨hpow_ne i⟩
  -- `W` as a product indexed by the subtype of primes `p ≤ w`.
  have hW : bigW w = ∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w := by
    rw [Work.HP.bigW, ← hs]
    exact (Finset.prod_attach s (fun p => p ^ rOf p w)).symm
  haveI hNeprod : NeZero (∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w) := by
    rw [← hW]; infer_instance
  -- Distinct primes give coprime prime powers.
  have hcop : ∀ i j : {p : ℕ // p ∈ s}, i ≠ j →
      Nat.Coprime (i.1 ^ rOf i.1 w) (j.1 ^ rOf j.1 w) := by
    intro i j hij
    have hpi : Nat.Prime i.1 := (Finset.mem_filter.mp i.2).2
    have hpj : Nat.Prime j.1 := (Finset.mem_filter.mp j.2).2
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hcopij : Nat.Coprime i.1 j.1 := (hpi.coprime_iff_not_dvd).mpr (fun hd => by
      rcases (Nat.dvd_prime hpj).mp hd with h1 | h2
      · exact hpi.ne_one h1
      · exact hne h2)
    exact hcopij.pow _ _
  -- Euler product (Chinese-remainder multiplicativity of the `-κ`-moment).
  have hE := sum_primFinset_prod (fun i : {p : ℕ // p ∈ s} => i.1 ^ rOf i.1 w) hcop d n κ
  -- The bound for the modulus written as the product `∏ᵢ Qᵢ`.
  have key : (∑ a ∈ primFinset d n (∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w),
        (sigQ d n (∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w) a) ^ (-κ))
      ≤ (((∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w : ℕ)) : ℝ) ^ (NN d n) * Real.exp (5 * C₁) := by
    rw [hE]
    -- Termwise bound of each prime factor.
    have hGleB : (∏ i : {p : ℕ // p ∈ s},
          (∑ a ∈ primFinset d n (i.1 ^ rOf i.1 w), (sigQ d n (i.1 ^ rOf i.1 w) a) ^ (-κ)))
        ≤ ∏ i : {p : ℕ // p ∈ s},
            ((i.1 : ℝ) ^ (rOf i.1 w * NN d n) * (1 + C₁ / (i.1 : ℝ) ^ ((5:ℝ)/4))) := by
      refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
      · exact Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (hsigQnn (i.1 ^ rOf i.1 w) a) _)
      · have hpp : Nat.Prime i.1 := (Finset.mem_filter.mp i.2).2
        have hr : 1 ≤ rOf i.1 w := by simp only [Work.HP.rOf]; exact Nat.le_add_left 1 _
        exact hper i.1 (rOf i.1 w) hpp hr
    -- `∏_{p ≤ w} p^{r_p N} = W^N`.
    have hA : (∏ i : {p : ℕ // p ∈ s}, (i.1 : ℝ) ^ (rOf i.1 w * NN d n))
        = (((∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w : ℕ)) : ℝ) ^ (NN d n) := by
      rw [show (∏ i : {p : ℕ // p ∈ s}, (i.1 : ℝ) ^ (rOf i.1 w * NN d n))
          = ∏ i : {p : ℕ // p ∈ s}, ((i.1 : ℝ) ^ (rOf i.1 w)) ^ (NN d n) from
        Finset.prod_congr rfl (fun i _ => pow_mul _ _ _)]
      rw [Finset.prod_pow]
      congr 1
      push_cast
      rfl
    -- `∏_{p ≤ w} (1 + C₁ / p^{5/4}) ≤ exp (5 C₁)`.
    have hB2 : (∏ i : {p : ℕ // p ∈ s}, (1 + C₁ / (i.1 : ℝ) ^ ((5:ℝ)/4)))
        ≤ Real.exp (5 * C₁) := by
      rw [show (∏ i : {p : ℕ // p ∈ s}, (1 + C₁ / (i.1 : ℝ) ^ ((5:ℝ)/4)))
          = ∏ p ∈ s, (1 + C₁ / (p : ℝ) ^ ((5:ℝ)/4)) from
        (Finset.prod_attach s (fun p => 1 + C₁ / (p : ℝ) ^ ((5:ℝ)/4)))]
      simpa only [hs] using prod_prime_bound C₁ hC₁ w
    refine le_trans hGleB ?_
    rw [Finset.prod_mul_distrib, hA]
    exact mul_le_mul_of_nonneg_left hB2 (pow_nonneg (Nat.cast_nonneg _) _)
  -- Transport `key` from the product modulus to `bigW w` (the `NeZero` instance of `primFinset`
  -- depends on the modulus, so abstract it explicitly).
  have keyGen : ∀ h : NeZero (∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w),
      (∑ a ∈ @primFinset d n (∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w) h,
          (sigQ d n (∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w) a) ^ (-κ))
        ≤ (((∏ i : {p : ℕ // p ∈ s}, i.1 ^ rOf i.1 w : ℕ)) : ℝ) ^ (NN d n)
            * Real.exp (5 * C₁) := fun _ => key
  exact (hW.symm ▸ keyGen) inferInstance

end Work.HP.NA
