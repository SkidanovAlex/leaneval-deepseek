import Mathlib
import Submission.Work.Tower.APDensity.Basic

/-!
# A dyadic bound for the prime part of the `Λ₁` Dirichlet series

`LambdaOne` is the von Mangoldt function restricted to the residue class `1 mod 3`.
Here we bound the associated Dirichlet series at the exponent `1 + δ`, using only
the prime part:

`∑_{p prime, p ≡ 1 mod 3} log p / p ^ (1 + δ) ≤ (dyadic estimate)`.

The proof decomposes the sum into dyadic blocks `[2^k, 2^(k+1))`.  On the blocks up to
`M` and beyond `M^A` we use Chebyshev's bound `θ(x) ≤ x log 4`; in between we use the
hypothesis that the progression has few primes (`goodPrimeSum N ≤ ε N`).
-/

namespace Work.Tower.APDensity.Analytic

open Work.Tower

section
variable {δ : ℝ}

/-- The summand `(if n.Prime then Λ₁ n else 0) / n ^ (1 + δ)` is nonnegative. -/
private lemma summand_nonneg (n : ℕ) :
    0 ≤ (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ (1 + δ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnum : 0 ≤ (if n.Prime then LambdaOne n else 0) := by
      split_ifs with h
      · exact lambdaOne_nonneg n
      · exact le_rfl
    exact div_nonneg hnum (Real.rpow_nonneg hnpos.le _)

/-- On a dyadic block, each summand is at most the prime part times `2 ^ (-(1+δ) k)`. -/
private lemma summand_le_block {k n : ℕ} (hδ : 0 ≤ δ)
    (hn : n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ)) :
    (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ (1 + δ)
      ≤ (if n.Prime then LambdaOne n else 0) * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) := by
  have hn1 : 1 ≤ n := Nat.one_le_two_pow.trans (Finset.mem_Ico.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnum : 0 ≤ (if n.Prime then LambdaOne n else 0) := by
    split_ifs with h
    · exact lambdaOne_nonneg n
    · exact le_rfl
  have hle := rpow_neg_le_of_mem_Ico_two_pow (n := n) (k := k) (x := 1 + δ)
    (by linarith) hn
  rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
  exact mul_le_mul_of_nonneg_left hle hnum

/-- Sum over a dyadic block, bounded by `primeBlock k * 2 ^ (-(1+δ) k)`. -/
private lemma block_sum_le (k : ℕ) (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
        (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ (1 + δ))
      ≤ primeBlock k * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) := by
  rw [primeBlock, Finset.sum_mul]
  exact Finset.sum_le_sum fun n hn => summand_le_block hδ hn

/-- Chebyshev's bound for the prime part of a dyadic block. -/
private lemma primeBlock_le_log4 (k : ℕ) :
    primeBlock k ≤ Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ) :=
  (primeBlock_le_theta k).trans (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _))

/-- Algebraic bookkeeping: `2 ^ (-(1+δ) k) * 2 ^ (k+1) = 2 * (2 ^ (-δ)) ^ k`. -/
private lemma two_rpow_mul_two_pow (k : ℕ) :
    (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) * ((2 ^ (k + 1) : ℕ) : ℝ)
      = 2 * ((2 : ℝ) ^ (-δ)) ^ k := by
  have h1 : (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) = ((2 : ℝ) ^ (-(1 + δ))) ^ k :=
    two_rpow_neg_mul_nat (1 + δ) k
  have h2 : (2 : ℝ) ^ (-(1 + δ)) * 2 = (2 : ℝ) ^ (-δ) := by
    have h := Real.rpow_add (show (0 : ℝ) < 2 by norm_num) (-(1 + δ)) 1
    rw [Real.rpow_one] at h
    rw [← h, show (-(1 + δ) + 1 : ℝ) = -δ by ring]
  have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  rw [hcast, h1, pow_succ, ← mul_assoc, ← mul_pow, h2]
  ring

/-- The same identity in the order in which it is applied below. -/
private lemma two_pow_mul_two_rpow (k : ℕ) :
    ((2 ^ (k + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ)))
      = 2 * ((2 : ℝ) ^ (-δ)) ^ k := by
  rw [mul_comm, two_rpow_mul_two_pow]

/-- Blocks well below `M` contribute at most `2 log 4` each. -/
private lemma block_sum_le_small (k : ℕ) (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
        (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ (1 + δ))
      ≤ 2 * Real.log 4 := by
  refine (block_sum_le k hδ).trans ?_
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc primeBlock k * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ)))
      ≤ (Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ)) * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right (primeBlock_le_log4 k) hB
    _ = Real.log 4 * (2 * ((2 : ℝ) ^ (-δ)) ^ k) := by
        rw [mul_assoc, two_pow_mul_two_rpow k]
    _ ≤ Real.log 4 * (2 * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hlog4
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ (a := (2 : ℝ) ^ (-δ)) (n := k)
            (Real.rpow_nonneg (by norm_num) _) (two_rpow_neg_le_one hδ))
          (by norm_num : (0 : ℝ) ≤ 2)
    _ = 2 * Real.log 4 := by ring

/-- Blocks far above `M ^ A` contribute a geometric amount. -/
private lemma block_sum_le_tail (k : ℕ) (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
        (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ (1 + δ))
      ≤ 2 * Real.log 4 * ((2 : ℝ) ^ (-δ)) ^ k := by
  refine (block_sum_le k hδ).trans ?_
  have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc primeBlock k * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ)))
      ≤ (Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ)) * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right (primeBlock_le_log4 k) hB
    _ = Real.log 4 * (2 * ((2 : ℝ) ^ (-δ)) ^ k) := by
        rw [mul_assoc, two_pow_mul_two_rpow k]
    _ = 2 * Real.log 4 * ((2 : ℝ) ^ (-δ)) ^ k := by ring

/-- Blocks in the range where the hypothesis on `goodPrimeSum` applies. -/
private lemma block_sum_le_middle {A ε M : ℝ} (hM : 1 ≤ M) (hA : 1 ≤ A) (_hε : 0 ≤ ε)
    (hbad : ∀ N : ℕ, M ≤ (N : ℝ) → (N : ℝ) ≤ M ^ A → goodPrimeSum N ≤ ε * N)
    {K₁ K₂ : ℕ} (hK₁ : K₁ = Nat.log 2 ⌊M⌋₊) (hK₂ : K₂ = Nat.log 2 ⌊M ^ A⌋₊)
    {k : ℕ} (hk₁ : K₁ < k) (hk₂ : k < K₂) (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ),
        (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ (1 + δ))
      ≤ 2 * ε * ((2 : ℝ) ^ (-δ)) ^ k := by
  have hMA1 : (1 : ℝ) ≤ M ^ A := Real.one_le_rpow hM (by linarith)
  have hMA0 : (0 : ℝ) < M ^ A := lt_of_lt_of_le one_pos hMA1
  have hK₂pow : (2 : ℝ) ^ K₂ ≤ M ^ A := by
    rw [hK₂]
    have hne : ⌊M ^ A⌋₊ ≠ 0 := by
      have : (1 : ℕ) ≤ ⌊M ^ A⌋₊ := (Nat.le_floor_iff hMA0.le).mpr (by exact_mod_cast hMA1)
      omega
    have h := Nat.pow_log_le_self 2 hne
    calc (2 : ℝ) ^ Nat.log 2 ⌊M ^ A⌋₊ = ((2 ^ Nat.log 2 ⌊M ^ A⌋₊ : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ (⌊M ^ A⌋₊ : ℝ) := by exact_mod_cast h
      _ ≤ M ^ A := Nat.floor_le hMA0.le
  have hMle : M ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
    have hK₁lt : ⌊M⌋₊ < 2 ^ (K₁ + 1) := by
      rw [hK₁]
      exact Nat.lt_pow_succ_log_self (by norm_num) ⌊M⌋₊
    have h₁ : M ≤ ((⌊M⌋₊ : ℕ) : ℝ) + 1 := by
      simpa using (Nat.lt_succ_floor M).le
    calc M ≤ ((⌊M⌋₊ : ℕ) : ℝ) + 1 := h₁
      _ = ((⌊M⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (K₁ + 1) : ℕ) : ℝ) := by exact_mod_cast hK₁lt
      _ ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
          rw [show ((2 ^ (K₁ + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (K₁ + 1) by push_cast; ring,
            show ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) by push_cast; ring]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hleMA : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ M ^ A := by
    have hk1 : k + 1 ≤ K₂ := by omega
    calc ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
      _ ≤ (2 : ℝ) ^ K₂ := pow_le_pow_right₀ (by norm_num) hk1
      _ ≤ M ^ A := hK₂pow
  have hgood : goodPrimeSum (2 ^ (k + 1)) ≤ ε * ((2 ^ (k + 1) : ℕ) : ℝ) := hbad _ hMle hleMA
  refine (block_sum_le k hδ).trans ?_
  calc primeBlock k * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ)))
      ≤ (ε * ((2 ^ (k + 1) : ℕ) : ℝ)) * (2 : ℝ) ^ (-((1 + δ) * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right ((primeBlock_le_goodPrimeSum k).trans hgood)
          (Real.rpow_nonneg (by norm_num) _)
    _ = 2 * ε * ((2 : ℝ) ^ (-δ)) ^ k := by
        rw [mul_assoc, two_pow_mul_two_rpow k]; ring

/-- The geometric factor attached to the first block beyond `M ^ A`. -/
private lemma rpow_pow_tail_le {A M : ℝ} (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {K₂ : ℕ} (hK₂ : K₂ = Nat.log 2 ⌊M ^ A⌋₊) :
    ((2 : ℝ) ^ (-δ)) ^ K₂ ≤ 2 * Real.exp (-(δ * A * Real.log M)) := by
  have hMA1 : (1 : ℝ) ≤ M ^ A := Real.one_le_rpow hM (by linarith)
  have hMA0 : (0 : ℝ) < M ^ A := lt_of_lt_of_le one_pos hMA1
  have hM0 : (0 : ℝ) < M := by linarith
  have hlt : M ^ A < (2 : ℝ) ^ (K₂ + 1) := by
    rw [hK₂]
    have hnat : ⌊M ^ A⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊M ^ A⌋₊ + 1) := by
      have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) ⌊M ^ A⌋₊
      simpa [Nat.succ_eq_add_one] using h
    calc M ^ A < ((⌊M ^ A⌋₊ : ℕ) : ℝ) + 1 := by
          simpa [Nat.succ_eq_add_one] using Nat.lt_succ_floor (M ^ A)
      _ = ((⌊M ^ A⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (Nat.log 2 ⌊M ^ A⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊M ^ A⌋₊ + 1) := by push_cast; ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : A * Real.log M ≤ ((K₂ : ℝ) + 1) * Real.log 2 := by
    have h1 : Real.log (M ^ A) ≤ Real.log ((2 : ℝ) ^ (K₂ + 1)) := Real.log_le_log hMA0 hlt.le
    rw [Real.log_rpow hM0, Real.log_pow] at h1
    have hcast : ((K₂ + 1 : ℕ) : ℝ) = (K₂ : ℝ) + 1 := by push_cast; ring
    rwa [hcast] at h1
  have hmain : -(δ * (K₂ : ℝ) * Real.log 2) ≤ Real.log 2 + -(δ * A * Real.log M) := by
    have h1 : δ * (A * Real.log M) ≤ δ * (((K₂ : ℝ) + 1) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlog hδ.le
    have h2 : δ * Real.log 2 ≤ Real.log 2 := by
      calc δ * Real.log 2 ≤ 1 * Real.log 2 := mul_le_mul_of_nonneg_right hδ1 hlog2.le
        _ = Real.log 2 := one_mul _
    nlinarith [h1, h2]
  rw [← two_rpow_neg_mul_nat δ K₂, two_rpow_neg_eq_exp]
  calc Real.exp (-(δ * (K₂ : ℝ) * Real.log 2))
      ≤ Real.exp (Real.log 2 + -(δ * A * Real.log M)) := Real.exp_le_exp.mpr hmain
    _ = 2 * Real.exp (-(δ * A * Real.log M)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end

theorem primePart_tsum_le {A ε δ M : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbad : ∀ N : ℕ, M ≤ (N : ℝ) → (N : ℝ) ≤ M ^ A → Work.Tower.goodPrimeSum N ≤ ε * N) :
    ∑' n : ℕ, (if n.Prime then Work.Tower.LambdaOne n else 0) / (n : ℝ) ^ (1 + δ) ≤
      2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1)
        + 2 * ε / (1 - (2 : ℝ) ^ (-δ))
        + 4 * Real.log 4 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)) := by
  set K₁ : ℕ := Nat.log 2 ⌊M⌋₊ with hK₁
  set K₂ : ℕ := Nat.log 2 ⌊M ^ A⌋₊ with hK₂
  set f : ℕ → ℝ := fun n => (if n.Prime then LambdaOne n else 0) / (n : ℝ) ^ (1 + δ) with hf
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-δ) := Real.rpow_nonneg (by norm_num) _
  have hrlt : (2 : ℝ) ^ (-δ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hrpos : (0 : ℝ) < 1 - (2 : ℝ) ^ (-δ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsumm : Summable f := by rw [hf]; exact summable_primePart_div_rpow (by linarith)
  have hfnn : ∀ n, 0 ≤ f n := by intro n; rw [hf]; exact summand_nonneg n
  have key : ∀ L : ℕ, ∑ n ∈ Finset.range (2 ^ L), f n
      ≤ 2 * Real.log 4 * ((K₁ : ℝ) + 1) + 2 * ε / (1 - (2 : ℝ) ^ (-δ))
        + 4 * Real.log 4 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)) := by
    intro L
    have h2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hsplit : ∑ n ∈ Finset.range (2 ^ L), f n = ∑ n ∈ Finset.Ico 1 (2 ^ L), f n := by
      have hdisj : Disjoint (Finset.Ico 0 1) (Finset.Ico 1 (2 ^ L)) :=
        Finset.disjoint_left.mpr fun x hx hx' => by
          rw [Finset.mem_Ico] at hx hx'; omega
      rw [Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le 1) h2L,
        Finset.sum_union hdisj]
      have hzero : ∑ n ∈ Finset.Ico 0 1, f n = 0 := by
        rw [← Finset.range_eq_Ico, Finset.range_one, Finset.sum_singleton, hf]
        simp [Nat.not_prime_zero]
      rw [hzero, zero_add]
    rw [hsplit, sum_Ico_one_two_pow_eq_sum_blocks f L]
    let g : ℕ → ℝ := fun k => ∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ), f n
    have hg : ∀ k, g k = ∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ), f n := fun k => rfl
    rw [show (∑ k ∈ Finset.range L, ∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1) : ℕ), f n)
        = ∑ k ∈ Finset.range L, g k from
      Finset.sum_congr rfl fun k _ => (hg k).symm]
    have hsmall : ∀ k, k ≤ K₁ → g k ≤ 2 * Real.log 4 := by
      intro k _
      rw [hg k, hf]
      exact block_sum_le_small (δ := δ) k hδ.le
    have hmid : ∀ k, ¬ k ≤ K₁ → k < K₂ → g k ≤ 2 * ε * ((2 : ℝ) ^ (-δ)) ^ k := by
      intro k hk1 hk2
      rw [hg k, hf]
      exact block_sum_le_middle (δ := δ) hM hA hε hbad hK₁ hK₂ (Nat.lt_of_not_le hk1) hk2 hδ.le
    have htail : ∀ k, ¬ k < K₂ → g k ≤ 2 * Real.log 4 * ((2 : ℝ) ^ (-δ)) ^ k := by
      intro k _
      rw [hg k, hf]
      exact block_sum_le_tail (δ := δ) k hδ.le
    have h1 : ∑ k ∈ (Finset.range L).filter (fun k => k ≤ K₁), g k
        + ∑ k ∈ (Finset.range L).filter (fun k => ¬ k ≤ K₁), g k
          = ∑ k ∈ Finset.range L, g k := Finset.sum_filter_add_sum_filter_not _ _ _
    have h2 : ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => k < K₂), g k
        + ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => ¬ k < K₂), g k
          = ∑ k ∈ (Finset.range L).filter (fun k => ¬ k ≤ K₁), g k :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [← h1, ← h2]
    have hA_sub : (Finset.range L).filter (fun k => k ≤ K₁) ⊆ Finset.range (K₁ + 1) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      omega
    have hsum1 : ∑ k ∈ (Finset.range L).filter (fun k => k ≤ K₁), g k
        ≤ 2 * Real.log 4 * ((K₁ : ℝ) + 1) := by
      have hcard : ((Finset.range L).filter (fun k => k ≤ K₁)).card ≤ K₁ + 1 :=
        (Finset.card_le_card hA_sub).trans_eq (Finset.card_range (K₁ + 1))
      calc ∑ k ∈ (Finset.range L).filter (fun k => k ≤ K₁), g k
          ≤ ∑ _k ∈ (Finset.range L).filter (fun k => k ≤ K₁), (2 * Real.log 4) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hsmall k (Finset.mem_filter.mp hk).2
        _ = (((Finset.range L).filter (fun k => k ≤ K₁)).card : ℝ) * (2 * Real.log 4) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((K₁ + 1 : ℕ) : ℝ) * (2 * Real.log 4) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
              (mul_nonneg (by norm_num) hlog4)
        _ = 2 * Real.log 4 * ((K₁ : ℝ) + 1) := by push_cast; ring
    have hB_sub : ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => k < K₂)
        ⊆ Finset.Ico (K₁ + 1) K₂ := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hk ⊢
      omega
    have hsum2 : ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => k < K₂), g k
        ≤ 2 * ε / (1 - (2 : ℝ) ^ (-δ)) := by
      have hne : (0 : ℝ) ≤ 2 * ε := mul_nonneg (by norm_num) hε
      calc ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => k < K₂), g k
          ≤ ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => k < K₂),
              (2 * ε * ((2 : ℝ) ^ (-δ)) ^ k) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk2 : k < K₂ := (Finset.mem_filter.mp hk).2
            have hk1 : ¬ k ≤ K₁ := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
            exact hmid k hk1 hk2
        _ = 2 * ε * ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => k < K₂),
              ((2 : ℝ) ^ (-δ)) ^ k := by rw [Finset.mul_sum]
        _ ≤ 2 * ε * ∑ k ∈ Finset.Ico (K₁ + 1) K₂, ((2 : ℝ) ^ (-δ)) ^ k := by
            refine mul_le_mul_of_nonneg_left ?_ hne
            exact Finset.sum_le_sum_of_subset_of_nonneg hB_sub (fun k _ _ => pow_nonneg hr0 k)
        _ ≤ 2 * ε * (((2 : ℝ) ^ (-δ)) ^ (K₁ + 1) / (1 - (2 : ℝ) ^ (-δ))) := by
            refine mul_le_mul_of_nonneg_left ?_ hne
            exact geom_sum_Ico_le hr0 hrlt (K₁ + 1) K₂
        _ ≤ 2 * ε * (1 / (1 - (2 : ℝ) ^ (-δ))) := by
            refine mul_le_mul_of_nonneg_left ?_ hne
            rw [div_le_div_iff_of_pos_right hrpos]
            exact pow_le_one₀ (a := (2 : ℝ) ^ (-δ)) (n := K₁ + 1) hr0 (two_rpow_neg_le_one hδ.le)
        _ = 2 * ε / (1 - (2 : ℝ) ^ (-δ)) := by ring
    have hC_sub : ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => ¬ k < K₂)
        ⊆ Finset.Ico K₂ L := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hk ⊢
      omega
    have hsum3 : ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => ¬ k < K₂), g k
        ≤ 4 * Real.log 4 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)) := by
      have hlog4' : (0 : ℝ) ≤ 2 * Real.log 4 := mul_nonneg (by norm_num) hlog4
      have htb := rpow_pow_tail_le (δ := δ) hM hA hδ hδ1 hK₂
      calc ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => ¬ k < K₂), g k
          ≤ ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter (fun k => ¬ k < K₂),
              (2 * Real.log 4 * ((2 : ℝ) ^ (-δ)) ^ k) := by
            apply Finset.sum_le_sum
            intro k hk
            exact htail k (Finset.mem_filter.mp hk).2
        _ = 2 * Real.log 4 * ∑ k ∈ ((Finset.range L).filter (fun k => ¬ k ≤ K₁)).filter
              (fun k => ¬ k < K₂), ((2 : ℝ) ^ (-δ)) ^ k := by rw [Finset.mul_sum]
        _ ≤ 2 * Real.log 4 * ∑ k ∈ Finset.Ico K₂ L, ((2 : ℝ) ^ (-δ)) ^ k := by
            refine mul_le_mul_of_nonneg_left ?_ hlog4'
            exact Finset.sum_le_sum_of_subset_of_nonneg hC_sub (fun k _ _ => pow_nonneg hr0 k)
        _ ≤ 2 * Real.log 4 * (((2 : ℝ) ^ (-δ)) ^ K₂ / (1 - (2 : ℝ) ^ (-δ))) := by
            refine mul_le_mul_of_nonneg_left ?_ hlog4'
            exact geom_sum_Ico_le hr0 hrlt K₂ L
        _ ≤ 2 * Real.log 4 * (2 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ))) := by
            refine mul_le_mul_of_nonneg_left ?_ hlog4'
            rw [div_le_div_iff_of_pos_right hrpos]
            exact htb
        _ = 4 * Real.log 4 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)) := by ring
    have hcomb : 2 * Real.log 4 * ((K₁ : ℝ) + 1) + 2 * ε / (1 - (2 : ℝ) ^ (-δ))
        + 4 * Real.log 4 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ))
        = 2 * Real.log 4 * ((K₁ : ℝ) + 1) + (2 * ε / (1 - (2 : ℝ) ^ (-δ))
          + 4 * Real.log 4 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ))) := by
      ring
    linarith [hsum1, hsum2, hsum3, hcomb]
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n
      ≤ 2 * Real.log 4 * ((K₁ : ℝ) + 1) + 2 * ε / (1 - (2 : ℝ) ^ (-δ))
        + 4 * Real.log 4 * Real.exp (-(δ * A * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)) := by
    intro N
    have hsub : Finset.range N ⊆ Finset.range (2 ^ N) := by
      intro n hn
      simp only [Finset.mem_range] at hn ⊢
      exact lt_of_lt_of_le hn Nat.lt_two_pow_self.le
    calc ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range (2 ^ N), f n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hfnn i)
      _ ≤ _ := key N
  exact le_of_tendsto hsumm.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hpartial)

end Work.Tower.APDensity.Analytic
