import ChallengeDeps
import Mathlib.Tactic
import Submission.Basic

/-!
# Reduction to the "upper half" averages (Krause--Mirek--Tao, Proposition 3.1(iii))

Following Krause--Mirek--Tao we introduce the *upper half* average
`Ã_m = (1/m) ∑_{⌊m/2⌋ < n ≤ m} f(T^{P₁(n)}x) g(T^{P₂(n)}x)`
and prove the dyadic telescoping identity expressing the ordinary average `A_N` as a
weighted sum of the averages `Ã_{⌊N⌋/2^k}`.  This is the technical reduction that allows
one to assume good lower bounds on the derivatives of the polynomials.
-/

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The unnormalised "upper half" block sum
`∑_{⌊m/2⌋ < n ≤ m} f(T^{P₁(n)}x) g(T^{P₂(n)}x)`. -/
noncomputable def Ablock (T : 𝓧 ≃ᵐ 𝓧) (m : ℕ) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) : ℂ :=
  ∑ n ∈ Finset.Ioc (m / 2) m,
    f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)

/-- The "upper half" average
`Ã_m = (1/m) ∑_{⌊m/2⌋ < n ≤ m} f(T^{P₁(n)}x) g(T^{P₂(n)}x)`. -/
noncomputable def Ahalf (T : 𝓧 ≃ᵐ 𝓧) (m : ℕ) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) : ℂ :=
  (m : ℝ)⁻¹ * Ablock T m P₁ P₂ f g x

/-- The dyadic block decomposition of the halved blocks: `⌊m/2⌋ / 2 = ⌊m/4⌋`; the blocks of the
telescoping identity tile `{1, …, ⌊N⌋}`. -/
lemma div_two_div (n k : ℕ) : (n / 2 ^ k) / 2 = n / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-- Dyadic block decomposition of a sum over `{1, …, N}` into the blocks
`(N / 2 ^ (k+1), N / 2 ^ k]`, `k = 0, …, log2 N`.  This is a local copy of
`Commons.Analysis.Sum.dyadic_block_decomposition`, kept here so that the file does not pull in
the heavy Mathlib imports of the shared copy (which perturb instance resolution and break the
statement comparison of the challenge). -/
lemma sum_Icc_eq_sum_Ioc_dyadic (c : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, c n
      = ∑ k ∈ Finset.range (Nat.log2 N + 1),
          ∑ n ∈ Finset.Ioc (N / 2 ^ (k + 1)) (N / 2 ^ k), c n := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hpow : N < 2 ^ (Nat.log2 N + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    simpa [Nat.log2_eq_log_two] using h
  have hlast : N / 2 ^ (Nat.log2 N + 1) = 0 := Nat.div_eq_of_lt hpow
  have hmono : ∀ k : ℕ, N / 2 ^ (k + 1) ≤ N / 2 ^ k := by
    intro k
    exact Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
      (by positivity)
  have hblock : ∀ a b : ℕ, a ≤ b →
      ∑ n ∈ Finset.Ioc a b, c n
        = (∑ n ∈ Finset.Ioc 0 b, c n) - (∑ n ∈ Finset.Ioc 0 a, c n) := by
    intro a b hab
    have hsub : Finset.Ioc 0 a ⊆ Finset.Ioc 0 b := by
      intro n hn
      simp only [Finset.mem_Ioc] at hn ⊢
      omega
    have hdiff : Finset.Ioc 0 b \ Finset.Ioc 0 a = Finset.Ioc a b := by
      ext n; simp only [Finset.mem_sdiff, Finset.mem_Ioc]; omega
    have h := Finset.sum_sdiff (f := c) hsub
    rw [hdiff] at h
    exact eq_sub_of_add_eq h
  set t : ℕ → ℂ := fun k => ∑ n ∈ Finset.Ioc 0 (N / 2 ^ k), c n with ht
  have htel : ∑ k ∈ Finset.range (Nat.log2 N + 1), (t k - t (k + 1))
      = ∑ n ∈ Finset.Ioc 0 N, c n := by
    have h1 := Finset.sum_range_sub t (Nat.log2 N + 1)
    have h2 : (∑ k ∈ Finset.range (Nat.log2 N + 1), (t k - t (k + 1)))
        = - ∑ k ∈ Finset.range (Nat.log2 N + 1), (t (k + 1) - t k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have ht0 : t 0 = ∑ n ∈ Finset.Ioc 0 N, c n := by simp [ht]
    have htm : t (Nat.log2 N + 1) = 0 := by simp [ht, hlast]
    rw [h2, h1, ht0, htm]
    ring
  calc ∑ n ∈ Finset.Icc 1 N, c n
      = ∑ n ∈ Finset.Ioc 0 N, c n := by rw [hIcc]
      _ = ∑ k ∈ Finset.range (Nat.log2 N + 1), (t k - t (k + 1)) := htel.symm
      _ = ∑ k ∈ Finset.range (Nat.log2 N + 1),
            ∑ n ∈ Finset.Ioc (N / 2 ^ (k + 1)) (N / 2 ^ k), c n := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hblock (N / 2 ^ (k + 1)) (N / 2 ^ k) (hmono k)]

/-- The block appearing in the telescoping identity is `Ablock`. -/
lemma Ablock_eq (T : 𝓧 ≃ᵐ 𝓧) (n k : ℕ) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) :
    Ablock T (n / 2 ^ k) P₁ P₂ f g x
      = ∑ i ∈ Finset.Ioc (n / 2 ^ (k + 1)) (n / 2 ^ k),
          f ((T ^ (P₁.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x) := by
  rw [Ablock, div_two_div]

/-- **Coefficient identity.**  A coefficient `⌊n/2^k⌋/n` applied to the halved average `Ã_{⌊n/2^k⌋}`
is the factor `1/n` applied to the halved block sum. -/
lemma coef_mul_Ahalf (T : 𝓧 ≃ᵐ 𝓧) {n m : ℕ} (hn : n ≠ 0) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ)
    (x : 𝓧) :
    ((m : ℝ) / (n : ℝ)) * Ahalf T m P₁ P₂ f g x
      = (n : ℝ)⁻¹ * Ablock T m P₁ P₂ f g x := by
  rw [Ahalf]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Ablock, Finset.Ioc_self]; simp
  · have hmC : (m : ℂ) ≠ 0 := by simp [hm]
    have hnC : (n : ℂ) ≠ 0 := by simp [hn]
    push_cast
    field_simp

/-- **Dyadic telescoping identity** (Krause--Mirek--Tao, Proposition 3.1(iii)).  The ordinary
bilinear average at scale `N` is the average over the dyadic blocks of the halved averages:
`A_N = ∑_k (⌊N/2^k⌋/⌊N⌋) Ã_{⌊N/2^k⌋}`. -/
lemma A_eq_sum_Ahalf (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧)
    (hN : 1 ≤ Nat.floor N) :
    A T N P₁ P₂ f g x
      = ∑ k ∈ Finset.range (Nat.log2 (Nat.floor N) + 1),
          ((Nat.floor N / 2 ^ k : ℕ) : ℝ) / (Nat.floor N : ℝ)
            * Ahalf T (Nat.floor N / 2 ^ k) P₁ P₂ f g x := by
  have hN0 : Nat.floor N ≠ 0 := by omega
  have hA : A T N P₁ P₂ f g x = (Nat.floor N : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 (Nat.floor N),
      f ((T ^ (P₁.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x) := rfl
  rw [hA]
  have h1 : ∑ i ∈ Finset.Icc 1 (Nat.floor N),
        f ((T ^ (P₁.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x)
      = ∑ k ∈ Finset.range (Nat.log2 (Nat.floor N) + 1),
          Ablock T (Nat.floor N / 2 ^ k) P₁ P₂ f g x := by
    rw [sum_Icc_eq_sum_Ioc_dyadic
      (fun i => f ((T ^ (P₁.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x)
        * g ((T ^ (P₂.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x)) hN]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Ablock_eq]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← coef_mul_Ahalf T hN0 P₁ P₂ f g x]

end PointwiseErgodicTheorems
end Submission
