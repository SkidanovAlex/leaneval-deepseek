/-
# The jump sum of a monotone chain is controlled by the `ℓ^r`-sum

`Work.KMTAreas.A7.chainSum_le_tsum` is the elementary "chain" estimate used in
`Work.KMTAreas.A7.variationalNorm_le_sqSum`: for a monotone chain `N : ℕ → ℕ`, an exponent `r ≥ 1`
and any `a : ℕ → ℂ`,

  `∑_{i<J} ‖a (N (i+1)) − a (N i)‖ₑ^r ≤ 2^r · ∑'_n ‖a n‖ₑ^r`.

The proof is elementary.  By `‖a (N (i+1)) − a (N i)‖ₑ ≤ ‖a (N (i+1))‖ₑ + ‖a (N i)‖ₑ` and
`(x + y)^r ≤ 2^{r-1} (x^r + y^r)` (`ENNReal.rpow_add_le_mul_rpow_add_rpow`, valid for `r ≥ 1`) each
term is at most `2^{r-1} (f (N (i+1)) + f (N i))` with `f n = ‖a n‖ₑ^r`.  The terms with
`N (i+1) = N i` vanish, and on the *jump* set `s = {i | N i < N (i+1)}` the maps
`i ↦ N i` and `i ↦ N (i+1)` are injective by monotonicity (`N i < N (i+1) ≤ N i' < N (i'+1)` for
`i < i'`); hence each of `∑_{i∈s} f (N i)` and `∑_{i∈s} f (N (i+1))` is at most the full tsum
`∑'_n f n`, and the total is `2^{r-1} · 2 · ∑'_n f n = 2^r ∑'_n f n`.
-/
import Mathlib

namespace Work.KMTAreas.A7

open scoped ENNReal BigOperators

/-- A sum of `f` along the values of an injective-on-`s` map `φ : ι → ℕ` is bounded by the full
`tsum` of `f` (all terms are nonnegative, in `ℝ≥0∞`). -/
private lemma sum_comp_le_tsum {ι : Type*} (s : Finset ι) (φ : ι → ℕ) (f : ℕ → ℝ≥0∞)
    (hφ : Set.InjOn φ ↑s) : ∑ i ∈ s, f (φ i) ≤ ∑' n : ℕ, f n := by
  rw [← Finset.sum_image (f := f) hφ]
  exact ENNReal.sum_le_tsum _

theorem chainSum_le_tsum {r : ℝ} (hr : 1 ≤ r) (a : ℕ → ℂ) {N : ℕ → ℕ} (hN : Monotone N) (J : ℕ) :
    ∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ r ≤ 2 ^ r * ∑' n : ℕ, ‖a n‖ₑ ^ r := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  set f : ℕ → ℝ≥0∞ := fun n => ‖a n‖ₑ ^ r with hf
  -- the set of jumps of the chain
  set s : Finset (Fin J) := Finset.univ.filter (fun i : Fin J => N i < N (i + 1)) with hs
  have hmem : ∀ i : Fin J, i ∈ s ↔ N i < N (i + 1) := by
    intro i; simp [hs]
  have hmono : ∀ i : Fin J, N i ≤ N (i + 1) := fun i => hN (Nat.le_succ (i : ℕ))
  -- a flat step contributes nothing
  have hzero : ∀ i : Fin J, ¬ (N i < N (i + 1)) →
      ‖a (N (i + 1)) - a (N i)‖ₑ ^ r = 0 := by
    intro i hi
    have heq : N i = N (i + 1) := le_antisymm (hmono i) (not_lt.mp hi)
    rw [← heq]
    simp [ENNReal.zero_rpow_of_pos hrpos]
  have hsum_eq : ∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ r
      = ∑ i ∈ s, ‖a (N (i + 1)) - a (N i)‖ₑ ^ r := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro x _ hx
    exact hzero x (fun hlt => hx ((hmem x).mpr hlt))
  -- the pointwise `2^{r-1}`-bound on the jump set
  have hbdd : ∑ i ∈ s, ‖a (N (i + 1)) - a (N i)‖ₑ ^ r
      ≤ 2 ^ (r - 1) * ∑ i ∈ s, (f (N (i + 1)) + f (N i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc ‖a (N (i + 1)) - a (N i)‖ₑ ^ r
        ≤ (‖a (N (i + 1))‖ₑ + ‖a (N i)‖ₑ) ^ r := ENNReal.rpow_le_rpow enorm_sub_le hr0
      _ ≤ 2 ^ (r - 1) * (‖a (N (i + 1))‖ₑ ^ r + ‖a (N i)‖ₑ ^ r) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
      _ = 2 ^ (r - 1) * (f (N (i + 1)) + f (N i)) := rfl
  -- monotonicity makes both endpoints maps injective on the jump set
  have hinjN : Set.InjOn (fun i : Fin J => N i) ↑s := by
    intro i hi j hj hij
    dsimp only at hij
    rcases lt_trichotomy i j with h | h | h
    · exfalso
      have h1 : N i < N (i + 1) := (hmem i).mp hi
      have h2 : N (i + 1) ≤ N j := hN (Nat.succ_le_of_lt (show (i : ℕ) < (j : ℕ) from h))
      rw [← hij] at h2
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    · exact h
    · exfalso
      have h1 : N j < N (j + 1) := (hmem j).mp hj
      have h2 : N (j + 1) ≤ N i := hN (Nat.succ_le_of_lt (show (j : ℕ) < (i : ℕ) from h))
      rw [hij] at h2
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
  have hinjS : Set.InjOn (fun i : Fin J => N (i + 1)) ↑s := by
    intro i hi j hj hij
    dsimp only at hij
    rcases lt_trichotomy i j with h | h | h
    · exfalso
      have h2 : N (i + 1) ≤ N j := hN (Nat.succ_le_of_lt (show (i : ℕ) < (j : ℕ) from h))
      have h3 : N j < N (j + 1) := (hmem j).mp hj
      rw [hij] at h2
      exact absurd (lt_of_lt_of_le h3 h2) (lt_irrefl _)
    · exact h
    · exfalso
      have h2 : N (j + 1) ≤ N i := hN (Nat.succ_le_of_lt (show (j : ℕ) < (i : ℕ) from h))
      have h3 : N i < N (i + 1) := (hmem i).mp hi
      rw [← hij] at h2
      exact absurd (lt_of_lt_of_le h3 h2) (lt_irrefl _)
  have hsum1 : ∑ i ∈ s, f (N i) ≤ ∑' n : ℕ, f n :=
    sum_comp_le_tsum s (fun i : Fin J => N i) f hinjN
  have hsum2 : ∑ i ∈ s, f (N (i + 1)) ≤ ∑' n : ℕ, f n :=
    sum_comp_le_tsum s (fun i : Fin J => N (i + 1)) f hinjS
  -- `2^{r-1} · 2 = 2^r`
  have hpow : (2 : ℝ≥0∞) ^ (r - 1) * 2 = 2 ^ r := by
    have h1 : (2 : ℝ≥0∞) ^ (r - 1) * 2 ^ (1 : ℝ) = 2 ^ (r - 1 + 1) :=
      (ENNReal.rpow_add (r - 1) 1 (by norm_num) (by norm_num)).symm
    rw [ENNReal.rpow_one] at h1
    rw [show r - 1 + 1 = r by ring] at h1
    exact h1
  calc ∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ r
      = ∑ i ∈ s, ‖a (N (i + 1)) - a (N i)‖ₑ ^ r := hsum_eq
    _ ≤ 2 ^ (r - 1) * ∑ i ∈ s, (f (N (i + 1)) + f (N i)) := hbdd
    _ = 2 ^ (r - 1) * (∑ i ∈ s, f (N (i + 1)) + ∑ i ∈ s, f (N i)) := by
        rw [Finset.sum_add_distrib]
    _ ≤ 2 ^ (r - 1) * (∑' n : ℕ, f n + ∑' n : ℕ, f n) := by
        gcongr
    _ = 2 ^ (r - 1) * (2 * ∑' n : ℕ, f n) := by rw [← two_mul]
    _ = 2 ^ r * ∑' n : ℕ, f n := by rw [← mul_assoc, hpow]
    _ = 2 ^ r * ∑' n : ℕ, ‖a n‖ₑ ^ r := rfl

end Work.KMTAreas.A7
