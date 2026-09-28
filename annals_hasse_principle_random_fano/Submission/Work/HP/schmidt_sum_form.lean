import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.prod_one_add_le_sum_prod

/-!
# Schmidt's bound in "sum of monomials" form (`Work.HP.schmidt_sum_form`)

For every sublattice `L ⊆ ℤ^ι` and every `T ≥ 1`,

`#(L ∩ B(T)) ≤ K(ι) · ∑_{k = 0}^{rk L} T^k / (λ_1 ⋯ λ_k)`,

where `λ_1 ≤ λ_2 ≤ ⋯` are the successive minima of `L` for the Euclidean unit ball and `K(ι)`
depends only on the ambient type `ι`.  Equivalently (reindexing `k = rk L - i`), the sum is
`∑_{i < rk L + 1} T^{rk L - i} / ∏_{j < rk L - i} lam L (j+1)`, which is the form used by
`Work.HP.ball_count_small` and `Work.HP.pair_counts`.

The proof starts from the already established product form of Schmidt's bound
(`Work.HP.Sig2.schmidt_bound`)

`#(L ∩ B(T)) ≤ K' · ∏_{i < rk L} (1 + T / λ_{i+1})`

and expands the product.  Since `i ↦ T / λ_{i+1}` is nonnegative and non-increasing
(`lam_mono`, `lam_pos`), the elementary-symmetric comparison
`Work.HP.prod_one_add_le_sum_prod` gives

`∏_{i < rk L} (1 + T / λ_{i+1}) ≤ 2^{rk L} · ∑_{k ≤ rk L} T^k / (λ_1 ⋯ λ_k)`,

and `2^{rk L} ≤ 2^{#ι}` (`rk_le_card`) is absorbed into the constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindexing the Schmidt sum: `∑_{i} T^{R-i} / ∏_{j<R-i} λ_{j+1} = ∑_{k} T^k / ∏_{j<k} λ_{j+1}`
for `R = rk L`. -/
lemma sum_reindex_schmidt (L : Submodule ℤ (ι → ℤ)) (T : ℝ) :
    (∑ i ∈ Finset.range (rk L + 1),
        T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1))
      = ∑ k ∈ Finset.range (rk L + 1), T ^ k / ∏ j ∈ Finset.range k, lam L (j + 1) := by
  have h := Finset.sum_range_reflect
    (fun k => T ^ k / ∏ j ∈ Finset.range k, lam L (j + 1)) (rk L + 1)
  simpa using h

/-- `∏_{m<k} (T / λ_{m+1}) = T^k / ∏_{m<k} λ_{m+1}`. -/
lemma prod_range_div (L : Submodule ℤ (ι → ℤ)) (T : ℝ) (k : ℕ) :
    ∏ m ∈ Finset.range k, (T / lam L (m + 1))
      = T ^ k / ∏ m ∈ Finset.range k, lam L (m + 1) := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]

theorem schmidt_sum_form (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∑ i ∈ Finset.range (rk L + 1),
        T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1) := by
  obtain ⟨Ks, hKs, hsb⟩ := Sig2.schmidt_bound (ι := ι)
  refine ⟨Ks * (2 : ℝ) ^ (Fintype.card ι), mul_pos hKs (pow_pos (by norm_num) _), ?_⟩
  intro L T hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  -- the ratio `T / λ_{i+1}`, truncated at `rk L`
  set a : ℕ → ℝ := (fun i => if i < rk L then T / lam L (i + 1) else 0) with ha
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    by_cases hi : i < rk L
    · simp only [ha, hi, ↓reduceIte]
      exact div_nonneg hT0 (lam_nonneg L _)
    · simp only [ha, hi, ↓reduceIte, le_refl]
  have hamono : ∀ i j, i ≤ j → a j ≤ a i := by
    intro i j hij
    by_cases hj : j < rk L
    · have hi : i < rk L := lt_of_le_of_lt hij hj
      simp only [ha, hi, hj, ↓reduceIte]
      exact div_le_div_of_nonneg_left hT0 (lam_pos L (by omega) (by omega))
        (lam_mono L (Nat.succ_le_succ hij) (by omega))
    · by_cases hi : i < rk L
      · simp only [ha, hi, hj, ↓reduceIte]
        exact div_nonneg hT0 (lam_nonneg L _)
      · simp only [ha, hi, hj, ↓reduceIte, le_refl]
  have hA := prod_one_add_le_sum_prod a ha0 hamono (rk L)
  have hprod : (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
      = ∏ i ∈ Finset.range (rk L), (1 + a i) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' : i < rk L := Finset.mem_range.mp hi
    simp only [ha, hi', ↓reduceIte]
    ring
  have hsum : (∑ k ∈ Finset.range (rk L + 1), ∏ m ∈ Finset.range k, a m)
      = ∑ k ∈ Finset.range (rk L + 1), T ^ k / ∏ m ∈ Finset.range k, lam L (m + 1) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ rk L := by have := Finset.mem_range.mp hk; omega
    have hp : (∏ m ∈ Finset.range k, a m)
        = ∏ m ∈ Finset.range k, (T / lam L (m + 1)) := by
      refine Finset.prod_congr rfl (fun m hm => ?_)
      have hm' : m < rk L := lt_of_lt_of_le (Finset.mem_range.mp hm) hk'
      simp only [ha, hm', ↓reduceIte]
    rw [hp, prod_range_div]
  have hSnn : 0 ≤ ∑ k ∈ Finset.range (rk L + 1),
      T ^ k / ∏ m ∈ Finset.range k, lam L (m + 1) :=
    Finset.sum_nonneg (fun k _ => div_nonneg (pow_nonneg hT0 k)
      (Finset.prod_nonneg (fun m _ => lam_nonneg L _)))
  have hpow : (2 : ℝ) ^ (rk L) ≤ (2 : ℝ) ^ (Fintype.card ι) :=
    pow_le_pow_right₀ (by norm_num) (rk_le_card L)
  calc (ballCount L T : ℝ)
      ≤ Ks * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) := hsb L T hT
    _ = Ks * ∏ i ∈ Finset.range (rk L), (1 + a i) := by rw [hprod]
    _ ≤ Ks * ((2 : ℝ) ^ (rk L) * ∑ k ∈ Finset.range (rk L + 1), ∏ m ∈ Finset.range k, a m) :=
        mul_le_mul_of_nonneg_left hA (le_of_lt hKs)
    _ = Ks * ((2 : ℝ) ^ (rk L) * ∑ k ∈ Finset.range (rk L + 1),
          T ^ k / ∏ m ∈ Finset.range k, lam L (m + 1)) := by rw [hsum]
    _ ≤ Ks * ((2 : ℝ) ^ (Fintype.card ι) * ∑ k ∈ Finset.range (rk L + 1),
          T ^ k / ∏ m ∈ Finset.range k, lam L (m + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hSnn) (le_of_lt hKs)
    _ = Ks * (2 : ℝ) ^ (Fintype.card ι) * (∑ k ∈ Finset.range (rk L + 1),
          T ^ k / ∏ m ∈ Finset.range k, lam L (m + 1)) := by ring
    _ = Ks * (2 : ℝ) ^ (Fintype.card ι) * (∑ i ∈ Finset.range (rk L + 1),
          T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1)) := by
        rw [← sum_reindex_schmidt L T]

end Work.HP
