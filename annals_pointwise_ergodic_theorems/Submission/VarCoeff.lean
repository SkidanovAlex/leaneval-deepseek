import ChallengeDeps
import Mathlib.Tactic
import Submission.VarSums
import Submission.VarPrep

/-!
# The variational norm of a weighted series

We bound the variational norm of a sequence of the form `n ↦ ∑' k, d k n * b k n`, where the
coefficients `d k n` decay like `1 / m n` and where each column `k ↦ b k n` is eventually zero.

* `sum_le_tsum_of_injOn`: a sub-sum of a nonnegative series along an injective index map;
* `enorm_tsum_mul_le`: `‖∑' k, d k n * b k n‖ ≤ (1/m n) ∑' k, ‖b k n‖`;
* `variationalNorm_mul_le`: the variational norm of `n ↦ ∑' k, d k n * b k n` is at most three
  times the pointwise `1/m`-weighted `ℓ¹` norm of the family `b`.

This is the estimate that controls the error term in the dyadic telescoping reduction.  The
`1/m n` weight is what makes the "extra" contributions of the individual dyadic pieces
summable: the `ℓ¹` sum over the *distinct* indices appearing in a monotone selection is bounded
by the corresponding series (the injectivity argument), and the increments vanish at repeated
indices, so no loss occurs on the non-strict part of a monotone selection.
-/

set_option maxHeartbeats 1600000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-- A finite sub-sum of a nonnegative series along an index map which is injective on the index
set is bounded by the whole series. -/
lemma sum_le_tsum_of_injOn {R : ℕ → ℝ≥0∞} {ι : Type*} {s : Finset ι} {φ : ι → ℕ}
    (h : ∀ i ∈ s, ∀ j ∈ s, φ i = φ j → i = j) :
    ∑ i ∈ s, R (φ i) ≤ ∑' n, R n := by
  rw [← Finset.sum_image h]
  exact ENNReal.sum_le_tsum _

/-- A single term of a nonnegative series is bounded by the series. -/
lemma le_tsum_nat (f : ℕ → ℝ≥0∞) (n : ℕ) : f n ≤ ∑' i, f i := by
  calc f n = ∑ i ∈ ({n} : Finset ℕ), f i := by simp
    _ ≤ ∑' i, f i := ENNReal.sum_le_tsum _

/-- `ENNReal.ofReal (m⁻¹) = (m : ℝ≥0∞)⁻¹` for a positive natural number `m`. -/
lemma ofReal_inv_natCast {m : ℕ} (hm : 0 < m) :
    ENNReal.ofReal ((m : ℝ)⁻¹) = ((m : ℝ≥0∞))⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hm : (0:ℝ) < (m:ℝ)),
    ENNReal.ofReal_natCast]

/-- `‖z‖ₑ ≤ (m : ℝ≥0∞)⁻¹` whenever `‖z‖ ≤ m⁻¹`. -/
lemma enorm_le_inv_of_norm_le {m : ℕ} {z : ℂ} (h : ‖z‖ ≤ (m : ℝ)⁻¹) :
    ‖z‖ₑ ≤ (m : ℝ≥0∞)⁻¹ := by
  cases m with
  | zero =>
      rw [Nat.cast_zero, inv_zero] at h
      rw [norm_le_zero_iff.mp h, enorm_zero]
      exact bot_le
  | succ k =>
      rw [← ofReal_norm, ← ofReal_inv_natCast (Nat.succ_pos k)]
      exact ENNReal.ofReal_le_ofReal h

/-- The `enorm` of a weighted pointwise series. -/
lemma enorm_tsum_mul_le {m : ℕ → ℕ} {d b : ℕ → ℕ → ℂ} (hd : ∀ k n, ‖d k n‖ ≤ (m n : ℝ)⁻¹)
    (hb : ∀ n, ∃ K, ∀ k ≥ K, b k n = 0) (n : ℕ) :
    ‖∑' k, d k n * b k n‖ₑ ≤ (m n : ℝ≥0∞)⁻¹ * ∑' k, ‖b k n‖ₑ := by
  obtain ⟨K, hK⟩ := hb n
  have h1 : (∑' k, d k n * b k n) = ∑ k ∈ range K, d k n * b k n :=
    tsum_eq_sum (f := fun k => d k n * b k n) (s := range K)
      (fun k hk => by
        rw [hK k (by simp only [mem_range, not_lt] at hk; omega), mul_zero])
  rw [h1]
  calc ‖∑ k ∈ range K, d k n * b k n‖ₑ ≤ ∑ k ∈ range K, ‖d k n * b k n‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ k ∈ range K, (m n : ℝ≥0∞)⁻¹ * ‖b k n‖ₑ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [enorm_mul]
        exact mul_le_mul_of_nonneg_right (enorm_le_inv_of_norm_le (hd k n))
          (zero_le : (0:ℝ≥0∞) ≤ ‖b k n‖ₑ)
    _ = (m n : ℝ≥0∞)⁻¹ * ∑ k ∈ range K, ‖b k n‖ₑ := by rw [Finset.mul_sum]
    _ ≤ (m n : ℝ≥0∞)⁻¹ * ∑' k, ‖b k n‖ₑ := by
        gcongr
        exact ENNReal.sum_le_tsum _

/-- **Error term estimate.**  If `‖d k n‖ ≤ 1/m n` and each column `k ↦ b k n` is eventually
zero, then the variational norm of `n ↦ ∑' k, d k n * b k n` is at most three times the pointwise
`1/m`-weighted `ℓ¹` norm of the family `b`. -/
lemma variationalNorm_mul_le {r : ℝ≥0} (hr : 1 ≤ r) {m : ℕ → ℕ}
    {d b : ℕ → ℕ → ℂ} (hd : ∀ k n, ‖d k n‖ ≤ (m n : ℝ)⁻¹)
    (hb : ∀ n, ∃ K, ∀ k ≥ K, b k n = 0) :
    variationalNorm r (fun n => ∑' k, d k n * b k n)
      ≤ 3 * ∑' n, (m n : ℝ≥0∞)⁻¹ * (∑' k, ‖b k n‖ₑ) := by
  let S : ℕ → ℝ≥0∞ := fun n => (m n : ℝ≥0∞)⁻¹ * ∑' k, ‖b k n‖ₑ
  change variationalNorm r (fun n => ∑' k, d k n * b k n) ≤ 3 * ∑' n, S n
  let e : ℕ → ℂ := fun n => ∑' k, d k n * b k n
  have henorm : ∀ n, ‖e n‖ₑ ≤ S n := fun n => enorm_tsum_mul_le hd hb n
  have hsup : (⨆ n, ‖(fun n => ∑' k, d k n * b k n) n‖ₑ) ≤ ∑' n, S n := by
    refine iSup_le (fun n => le_trans (henorm n) ?_)
    exact le_tsum_nat S n
  have hvar : varPart r (fun n => ∑' k, d k n * b k n) ≤ 2 * ∑' n, S n := by
    haveI : Fact (1 ≤ (↑r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
    refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
    set supp : Finset (Fin J) :=
      Finset.univ.filter (fun i => N ((i : ℕ) + 1) ≠ N (i : ℕ)) with hsupp
    have hmem : ∀ i ∈ supp, N (i : ℕ) < N ((i : ℕ) + 1) := by
      intro i hi
      have hne : N ((i : ℕ) + 1) ≠ N (i : ℕ) := (Finset.mem_filter.mp hi).2
      have hle : N (i : ℕ) ≤ N ((i : ℕ) + 1) := hN (by omega)
      omega
    have hinj1 : ∀ i ∈ supp, ∀ j ∈ supp, N (i : ℕ) = N (j : ℕ) → i = j := by
      intro i hi j hj heq
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · exfalso
        have h1 := hmem i hi
        have h2 : N ((i : ℕ) + 1) ≤ N (j : ℕ) := hN (by omega)
        omega
      · exact Fin.ext h
      · exfalso
        have h1 := hmem j hj
        have h2 : N ((j : ℕ) + 1) ≤ N (i : ℕ) := hN (by omega)
        omega
    have hinj2 : ∀ i ∈ supp, ∀ j ∈ supp, N ((i : ℕ) + 1) = N ((j : ℕ) + 1) → i = j := by
      intro i hi j hj heq
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · exfalso
        have h1 := hmem i hi
        have h2 : N ((i : ℕ) + 1) ≤ N (j : ℕ) := hN (by omega)
        have h3 := hmem j hj
        omega
      · exact Fin.ext h
      · exfalso
        have h1 := hmem j hj
        have h2 : N ((j : ℕ) + 1) ≤ N (i : ℕ) := hN (by omega)
        have h3 := hmem i hi
        omega
    have hstep3 : ENNReal.ofReal ‖WithLp.toLp r
        (fun i : Fin J => e (N ((i : ℕ) + 1)) - e (N (i : ℕ)))‖
        ≤ ∑ i ∈ supp, ENNReal.ofReal ‖e (N ((i : ℕ) + 1)) - e (N (i : ℕ))‖ := by
      have hmain : ENNReal.ofReal ‖WithLp.toLp r
          (fun i : Fin J => e (N ((i : ℕ) + 1)) - e (N (i : ℕ)))‖
          ≤ ∑ i : Fin J, ENNReal.ofReal ‖e (N ((i : ℕ) + 1)) - e (N (i : ℕ))‖ := by
        calc ENNReal.ofReal ‖WithLp.toLp r
              (fun i : Fin J => e (N ((i : ℕ) + 1)) - e (N (i : ℕ)))‖
            ≤ ENNReal.ofReal (∑ i : Fin J, ‖e (N ((i : ℕ) + 1)) - e (N (i : ℕ))‖) :=
              ENNReal.ofReal_le_ofReal (norm_toLp_le_sum_norm hr _)
          _ = ∑ i : Fin J, ENNReal.ofReal ‖e (N ((i : ℕ) + 1)) - e (N (i : ℕ))‖ :=
              ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)
      have hsub : (∑ i : Fin J, ENNReal.ofReal ‖e (N ((i : ℕ) + 1)) - e (N (i : ℕ))‖)
          = ∑ i ∈ supp, ENNReal.ofReal ‖e (N ((i : ℕ) + 1)) - e (N (i : ℕ))‖ := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro i _; exact Finset.mem_univ i
        · intro i _ hi
          have heq : N ((i : ℕ) + 1) = N (i : ℕ) := by
            by_contra hne
            exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
          rw [heq, sub_self, norm_zero, ENNReal.ofReal_zero]
      rw [hsub] at hmain
      exact hmain
    have hstep1 : ∑ i ∈ supp, ENNReal.ofReal ‖e (N ((i : ℕ) + 1)) - e (N (i : ℕ))‖
        ≤ ∑ i ∈ supp, (S (N ((i : ℕ) + 1)) + S (N (i : ℕ))) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [ofReal_norm]
      exact le_trans enorm_sub_le (add_le_add (henorm _) (henorm _))
    have hstep2 : ∑ i ∈ supp, (S (N ((i : ℕ) + 1)) + S (N (i : ℕ))) ≤ 2 * ∑' n, S n := by
      rw [Finset.sum_add_distrib, two_mul]
      exact add_le_add
        (sum_le_tsum_of_injOn (R := S) (φ := fun i : Fin J => N ((i : ℕ) + 1)) hinj2)
        (sum_le_tsum_of_injOn (R := S) (φ := fun i : Fin J => N (i : ℕ)) hinj1)
    exact hstep3.trans (hstep1.trans hstep2)
  calc ((⨆ n, ‖∑' k, d k n * b k n‖ₑ) + varPart r (fun n => ∑' k, d k n * b k n))
      ≤ (∑' n, S n) + (2 * ∑' n, S n) := add_le_add hsup hvar
    _ = 3 * ∑' n, S n := by ring

end PointwiseErgodicTheorems
end Submission
