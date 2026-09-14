

import Mathlib
import Submission.Vdw.MultiPrimeSigma
import Submission.Commons.NumberTheory.ZMod.sum_minrep_weight_all

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The full frequency sum `σ(M)` and its `Wsum` decomposition

For the multi-prime §4 chapter we need the *full* frequency sum
`σ(M) = Σ_{b : ZMod M} freqWeightZ M H b` (`sig`) and its relation to the
reduced sum `Wsum` (`MultiPrimeSigma.Wsum`): the nonzero-frequency part is

    `Wsum n H M = σ(M)^n - (2H+1)^n`   (`Wsum_eq_sig`),

together with the two elementary bounds on `σ` derived from the commons
harmonic-sum estimates:

* `sig_le`: `σ(M) ≤ (2H+1) + M(1+log M)`,
* `sig_le_two`: `σ(M) ≤ 5(M + 2H+1)(1+log M)`,

and `sig_le_self`: `2H+1 ≤ σ(M)` (the zero frequency always contributes).

Axioms: propext / Classical.choice / Quot.sound only.
-/


namespace Submission.Vdw
noncomputable section

/-- The full frequency sum `σ(M) = Σ_{b : ZMod M} freqWeightZ M H b`. -/
def sig (H M : ℕ) [NeZero M] : ℝ := ∑ b : ZMod M, freqWeightZ M H b

lemma sig_nonneg (H M : ℕ) [NeZero M] : 0 ≤ sig H M :=
  Finset.sum_nonneg (fun b _ => freqWeightZ_nonneg _ H _)

/-- The factorization of the product sum over frequency vectors. -/
lemma sum_prod_freqWeightZ (n H M : ℕ) [NeZero M] :
    (∑ x : Fin n → ZMod M, ∏ i, freqWeightZ M H (x i)) = (sig H M) ^ n := by
  rw [sig]
  have h1 : (∑ x : Fin n → ZMod M, ∏ i, freqWeightZ M H (x i))
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod M))),
          ∏ i, (fun (_ : Fin n) (b : ZMod M) => freqWeightZ M H b) i (x i) := by
    rw [Fintype.piFinset_univ]
  rw [h1, ← Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset (ZMod M)))
    (f := fun _ b => freqWeightZ M H b), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `Wsum` is `σ(M)^n` minus the contribution of the zero frequency. -/
lemma Wsum_eq_sig (n H M : ℕ) [NeZero M] (hM : M ≠ 0) :
    Wsum n H M = (sig H M) ^ n - (((2 * H + 1 : ℕ)) : ℝ) ^ n := by
  have hzero : ∏ i : Fin n, freqWeightZ M H ((0 : Fin n → ZMod M) i)
      = (((2 * H + 1 : ℕ)) : ℝ) ^ n := by
    have h1 : ∀ i : Fin n, freqWeightZ M H ((0 : Fin n → ZMod M) i)
        = (((2 * H + 1 : ℕ)) : ℝ) := by
      intro i
      simp [freqWeightZ]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [Wsum_of_ne_zero n H M hM, ← sum_prod_freqWeightZ n H M,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n → ZMod M)), hzero]
  ring

lemma Wsum_le_sig_pow (n H M : ℕ) [NeZero M] (hM : M ≠ 0) :
    Wsum n H M ≤ (sig H M) ^ n := by
  rw [Wsum_eq_sig n H M hM]
  have h0 : (0 : ℝ) ≤ (((2 * H + 1 : ℕ)) : ℝ) ^ n := by positivity
  linarith

lemma sig_le (H M : ℕ) [NeZero M] :
    sig H M ≤ (((2 * H + 1 : ℕ)) : ℝ) + (M : ℝ) * (1 + Real.log M) := by
  have h := Commons.NumberTheory.ZMod.sum_minrep_weight_all M (((2 * H + 1 : ℕ)) : ℝ)
    (by positivity)
  have hsplit : sig H M
      = (((2 * H + 1 : ℕ)) : ℝ)
        + ∑ b ∈ (Finset.univ : Finset (ZMod M)).erase 0,
            min (((2 * H + 1 : ℕ)) : ℝ)
              ((M : ℝ) / (2 * ((min b.val (M - b.val) : ℕ) : ℝ))) := by
    rw [sig, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod M))]
    have h0 : freqWeightZ M H (0 : ZMod M) = (((2 * H + 1 : ℕ)) : ℝ) := by
      simp [freqWeightZ]
    rw [h0, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    simp only [freqWeightZ, if_neg hb0]
  rw [hsplit]
  refine add_le_add le_rfl ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun b _ _ => le_min (by positivity) (by positivity))) h

lemma sig_le_two (H M : ℕ) [NeZero M] :
    sig H M ≤ 5 * ((M : ℝ) + (((2 * H + 1 : ℕ)) : ℝ)) * (1 + Real.log M) := by
  have h := Commons.NumberTheory.ZMod.sum_minrep_weight_le M H
  simp only [sig, freqWeightZ] at h ⊢
  exact h

lemma sig_le_self (H M : ℕ) [NeZero M] :
    (((2 * H + 1 : ℕ)) : ℝ) ≤ sig H M := by
  have h := freqWeightZ_nonneg (M := M) H 0
  have hmem : (0 : ZMod M) ∈ (Finset.univ : Finset (ZMod M)) := Finset.mem_univ _
  have h2 : freqWeightZ M H 0 ≤ sig H M := by
    rw [sig]
    exact Finset.single_le_sum (fun b _ => freqWeightZ_nonneg (M := M) H b) hmem
  rwa [freqWeightZ, if_pos rfl] at h2

end
end Submission.Vdw
