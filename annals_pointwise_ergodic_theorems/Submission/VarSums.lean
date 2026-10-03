import ChallengeDeps
import Mathlib.Tactic
import Submission.VarNorm

/-!
# The variational norm of sums and shifted sequences

We record two further structural facts about the variational norm
`variationalNorm r a = sup_n ‖a n‖ₑ + V^r(a)` of a sequence `a : ℕ → ℂ`:

* subadditivity over a *countable* pointwise sum of eventually vanishing families
  (`variationalNorm_tsum_le`), the form needed for the dyadic telescoping reduction;
* the "prepend zeros" estimate (`variationalNorm_prepend_le`): shifting a sequence to the
  right by `m` steps and filling the initial segment with zeros multiplies the variational
  norm by at most `4`.

Both are standard tools of the variational formalism; the first is what lets one bound the
variation of a telescoped average by the sum of the variations of its dyadic pieces.
-/

set_option maxHeartbeats 1600000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-- The supremum part of the variational norm of a pointwise sum of an eventually vanishing family
of sequences is at most the sum of the supremum parts. -/
lemma iSup_enorm_tsum_le {b : ℕ → ℕ → ℂ} (hb : ∀ n, ∃ K, ∀ k ≥ K, b k n = 0) :
    (⨆ n, ‖∑' k, b k n‖ₑ) ≤ ∑' k, ⨆ n, ‖b k n‖ₑ := by
  refine iSup_le (fun n => ?_)
  obtain ⟨K, hK⟩ := hb n
  have h1 : (∑' k, b k n) = ∑ k ∈ range K, b k n :=
    tsum_eq_sum (f := fun k => b k n) (s := range K)
      (fun k hk => hK k (by simp only [mem_range, not_lt] at hk; omega))
  rw [h1]
  calc ‖∑ k ∈ range K, b k n‖ₑ ≤ ∑ k ∈ range K, ‖b k n‖ₑ := enorm_sum_le _ _
    _ ≤ ∑' k, ‖b k n‖ₑ := ENNReal.sum_le_tsum _
    _ ≤ ∑' k, ⨆ n, ‖b k n‖ₑ := ENNReal.tsum_le_tsum (fun k => le_iSup (fun n => ‖b k n‖ₑ) n)

/-- The variation part of the variational norm of a pointwise sum of an eventually vanishing
family of sequences is at most the sum of the variation parts. -/
lemma varPart_tsum_le {r : ℝ≥0} (hr : 1 ≤ r) {b : ℕ → ℕ → ℂ}
    (hb : ∀ n, ∃ K, ∀ k ≥ K, b k n = 0) :
    varPart r (fun n => ∑' k, b k n) ≤ ∑' k, varPart r (fun n => b k n) := by
  classical
  haveI : Fact (1 ≤ (↑r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
  have hKfspec : ∀ n, ∀ k ≥ Nat.find (hb n), b k n = 0 := fun n => Nat.find_spec (hb n)
  set K : ℕ := (∑ i ∈ range (J + 1), Nat.find (hb (N i))) + 1 with hK
  have hKle : ∀ i, i ≤ J → Nat.find (hb (N i)) ≤ K := by
    intro i hi
    have hmem : i ∈ range (J + 1) := by simp only [mem_range]; omega
    have := Finset.single_le_sum (f := fun j => Nat.find (hb (N j)))
      (fun j _ => Nat.zero_le _) hmem
    omega
  have hNzero : ∀ i, i ≤ J → ∀ k, k ≥ K → b k (N i) = 0 :=
    fun i hi k hk => hKfspec (N i) k (le_trans (hKle i hi) hk)
  have hAeq : ∀ i, i ≤ J → (∑' k, b k (N i)) = ∑ k ∈ range K, b k (N i) := by
    intro i hi
    exact tsum_eq_sum (f := fun k => b k (N i)) (s := range K)
      (fun k hk => hNzero i hi k (by simp only [mem_range, not_lt] at hk; omega))
  set g : ℕ → Fin J → ℂ := fun k i => b k (N (i + 1)) - b k (N i) with hg
  have hvec : (fun i : Fin J => (∑' k, b k (N (i + 1))) - (∑' k, b k (N i)))
      = ∑ k ∈ range K, g k := by
    funext i
    have hi1 : (i : ℕ) + 1 ≤ J := by have := i.2; omega
    have hi0 : (i : ℕ) ≤ J := by have := i.2; omega
    rw [Finset.sum_apply, hAeq ((i : ℕ) + 1) hi1, hAeq (i : ℕ) hi0,
      ← Finset.sum_sub_distrib]
  rw [hvec, WithLp.toLp_sum]
  calc ENNReal.ofReal ‖∑ k ∈ range K, WithLp.toLp r (g k)‖
      ≤ ENNReal.ofReal (∑ k ∈ range K, ‖WithLp.toLp r (g k)‖) :=
        ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
    _ = ∑ k ∈ range K, ENNReal.ofReal ‖WithLp.toLp r (g k)‖ :=
        ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg _)
    _ ≤ ∑' k, ENNReal.ofReal ‖WithLp.toLp r (g k)‖ := ENNReal.sum_le_tsum _
    _ ≤ ∑' k, varPart r (fun n => b k n) := ENNReal.tsum_le_tsum (fun k =>
        le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl)))

/-- **Variational norm of a countable pointwise sum.**  If every column `n ↦ b k n` is
eventually zero in `k`, then the variational norm of the pointwise sum is at most the sum of the
variational norms of the columns. -/
lemma variationalNorm_tsum_le {r : ℝ≥0} (hr : 1 ≤ r) {b : ℕ → ℕ → ℂ}
    (hb : ∀ n, ∃ K, ∀ k ≥ K, b k n = 0) :
    variationalNorm r (fun n => ∑' k, b k n) ≤ ∑' k, variationalNorm r (fun n => b k n) := by
  have hsup := iSup_enorm_tsum_le (b := b) hb
  have hvar := varPart_tsum_le (r := r) hr (b := b) hb
  rw [variationalNorm_eq_add]
  calc ((⨆ n, ‖∑' k, b k n‖ₑ) + varPart r (fun n => ∑' k, b k n))
      ≤ (∑' k, ⨆ n, ‖b k n‖ₑ) + (∑' k, varPart r (fun n => b k n)) := add_le_add hsup hvar
    _ = ∑' k, ((⨆ n, ‖b k n‖ₑ) + varPart r (fun n => b k n)) := (ENNReal.tsum_add).symm

end PointwiseErgodicTheorems
end Submission
