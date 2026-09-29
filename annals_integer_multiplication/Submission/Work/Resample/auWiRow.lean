import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auRowDefs
import Submission.Work.Resample.auWiEqPsi
import Submission.Work.Resample.auPsiSummable
import Submission.Work.Resample.auPsiTsumRow

/-!
# The retained weights of one output of the resampling word sum to at most `3/4`

`auWi p α s t k i = (1/(2α))·e^{−π (t·n − s·k)²/(α²t²)}`, `n = auK s t k + i − auM p α`,
is the ideal Gaussian weight of the `i`-th retained term of output `k` of the 1-D
windowed resampling word.  This module proves `Work.Resample.auWiRow`: the `auL p α = 2m+1`
retained weights of any output sum to at most `3/4`, the same bound as a row sum of the
Gaussian resampling matrix `resA s t α` (`Work.ResMath.resA_rowsum_le`).

The argument is that the window index `i ↦ auK s t k + i − auM p α` is injective, that
`auWi p α s t k i = auPsi α s t k n` for that index, and that the *full* Gaussian series
`∑' n : ℤ, auPsi α s t k n` is exactly the row sum `∑ j, ‖(resA s t α) k j‖`
(`Work.Resample.auPsiTsumRow`, by reindexing `ℤ ≃ Fin s × ℤ`).  A partial sum of a
nonnegative summable family is at most the total sum.
-/

namespace Work.Resample

open HvdH

/-- The Gaussian weights are nonnegative. -/
lemma auPsi_nonneg (α s t k : ℕ) (hα : 0 < α) (n : ℤ) : 0 ≤ auPsi α s t k n := by
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  refine mul_nonneg ?_ (Real.exp_nonneg _)
  positivity

/-- The window index `i ↦ auK s t k + i - auM p α` is injective. -/
lemma auIdx_inj (α s t k p : ℕ) {i i' : ℕ}
    (h : (auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ) = (auK s t k : ℤ) + (i' : ℤ) - (auM p α : ℤ)) :
    i = i' := by
  have h2 : (i : ℤ) = (i' : ℤ) := by linarith
  exact Int.ofNat_inj.mp h2

-- The retained ideal weights of output k sum to at most 3/4.  Each window term
-- (1/(2α)) exp(-π s^2 (k/t - j/s - q)^2/α^2) is one coset term of the entry (resA s t α) k j,
-- and i ↦ (n mod s, n div s) with n = auK s t k + i - auM p α is injective, so the window sum is
-- at most the row sum of resA, which is ≤ 3/4 by Work.ResMath.resA_rowsum_le
-- (Submission/Work/ResMath/resA_norm_le.lean), via the coset reindexing lemmas of
-- Submission/Work/ResMath/ (e.g. resS_rowsum_reindex).  Compare Work.Resample.sliceA1Sum.
theorem auWiRow (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (hαp : α ^ 2 < p) (hst : s < t) :
    ∀ k : Fin t, ∑ i ∈ Finset.range (Work.Resample.auL p α), Work.Resample.auWi p α s t (k : ℕ) i ≤ 3 / 4 := by
  intro k
  have _ := hαp
  have _ := hst
  have ht : 0 < t := Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hα0 : 0 < α := by omega
  have hs0 : 0 < s := by omega
  -- the window index `i ↦ auK s t k + i - auM p α` is an embedding `ℕ ↪ ℤ`
  let e : ℕ ↪ ℤ :=
    ⟨fun i => (auK s t (k : ℕ) : ℤ) + (i : ℤ) - (auM p α : ℤ),
      fun i i' h => auIdx_inj α s t (k : ℕ) p h⟩
  -- each retained weight is the Gaussian weight of the window index
  have hterm : ∀ i : ℕ, auWi p α s t (k : ℕ) i = auPsi α s t (k : ℕ) (e i) :=
    fun i => auWiEqPsi p α s t (k : ℕ) i ht
  have hsumm : Summable (auPsi α s t (k : ℕ)) := auPsiSummable α s t (k : ℕ) hα0
  calc ∑ i ∈ Finset.range (auL p α), auWi p α s t (k : ℕ) i
      = ∑ i ∈ Finset.range (auL p α), auPsi α s t (k : ℕ) (e i) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∑ n ∈ (Finset.range (auL p α)).map e, auPsi α s t (k : ℕ) n :=
        (Finset.sum_map _ e _).symm
    _ ≤ ∑' n : ℤ, auPsi α s t (k : ℕ) n :=
        hsumm.sum_le_tsum _ (fun n _ => auPsi_nonneg α s t (k : ℕ) hα0 n)
    _ = ∑ j : Fin s, ‖(HvdH.resA s t α) k j‖ := auPsiTsumRow α s t hs0 hα0 k
    _ ≤ 3 / 4 := Work.ResMath.resA_rowsum_le s t α hs0 hα k

end Work.Resample
