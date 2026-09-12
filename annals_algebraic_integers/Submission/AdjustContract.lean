import Submission.Contracts
import Submission.RootData
import Submission.SqSep
import Submission.AdjustLemma
import Mathlib.Tactic

/-!
# `Contracts.AdjustContract` from the adjust lemma

Given `Submission.AdjustLemma.adjust_lemma` (thm:adjust + cor:adjust in root
data form), `Squarefree Q` + `natDegree = n` hypotheses are converted into
root data via `SqSep.squarefree_separable` (Squarefree ℤ[X] ⟹ Separable over
ℂ) and `RootData.root_data_of_separable`.  The theorem closes
`Contracts.AdjustContract`.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.AdjustContract

open Submission.Contracts
open Submission.RootData
open Submission.SqSep

/-- Contract 2 (Corollary adjust) is closed by the adjust lemma. -/
theorem adjust_contract : Submission.Contracts.AdjustContract := by
  rcases Submission.AdjustLemma.adjust_lemma with ⟨Cadj, hCadjpos, hCadj⟩
  refine ⟨Cadj, hCadjpos, ?_⟩
  intro n hn Q hsq hQn P hP
  have hn1 : 1 ≤ n := by omega
  have hQ0 : Q ≠ 0 := Squarefree.ne_zero hsq
  have hsep : (Q.map (algebraMap ℤ ℂ)).Separable := squarefree_separable hQ0 hsq
  have hrd : RootDataOf Q n := root_data_of_separable (n := n) hn1 Q hQ0 hQn hsep
  rcases hrd with ⟨α, hαinj, hfac⟩
  rcases hCadj n hn Q hQ0 hQn α hαinj hfac P hP with ⟨R, _β, hRdeg, _hid, _hβ, hnorm⟩
  exact ⟨R, hRdeg, hnorm⟩

end Submission.AdjustContract
