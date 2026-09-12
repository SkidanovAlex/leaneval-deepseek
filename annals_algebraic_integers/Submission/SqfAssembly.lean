import Submission.Contracts
import Submission.SqfCore
import Submission.SqfSort
import Submission.SqfRemez
import Submission.SqfSqfree
import Mathlib.Tactic

/-!
# Theorem squarefree at the Serre data: `Contracts.SquarefreeContract`
-/

noncomputable section
open scoped BigOperators
open Polynomial
open MeasureTheory

set_option maxHeartbeats 0

namespace Submission.SqfAssembly

open Submission.Contracts
open Submission.SqfSort
open Submission.SqfRemez
open Submission.SqfSqfree
open Submission.SqfCore

/-- Theorem squarefree at the Serre data (`Contracts.SquarefreeContract`):
assembled from the sorted Hilbert family, the second-squeeze / weak-lower
bounds, the complex Remez chain and the primitive-part-squarefree lemma
(`Submission.SqfCore.core_squarefree`). -/
theorem squarefree_contract : SquarefreeContract :=
  SqfCore.core_squarefree SqfSort.exists_sorted_perm
    (fun C hCpos hcr => SqfRemez.remez_chain C hCpos hcr)
    (fun {A : Polynomial ℤ} (hA : A ≠ 0)
      (hsep : (A.map (algebraMap ℤ ℂ)).Separable) (S : Finset ℕ)
      (hSroot : ∀ s ∈ S, ¬ Polynomial.aeval (s : ℂ) (A.map (algebraMap ℤ ℂ)) = 0) =>
      SqfSqfree.squarefree_mul_primPart hA hsep S hSroot)

end Submission.SqfAssembly
