import Mathlib
import Submission.Work.Diff.STE.DeTurckJet
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chartwise DeTurck operator `pPhi`

`Work.Diff.STE.DeTurck.pPhi` is the coordinate expression of the DeTurck operator
`P(g) = -2 Ric(g) + L_{W(g)} g`, read off from the `2`-jets `(A, L, B)` of the chart matrix of `g`
and `(Abar, Lbar, Bbar)` of the chart matrix of the (fixed) background metric `g̃`.

Each entry of `pPhi` is a polynomial expression in

* the entries of the two Gram matrices `A`, `Abar`,
* the entries of the two inverse Gram matrices `(Matrix.of A)⁻¹`, `(Matrix.of Abar)⁻¹`,
* the evaluations of the first and second jets `L, B, Lbar, Bbar` on the canonical basis `bB`,

and the only non-polynomial ingredient is the inverse of the Gram matrix.  By Cramer's rule
(`Matrix.inv_def`: `A⁻¹ = (det A)⁻¹ • A.adjugate`) its entries are `(det A)⁻¹` times a polynomial in
the entries, hence `C^∞` exactly on the open set where `det A ≠ 0`.

Consequently `pPhi` is `C^∞` on the set where *both* determinants are nonvanishing; this file
proves it, by recording the two inverse-Gram entries as local `fun_prop` atoms and letting
`fun_prop` unfold the (polynomial) rest of the expression.
-/

namespace Work.Diff.STE.deTurck

open Work.Diff.EXT
open Work.Diff.STE.DeTurck

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

noncomputable section

/-- The pair of `2`-jets on which `pPhi` is evaluated: the background jet `(Abar, Lbar, Bbar)`
together with the jet `(A, L, B)` of the metric. -/
abbrev JetPair (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :=
  (MatE (E := E) × LinMat E × BilMat E) × (MatE (E := E) × LinMat E × BilMat E)

/-- The set of pairs of jets for which the DeTurck operator is defined smoothly: both Gram
matrices are nondegenerate. -/
abbrev pPhiDom (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Set (JetPair E) :=
  {w | (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0}

/-- The entries of the inverse Gram matrix of the metric depend `C^∞`-ly on the pair of jets, away
from the degenerate matrices. -/
lemma contDiffOn_invEntry_metric (r s : Idx E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : JetPair E => (Matrix.of w.2.1)⁻¹ r s) (pPhiDom E) := by
  intro w hw
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A)⁻¹ r s) w.2.1 :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_matrix_inv_pi (M := w.2.1) hw.2) r)) s
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : JetPair E => w.2.1) w := by fun_prop
  exact (h1.comp w h2).contDiffWithinAt

/-- The entries of the inverse Gram matrix of the background metric depend `C^∞`-ly on the pair of
jets, away from the degenerate matrices. -/
lemma contDiffOn_invEntry_background (r s : Idx E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : JetPair E => (Matrix.of w.1.1)⁻¹ r s) (pPhiDom E) := by
  intro w hw
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A)⁻¹ r s) w.1.1 :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_matrix_inv_pi (M := w.1.1) hw.1) r)) s
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : JetPair E => w.1.1) w := by fun_prop
  exact (h1.comp w h2).contDiffWithinAt

attribute [local fun_prop] contDiffOn_invEntry_metric contDiffOn_invEntry_background

theorem contDiffOn_pPhi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
          Work.Diff.STE.DeTurck.BilMat E) ×
        (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
          Work.Diff.STE.DeTurck.BilMat E) =>
        Work.Diff.STE.DeTurck.pPhi w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2)
      {w | (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0} := by
  rw [contDiffOn_pi]; intro i
  rw [contDiffOn_pi]; intro j
  simp only [pPhi, jLW, jnabW, jdWb, jdWU, jWb, jWU, jdGamU, jGamU, jdInv, jKzD, jKz, jRic, jRm,
    jInv]
  fun_prop

end

end Work.Diff.STE.deTurck
