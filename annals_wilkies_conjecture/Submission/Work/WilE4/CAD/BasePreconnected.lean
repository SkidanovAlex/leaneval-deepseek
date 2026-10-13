/-
  WilE4 / CAD — the base cells of a projection are preconnected.

  `baseCell_type_const` (`Level.lean`) needs, at level `k`, the preconnectedness of the cells of
  `CadCells k (projDataT k H)` — that is the hypothesis `hpre` under which the type constancy is
  stated, and hence the input of the degree recursion `CadCells_length_le` (`Bounds.lean`).

  For `k = 0` the decomposition has the single cell `ℝ⁰`.  For `k = k' + 1` the family
  `projDataT (k' + 1) H` is `tower (projData H) ++ [0]`, hence strongly closed under
  `pderiv (Fin.last k')` (`projDataT_deriv_closed`), so `CadCells_preconnected` applies.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.Decomp
import Submission.Work.WilE4.CAD.CadCells_isUnionOf
import Submission.Work.WilE4.CAD.CadCells_preconnected

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial

/-- **The cells of `CadCells k (projDataT k H)` are preconnected.**  This is the `hpre` input of
`baseCell_type_const` at every level of the decomposition. -/
theorem projDataT_base_preconnected {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) :
    ∀ C ∈ CadCells k (projDataT k H), IsPreconnected C.set := by
  match k with
  | 0 =>
    intro C hC
    rw [mem_CadCells_zero] at hC
    subst hC
    rw [topCell_set]
    exact isPreconnected_univ
  | k' + 1 =>
    exact CadCells_preconnected (n := k') (projDataT (k' + 1) H)
      (projDataT_deriv_closed (m := k') H)

end Work.WilE4.CAD
