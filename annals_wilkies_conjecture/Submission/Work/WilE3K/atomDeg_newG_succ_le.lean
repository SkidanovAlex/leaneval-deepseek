/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): degree bookkeeping of the
  Khovanskii–Rolle elimination step.

  `E.newG y δ : Fin (n+1) → EAPoly (N+1) re` (`Elim.lean` §3) is the list of polynomial equations
  of the new system `E.newData y δ`:

  * index `0` is the Rolle equation `E.rolleDetP - C δ * E.prodPoly`;
  * the remaining indices are the old equations shifted by the value `y` of the remaining system,
    `i.succ ↦ E.G i - C (y _)`.

  This file settles the second family: subtracting a constant never raises the total degree of an
  (EA) polynomial, `MvPolynomial.totalDegree_sub_C_le`, so the carried-over equations do not raise
  the degree sum of the system.
-/
import Mathlib
import Submission.Work.WilE3K.Elim

namespace Work.WilE3K

open WilkiesDesign.E

/-- The carried-over equation `E.newG y δ i.succ` of the new system is the old equation `E.G i`
shifted by the constant `y (…)`, hence has no larger atom degree. -/
theorem atomDeg_newG_succ_le {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (y : Fin N → ℝ) (δ : ℝ) (i : Fin n) :
    WilkiesDesign.E.atomDeg (E.newG y δ i.succ) ≤ WilkiesDesign.E.atomDeg (E.G i) := by
  -- `i.succ` is not the distinguished index `0`, so the definition of `newG` selects the
  -- "shift the old equation" branch.
  have hne : ¬ (((i.succ : Fin (n + 1)) : ℕ) = 0) := by rw [Fin.val_succ]; omega
  -- Evaluate the `else` branch: the index `↑(i.succ) - 1 = ↑i` is `i` and the constant is
  -- `y ⟨rt + ↑i, _⟩`.
  have hEq : E.newG y δ i.succ =
      E.G i - MvPolynomial.C
        (y ⟨rt + (i : ℕ), by have h1 := i.isLt; have h2 := E.h; omega⟩) := by
    rw [ETData.newG, dite_eq_right hne]
    refine congr_arg₂ (fun u v : EAPoly (N + 1) re => u - v) ?_ ?_
    · exact congr_arg E.G (Fin.ext (by simp))
    · exact congr_arg (fun j => MvPolynomial.C (y j)) (Fin.ext (by simp))
  rw [hEq, atomDeg, atomDeg]
  exact Nat.add_le_add_right (MvPolynomial.totalDegree_sub_C_le (E.G i) _) 1

end Work.WilE3K
