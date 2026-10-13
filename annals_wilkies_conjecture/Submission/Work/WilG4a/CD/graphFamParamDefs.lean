/-
  WilG4a / CD — the two coordinate maps used to pull a family back along a parametrisation.

  Vocabulary for the target `Work.WilG4a.CD.graphFam_param_mem`.  Given a `p`-parameter family
  `f` and a parametrisation `Ψ : ℝ^k → ℝ^p`, the graph of `(u,x) ↦ f (Ψ u) x` is obtained in the
  ambient space `ℝ^{(k+1+1)+p}` with layout `(u, x, y, v)`:

  * `pullIdxA` selects `(u, v)` out of `(u, x, y, v)`, so that the pullback of `paramGraph Ψ`
    expresses `v = Ψ u` (the layout of `paramGraph` is "first `k` coordinates the parameter,
    last `p` the value");
  * `pullIdxB` selects `(v, x, y)`, so that the pullback of `graphFam f` expresses `y = f v x`.

  The intersection of the two pullbacks, projected away from the `p` coordinates `v` by
  `Work.WilG0.projLastIter (k+1+1) p`, is exactly `graphFam (fun u x => f (Ψ u) x)`; this
  set-theoretic identity is proved in `Submission.Work.WilG4a.CD.pullProjGraphFam`.
-/
import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.subst_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a.CD

open Work.WilG0

/-- The coordinate map `Fin (k+p) → Fin ((k+1+1)+p)` which sends the first `k` coordinates to
the `u`-block `0, …, k-1` and the last `p` coordinates to the `v`-block `k+1+1, …, (k+1+1)+p-1`
of the ambient space with layout `(u, x, y, v)`. -/
def pullIdxA (k p : ℕ) : Fin (k + p) → Fin ((k + 1 + 1) + p) :=
  Fin.addCases (fun i : Fin k => Fin.castAdd p (Fin.castSucc (Fin.castSucc i)))
    (fun j : Fin p => Fin.natAdd (k + 1 + 1) j)

/-- The coordinate map `Fin (p+1+1) → Fin ((k+1+1)+p)` which sends the first `p` coordinates to
the `v`-block and the last two to the `x`- and `y`-coordinates `k`, `k+1` of the ambient space
with layout `(u, x, y, v)`. -/
def pullIdxB (k p : ℕ) : Fin (p + 1 + 1) → Fin ((k + 1 + 1) + p) :=
  Fin.addCases (m := p) (n := 1 + 1) (fun j : Fin p => Fin.natAdd (k + 1 + 1) j)
    (fun i : Fin (1 + 1) => ⟨k + i.val, by have := i.isLt; omega⟩)

/-! ## Values of the coordinate maps at the distinguished indices -/

@[simp] theorem pullIdxA_natAdd (k p : ℕ) (j : Fin p) :
    pullIdxA k p (Fin.natAdd k j) = Fin.natAdd (k + 1 + 1) j := by
  simp [pullIdxA]

@[simp] theorem pullIdxA_castAdd (k p : ℕ) (i : Fin k) :
    pullIdxA k p (Fin.castAdd p i) = Fin.castAdd p (Fin.castSucc (Fin.castSucc i)) := by
  simp [pullIdxA]

@[simp] theorem pullIdxB_castAdd (k p : ℕ) (j : Fin p) :
    pullIdxB k p (Fin.castAdd (1 + 1) j) = Fin.natAdd (k + 1 + 1) j := by
  simp [pullIdxB]

theorem pullIdxB_castSucc_castSucc (k p : ℕ) (i : Fin p) :
    pullIdxB k p (Fin.castSucc (Fin.castSucc i)) = Fin.natAdd (k + 1 + 1) i := by
  have h : (Fin.castSucc (Fin.castSucc i) : Fin (p + 1 + 1)) = Fin.castAdd (1 + 1) i :=
    Fin.ext rfl
  rw [h, pullIdxB_castAdd]

theorem pullIdxB_last (k p : ℕ) :
    pullIdxB k p (Fin.last (p + 1)) = Fin.castAdd p (Fin.last (k + 1)) := by
  have h : (Fin.last (p + 1) : Fin (p + 1 + 1)) = Fin.natAdd p (1 : Fin (1 + 1)) := Fin.ext rfl
  rw [h, pullIdxB, Fin.addCases_right]
  rfl

theorem pullIdxB_castSucc_last (k p : ℕ) :
    pullIdxB k p (Fin.castSucc (Fin.last p)) =
      Fin.castAdd p (Fin.castSucc (Fin.last k)) := by
  have h : (Fin.castSucc (Fin.last p) : Fin (p + 1 + 1)) = Fin.natAdd p (0 : Fin (1 + 1)) :=
    Fin.ext rfl
  rw [h, pullIdxB, Fin.addCases_right]
  rfl

end Work.WilG4a.CD
