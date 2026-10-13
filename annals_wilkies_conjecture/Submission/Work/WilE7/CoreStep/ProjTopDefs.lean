/-
  `Work.WilE7.CoreStep.ProjTopDefs`: the map `projTop` of the `(n+1)`-projection in the swapped
  picture, and its elementary properties.

  At level `n+1` the ambient space of a piece is `ℝ^{n+(m+1)}` (base = the first `n` coordinates,
  fibre = the last `m+1`, of which the **last** is the vertical coordinate that `π_{n+1}` keeps —
  this is the `vertSwap`-normalised picture of `NOTES_S32_CoreLT_succ_design.md` §2).  The
  `(n+1)`-projection `π_{n+1}` is therefore the map

  `projTop n m z = (z 0, …, z (n-1), z (n+m))`,

  i.e. the first `n` coordinates followed by the *last* coordinate of the fibre.  In the `Fin`
  bookkeeping this is `Fin.snoc (projFirst n (m+1) z) (projSnd n (m+1) z (Fin.last m))`.

  The cells over a base cell `C ⊆ ℝ^n` live in the cylinder `cyl C = {z | Fin.init z ∈ C}`
  (`Work.WilE7.cyl`, with the additional cube bound `|z (last n)| ≤ 1`).
-/
import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.stratGraph

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- The `(n+1)`-projection in the swapped picture `ℝ^{n+(m+1)}`: the first `n` coordinates
followed by the last coordinate of the fibre. -/
def projTop (n m : ℕ) (z : Fin (n + (m + 1)) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (projFirst n (m + 1) z) (projSnd n (m + 1) z (Fin.last m))

@[simp] theorem projTop_init (n m : ℕ) (z : Fin (n + (m + 1)) → ℝ) :
    Fin.init (projTop n m z) = projFirst n (m + 1) z :=
  Fin.init_snoc ..

@[simp] theorem projTop_last (n m : ℕ) (z : Fin (n + (m + 1)) → ℝ) :
    projTop n m z (Fin.last n) = projSnd n (m + 1) z (Fin.last m) :=
  Fin.snoc_last ..

theorem projTop_castSucc (n m : ℕ) (z : Fin (n + (m + 1)) → ℝ) (i : Fin n) :
    projTop n m z i.castSucc = projFirst n (m + 1) z i :=
  Fin.snoc_castSucc ..

/-- `projTop` is continuous. -/
theorem continuous_projTop (n m : ℕ) : Continuous (projTop n m) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ ?_ i
  · have he : (fun z : Fin (n + (m + 1)) → ℝ => projTop n m z (Fin.last n))
        = fun z => projSnd n (m + 1) z (Fin.last m) := by
      funext z; rw [projTop_last]
    rw [he]
    exact (continuous_apply (Fin.last m)).comp (Work.WilE7.continuous_projSnd n (m + 1))
  · intro i'
    have he : (fun z : Fin (n + (m + 1)) → ℝ => projTop n m z i'.castSucc)
        = fun z => projFirst n (m + 1) z i' := by
      funext z; rw [projTop_castSucc]
    rw [he]
    exact (continuous_apply i').comp (Work.WilE7.continuous_projFirst n (m + 1))

/-- The `if`-form of `projTop` used in `Work.CoreStep.projTop_graph_union`. -/
theorem projTop_eq_ite (n m : ℕ) (z : Fin (n + (m + 1)) → ℝ) :
    projTop n m z = fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n then z ⟨i, by omega⟩ else z ⟨n + m, by omega⟩ := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [projTop_last, dif_neg (by simp : ¬ (((Fin.last n : Fin (n + 1)) : ℕ)) < n)]
    simp [projSnd, Fin.last]
  · intro i'
    rw [projTop_castSucc, dif_pos (by simp : (((i'.castSucc : Fin (n + 1)) : ℕ)) < n)]
    exact congrArg z (Fin.ext rfl)

/-- The `projTop`-image of a piece. -/
def projTopSet {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) :
    Set (Fin (n + 1) → ℝ) :=
  projTop n m '' Work.WilE7.MainDesign.absSet T

end Work.WilE7.CoreStep
