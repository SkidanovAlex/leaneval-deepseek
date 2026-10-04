import Mathlib
import Submission.Work.Diff.EXT.lapComm_tower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tuple bookkeeping for the jet-level Weitzenböck (Laplacian-commutator) estimate

This module only collects the tuple-manipulation definitions used by the statement and the
proof of `Work.Diff.EXT.evolX.lapComm_src_jets` (and of the two supporting lemmas
`Work.Diff.EXT.evolX.lapOpE_jetAll` and `Work.Diff.EXT.evolX.ckt_adjacent_swap_bound`):

* `Work.Diff.EXT.evolX.tupIns m j Ef G i` — the tuple
  `(G_0, …, G_{j-1}, Ef i, Ef i, G_j, …, G_{m+3+j})` of arity `(m+2+j)+4`: this is the tuple on
  which the `j`-th jet of the frame-traced tower operator `lapOpE Ef g m` is evaluated (the `j`
  differentiation directions come first, then the two frame slots, then the remaining entries of
  `G`);

* `Work.Diff.EXT.evolX.tupSwap d p hp G` — the tuple `G : Fin (d+4) → TField` with the entries at
  positions `p` and `p+1` exchanged (both are *derivative* slots of the level-`d` tower when
  `p + 2 ≤ d`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The tuple `(G_0, …, G_{j-1}, Ef i, Ef i, G_j, …, G_{m+3+j})`, of arity `(m+2+j)+4`.
This is the tuple of the `j`-th jet of `lapOpE Ef g m`: the `j` derivative directions
`G_0,…,G_{j-1}` come first, then the two slots of the traced (second) derivative carrying the
frame field `Ef i`, then the remaining entries of `G`. -/
noncomputable def tupIns (m j : ℕ)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) :
    Fin ((m + 2 + j) + 4) → Work.Diff.EXT.TField (I := I) (M := M) :=
  fun r => Fin.append (fun t : Fin j => G ⟨t.val, by omega⟩)
      (Fin.cons (Ef i) (Fin.cons (Ef i) (fun t : Fin (m + 4) => G ⟨j + t.val, by omega⟩)))
      (Fin.cast (by omega) r)

/-- The tuple `G : Fin (d+4) → TField` with the entries at positions `p` and `p+1` swapped.
For `p + 2 ≤ d` both positions are *derivative* slots of the level-`d` tower. -/
noncomputable def tupSwap (d p : ℕ) (hp : p + 2 ≤ d)
    (G : Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M) :=
  fun r => G (if (r : ℕ) = p then ⟨p + 1, by omega⟩
    else if (r : ℕ) = p + 1 then ⟨p, by omega⟩ else r)

/-- `tupSwap` fixes the entries at all positions other than `p` and `p+1`. -/
theorem tupSwap_of_ne {d p : ℕ} {hp : p + 2 ≤ d}
    (G : Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M))
    {r : Fin (d + 4)} (h1 : (r : ℕ) ≠ p) (h2 : (r : ℕ) ≠ p + 1) :
    tupSwap (I := I) (M := M) d p hp G r = G r := by
  simp only [tupSwap]
  rw [if_neg h1, if_neg h2]

/-- `tupSwap` exchanges the entries at positions `p` and `p+1`. -/
theorem tupSwap_at_p {d p : ℕ} {hp : p + 2 ≤ d}
    (G : Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M)) :
    tupSwap (I := I) (M := M) d p hp G ⟨p, by omega⟩ = G ⟨p + 1, by omega⟩ := by
  simp [tupSwap]

/-- `tupSwap` exchanges the entries at positions `p` and `p+1` (second slot). -/
theorem tupSwap_at_p_succ {d p : ℕ} {hp : p + 2 ≤ d}
    (G : Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M)) :
    tupSwap (I := I) (M := M) d p hp G ⟨p + 1, by omega⟩ = G ⟨p, by omega⟩ := by
  simp [tupSwap]

end Work.Diff.EXT.evolX
