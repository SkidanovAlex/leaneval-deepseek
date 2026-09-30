import Mathlib
import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.RatHurewicz.Bridge.H_faces
import Submission.Work.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.Serre.Defs

/-!
# SUBPROJECT SERRE — E0 in range form: the vocabulary

Blueprint `Submission/Work/Drive/SERRE_BLUEPRINT.md`, ADDENDUM 1 (C) ("the singular cone
construction").  The statement `Work.Serre.SerreE0Range` says:

> if `πᵢ(X,x₀) = 0` for `i ≤ N` then `H̃ⱼ(X;ℚ) = 0` for `0 < j ≤ N`.

The blueprint's proof is the elementary cone construction: for every singular simplex `σ` one
chooses a **filler** `H σ` of the prescribed boundary of `σ` (all faces `dᵢ H σ = H (dᵢ σ)` except
the last, which is `σ` itself), which exists because the corresponding map `∂Δ^{n+1} → X` is
null-homotopic as soon as `πₙ` vanishes.  The fillers give a chain contraction
`∂ s + s ∂ = id` of the singular chain complex in degrees `≤ N`, hence the vanishing of the
homology there.

## What this file contains

* `Work.Serre.SSetConeData K N` — the cone/filler data on a simplicial set `K` up to degree `N`;
* `Work.Serre.singSSet X` — the singular simplicial set of `X`;
* `Work.Serre.HasSimplexCones X N` — the existence of that data for `X`;
* the two halves of the theorem as separate statements:
  `hasSimplexCones_of_homotopyGroup_subsingleton` (geometry — this is where the cone construction
  lives) and `ratVanishingBelow_of_hasSimplexCones` (chain algebra).

The splitting is recorded because the two halves are independent and are proved separately.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-- The singular simplicial set of a topological space. -/
abbrev singSSet (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

/-- **Cone (filler) data on a simplicial set `K`, in degrees `≤ N`.**

`H n σ` is the chosen `(n+1)`-simplex filling the boundary of an `n`-simplex `σ`: its `i`-th face
is the filler of the `i`-th face of `σ` (`face_cast`), and its *last* face is `σ` (`face_last`).
The values of `H` above degree `N` are unconstrained: they exist only so that `H` is a single
function. -/
structure SSetConeData (K : SSet) (N : ℕ) where
  /-- The filler of a simplex. -/
  H : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌
  /-- The non-last faces of the filler of `σ` are the fillers of the faces of `σ`. -/
  face_cast : ∀ m : ℕ, m + 1 ≤ N → ∀ (σ : K _⦋m+1⦌) (i : Fin (m+2)),
    K.δ (Fin.castSucc i) (H (m+1) σ) = H m (K.δ i σ)
  /-- The last face of the filler of `σ` is `σ` itself. -/
  face_last : ∀ m : ℕ, m ≤ N → ∀ (σ : K _⦋m⦌), K.δ (Fin.last (m+1)) (H m σ) = σ

/-- The cone data exists for the singular simplicial set of `X` in degrees `≤ N`. -/
def HasSimplexCones (X : Type) [TopologicalSpace X] (N : ℕ) : Prop :=
  Nonempty (SSetConeData (singSSet X) N)

/-! The two halves of the theorem (`hasSimplexCones_of_homotopyGroup_subsingleton` and
`ratVanishingBelow_of_hasSimplexCones`) are proved in `Submission/Work/Serre/E0Assembly.lean` and
`Submission/Work/Serre/e0ChainAlgebra.lean` respectively. -/

end

end Work.Serre
