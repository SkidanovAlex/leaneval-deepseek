import Mathlib

/-!
# The level-`n` dyadic nerve of the interval (definitions)

Fix `M ≥ 1` (in the application `M = 2^{n+1}`, the number of intervals in the `n`-th dyadic
subdivision of `[0,1]`).  A `p`-simplex of the *level-`n` dyadic nerve* is a `(p+1)`-tuple of
vertices of `{0, …, M-1}` whose diameter is at most one, i.e. the corresponding closed dyadic
intervals have a common point.  The face maps delete a coordinate, and the differential of the
associated complex is the alternating sum of the pullbacks.

This is the combinatorial input for the exactness of the *dual* Čech complex of the Cantor cover
of the interval (see `Submission/Work/ANALYTIC/NOTES_HI_pt.md`).
-/

namespace Work.ANALYTIC.CechPt.Level

/-- The `p`-simplices of the level-`n` dyadic nerve of the interval: `(p+1)`-tuples of vertices of
`{0, …, M-1}` of diameter at most one. -/
def lev (M p : ℕ) : Type := { x : Fin (p + 1) → Fin M // ∀ i j, (x i : ℕ) ≤ (x j : ℕ) + 1 }

/-- The `i`-th face map (deleting the `i`-th coordinate). -/
def face {M p : ℕ} (i : Fin (p + 2)) (x : lev M (p + 1)) : lev M p :=
  ⟨fun j => x.1 (Fin.succAbove i j),
    fun a b => x.2 (Fin.succAbove i a) (Fin.succAbove i b)⟩

/-- The alternating sum of pullbacks along the face maps. -/
def diff {M p : ℕ} (f : lev M p → ℤ) : lev M (p + 1) → ℤ :=
  fun x => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) * f (face i x)

end Work.ANALYTIC.CechPt.Level
