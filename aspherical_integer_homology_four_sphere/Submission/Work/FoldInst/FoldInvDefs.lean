/-
# The Klein-coordinate inverse of a fold chart, and the canonical lift into a Voronoi piece

The fold chart map of the class `i` and the sign index `r` is

  `foldTheta i r = coordPerm i ∘ mobiusKlein (N_F · D_r)`,

the coordinate permutation of the model composed with the Klein action of the *Lorentz* matrix
`N_F · D_r = foldNr i * foldDrR i r`.  On the Klein ball `mobiusKlein` is inverted by

  `z ↦ kleinOfHyp (A⁻¹ · hypOfUHS z)`

(undo the upper-half-space presentation `uhsOfHyp`, apply the inverse Lorentz matrix, project the
upper sheet back to the Klein ball); composing with the inverse coordinate permutation
`coordPermInv i` gives the *Klein inverse* `foldInv i r` of the chart defined below.

This file only holds the definitions and their elementary consequences, so that the lemmas about
`foldInv` can be stated and proved without depending on the (in-flight) assembly of the fold
charts.  The two analytic facts about `foldInv` are proved in the sibling files

* `Submission.Work.FoldInst.foldInv_foldTheta` — `foldInv i r (foldTheta i r y) = y` for `y` in the
  Klein ball, and
* `Submission.Work.FoldInst.continuousOn_foldInv` — `foldInv i r` is continuous on the image of the
  Klein ball.
-/
import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.isOpen_foldTheta_image
import Submission.Work.FoldInst.foldPsi_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Matrix

namespace Work.FoldInst

/-! ### The inverse of the chart map -/

/-- **The Klein-coordinate inverse of the fold chart** of the class `i` and the sign index `r`:
undo the coordinate permutation (`coordPermInv i`), lift the upper half space point to the upper
sheet (`hypOfUHS`), apply the inverse of the Lorentz matrix `N_F · D_r`, and project back to the
Klein ball (`kleinOfHyp`). -/
def foldInv (i : Fin 98) (r : Fin (foldCodim i) → Bool) (z : E4) : E4 :=
  HypModel.kleinOfHyp ((foldNr i * foldDrR i r)⁻¹ *ᵥ HypModel.hypOfUHS (coordPermInv i z))

/-! ### The canonical lift of a chart value into the copy `Q̄` of a Voronoi piece -/

/-- The origin is a point of the truncated 24-cell: all its slacks are `1` and `4/5`. -/
theorem zero_mem_Qbar : (0 : E4) ∈ Qbar := by
  constructor
  · intro S
    rw [sideSlack]
    simp
  · intro w
    rw [truncSlack]
    norm_num

/-- The default point of `X̄ = ZMod 2 × Q̄`, used to make the partial constructions below total. -/
def baseXbar : Xbar := (0, (⟨0, zero_mem_Qbar⟩ : Qbar))

/-- **The canonical candidate for the point of the piece mapping to a chart value `z`.**
The Klein inverse `foldInv i r z`, placed in the copy `foldCr i r` of `Q̄`.  The `if` is only a
guard making the definition total on `E4`; on a chart value that actually lies in the image of the
piece `Dvor i r` the point satisfies the Voronoi conditions by construction (see
`piecePt_mem_Dvor`). -/
noncomputable def piecePt (i : Fin 98) (r : Fin (foldCodim i) → Bool) (z : E4) : Xbar := by
  classical
  exact if h : foldInv i r z ∈ Qbar then (foldCr i r, (⟨foldInv i r z, h⟩ : Qbar)) else baseXbar

/-- On a chart value whose Klein inverse lies in `Q̄` — in particular on the image of the piece —
the second coordinate of `piecePt` is the Klein inverse itself. -/
theorem piecePt_snd {i : Fin 98} {r : Fin (foldCodim i) → Bool} {z : E4}
    (h : foldInv i r z ∈ Qbar) : (piecePt i r z).2.1 = foldInv i r z := by
  rw [piecePt, dite_eq_left h]

/-- The second coordinate of `piecePt` is the Klein inverse whenever the guard is satisfied.  This
is the form in which the definition unfolds on the image of the piece. -/
theorem piecePt_snd' {i : Fin 98} {r : Fin (foldCodim i) → Bool} {z : E4}
    (h : foldInv i r z ∈ Qbar) : (piecePt i r z).2 = (⟨foldInv i r z, h⟩ : Qbar) := by
  rw [piecePt, dite_eq_left h]

/-- The image in `M̄` of `piecePt` at a chart value whose Klein inverse lies in `Q̄` — the form in
which the definition unfolds on the image of a piece. -/
theorem mk_piecePt_eq {i : Fin 98} {r : Fin (foldCodim i) → Bool} {z : E4}
    (h : foldInv i r z ∈ Qbar) :
    mk (piecePt i r z) = mk ((foldCr i r, (⟨foldInv i r z, h⟩ : Qbar)) : Xbar) := by
  rw [piecePt, dite_eq_left h]

/-- **A chart value in the image of a Voronoi piece comes from a point of the piece.**  On the
piece `Dvor i r` the glued value is `foldTheta i r` (`foldPsi_eq`). -/
theorem exists_witness_of_mem (i : Fin 98) (r : Fin (foldCodim i) → Bool) {z : E4}
    (hz : z ∈ foldPsi i '' Dvor i r) : ∃ x ∈ Dvor i r, foldTheta i r x.2.1 = z := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, hx, (foldPsi_eq i hx).symm⟩

/-- A chart value in the image of the piece lies in the image of the ball under the chart map. -/
theorem mem_image_ball_of_mem (i : Fin 98) (r : Fin (foldCodim i) → Bool) {z : E4}
    (hz : z ∈ foldPsi i '' Dvor i r) : z ∈ foldTheta i r '' HypModel.ball := by
  obtain ⟨x, hx, hxz⟩ := exists_witness_of_mem i r hz
  exact ⟨x.2.1, Dvor_subset_ball i r hx, hxz⟩

end Work.FoldInst
