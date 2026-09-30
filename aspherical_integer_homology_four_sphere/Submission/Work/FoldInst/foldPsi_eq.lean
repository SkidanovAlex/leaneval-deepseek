import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.Dvor_disjoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-- **Uniqueness of the representative attached to a point of a Voronoi piece.**  Since two
distinct sign indices have disjoint Voronoi pieces (`Dvor_disjoint`), a point of `Xbar` lies in at
most one piece `Dvor i r`. -/
theorem Dvor_eq_of_mem {i : Fin 98} {r s : Fin (foldCodim i) → Bool} {x : Xbar}
    (hr : x ∈ Dvor i r) (hs : x ∈ Dvor i s) : r = s := by
  by_contra h
  exact (Set.disjoint_left.mp (Dvor_disjoint i h) hr) hs

/-- **The glued chart value on its own piece.**  On the Voronoi piece `Dvor i r` the glued value
`foldPsi i` — which picks the (unique) representative whose piece contains the point — coincides
with `foldTheta i r`.  Uniqueness is `Dvor_eq_of_mem`, i.e. the disjointness of the pieces. -/
theorem foldPsi_eq (i : Fin 98) {r : Fin (foldCodim i) → Bool} {x : Xbar}
    (hx : x ∈ Dvor i r) : foldPsi i x = foldTheta i r x.2.1 := by
  classical
  have h : ∃ r : Fin (foldCodim i) → Bool, x ∈ Dvor i r := ⟨r, hx⟩
  unfold foldPsi
  rw [dite_eq_left h]
  have hc : h.choose = r := Dvor_eq_of_mem h.choose_spec hx
  rw [hc]

end Work.FoldInst
