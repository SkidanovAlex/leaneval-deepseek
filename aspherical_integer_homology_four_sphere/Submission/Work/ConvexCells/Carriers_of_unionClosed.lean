import Mathlib
import Submission.Work.ConvexCells.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ConvexCells

open scoped BigOperators

/-- For a point `x` of the polytope, its tight set is the union of the tight sets of the faces
`gface i` over the constraints `i` that are tight at `x`.

Indeed, `j ∈ tightAt x` implies `j ∈ tight (gface j)` by `Ok.gface_mem`; conversely if `i` is tight
at `x` then every constraint of `tight (gface i)` is tight at `x` by `tight_gface_subset`. -/
theorem tightAt_eq_sup {d : ℕ} (P : PolytopeData d) (h : P.Ok) {x : E d} (hx : x ∈ P.Pset) :
    P.tightAt x = (P.tightAt x).sup (fun i => P.tight (P.gface i)) := by
  ext j
  rw [Finset.mem_sup]
  constructor
  · intro hj
    exact ⟨j, hj, PolytopeData.Ok.gface_mem P h j⟩
  · rintro ⟨i, hi, hji⟩
    rw [PolytopeData.tightAt_of_mem P hx j]
    have hi' : inner ℝ (P.nR i) x = P.bR i := (PolytopeData.tightAt_of_mem P hx i).mp hi
    exact PolytopeData.tight_gface_subset P h i hx hi' j hji

/-- A finite union of tight sets of the faces `gface i`, `i ∈ s`, is the tight set of a listed
face. This is the induction on the finite set `s` using `UnionClosed` for the binary unions, with
`P.top` (of empty tight set) as the base case. -/
theorem exists_tight_sup {d : ℕ} (P : PolytopeData d) (h : P.Ok) (hu : P.UnionClosed)
    (s : Finset (Fin P.m)) :
    ∃ f : Fin P.K, P.tight f = s.sup (fun i => P.tight (P.gface i)) := by
  induction s using Finset.induction with
  | empty =>
      refine ⟨P.top, ?_⟩
      rw [Finset.sup_empty, PolytopeData.Ok.tight_top P h]
      rfl
  | insert a s ha ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨g, hg⟩ := hu f (P.gface a)
      refine ⟨g, ?_⟩
      rw [Finset.sup_insert, hg, hf, Finset.union_comm]
      rfl

/-- If the face family is closed under unions of tight sets, then every point of the polytope has
its tight set among the listed faces: for `x ∈ Pset`, `tightAt x = ⋃_{i ∈ tightAt x} tight (gface i)`
(one inclusion is `Ok.gface_mem`, the other `tight_gface_subset`), and a finite union of tight sets
of listed faces is again the tight set of a listed face. -/
theorem Carriers_of_unionClosed {d : ℕ} (P : PolytopeData d) (h : P.Ok) (hu : P.UnionClosed) :
    P.Carriers := by
  intro x hx
  obtain ⟨f, hf⟩ := exists_tight_sup P h hu (P.tightAt x)
  exact ⟨f, by rw [hf, ← tightAt_eq_sup P h hx]⟩

end Work.ConvexCells
