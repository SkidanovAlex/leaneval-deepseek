import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Charts

/-- **A curve has infinitely many places.**  Removing finitely many places from a curve
leaves infinitely many places: the complement of a finite set of closed points of a
one-dimensional scheme of finite type over a field is infinite.

The proof is topological.  If only finitely many places remained outside `S`, then the set
`closedPoints C.left` of all closed points of the curve would be a finite union of closed
singletons, hence closed.  A curve is a Jacobson space, so its closed points are dense;
thus every point of the curve would be closed.  But the generic point of the (irreducible)
curve is not closed: its closure is all of the curve, so if it were closed the curve would
consist of a single point, contradicting `Nontrivial C.left`. -/
theorem infinite_places_compl_finset {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) (S : Finset C.Place) :
    {P : C.Place | P ∉ S}.Infinite := by
  rw [Set.Infinite]
  intro hcomp
  -- The places `S ∪ (places outside S)` are all the closed points of `C`.
  have hS : (↑S : Set C.Place).Finite := S.finite_toSet
  have hcov : (↑S : Set C.Place) ∪ {P | P ∉ S} = Set.univ := by
    ext P; by_cases h : P ∈ S <;> simp [Set.mem_union, h]
  have hcp : (closedPoints C.left).Finite := by
    have h1 := (hS.union hcomp).image (fun P : C.Place => (P : C.left))
    rwa [hcov, Set.image_univ, Subtype.range_coe] at h1
  -- Finitely many closed points force the (Jacobson) topology to be discrete.
  haveI : DiscreteTopology C.left := JacobsonSpace.discreteTopology hcp
  -- Hence the generic point is closed, but its closure is the whole curve.
  have hclosed : IsClosed ({genericPoint C.left} : Set C.left) := by
    simpa using ((discreteTopology_iff_forall_isOpen.mp inferInstance)
      ({genericPoint C.left}ᶜ)).isClosed_compl
  have h2 : (Set.univ : Set C.left) = {genericPoint C.left} := by
    rw [← genericPoint_closure C.left, hclosed.closure_eq]
  -- So the curve has at most one point, contradicting `Nontrivial C.left`.
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial C.left)
  exact hxy (by
    have hx : x ∈ ({genericPoint C.left} : Set C.left) := by rw [← h2]; trivial
    have hy : y ∈ ({genericPoint C.left} : Set C.left) := by rw [← h2]; trivial
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy])

end Work.Charts
