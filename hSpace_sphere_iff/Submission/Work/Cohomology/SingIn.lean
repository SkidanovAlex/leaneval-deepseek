/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The singular simplices lying inside a subset

For a topological space `X` and a subset `W ⊆ X`, `singIn X W` is the sub-simplicial-set of the
singular simplicial set `Sing X` consisting of the singular simplices whose image is contained in
`W`.  It is the geometric input of the small-simplex (Mayer–Vietoris) machine: for an open cover
`X = U ∪ V` the subcomplex `singIn X U ⊔ singIn X V` of `Sing X` has the same cohomology as
`Sing X`, and the two pieces and their intersection are the singular complexes of the subspaces
`U`, `V`, `U ∩ V`.
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Cover

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

variable {X : TopCat.{0}}

/-- The subcomplex of `Sing X` of the simplices whose image lies in `W`. -/
def singIn (X : TopCat.{0}) (W : Set X) : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∀ t, TopCat.toSSetObjEquivT X n σ t ∈ W}
  map {n m} i σ hσ t := by
    have h : TopCat.toSSetObjEquivT X m ((TopCat.toSSet.obj X).map i σ) t
        = TopCat.toSSetObjEquivT X n σ (stdSimplex.map i.unop t) :=
      TopCat.toSSetObjEquivT_naturality_apply (X := X) (f := i.unop) σ t
    rw [h]
    exact hσ _

@[simp] lemma mem_singIn_iff {W : Set X} {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (singIn X W).obj n ↔ ∀ t, TopCat.toSSetObjEquivT X n σ t ∈ W := Iff.rfl

lemma singIn_mono {W W' : Set X} (h : W ⊆ W') : singIn X W ≤ singIn X W' :=
  fun _n _σ hσ _t => h (hσ _)

@[simp] lemma singIn_univ (X : TopCat.{0}) : singIn X (Set.univ : Set X) = ⊤ := by
  ext n σ
  simp

lemma singIn_inter (X : TopCat.{0}) (U V : Set X) :
    singIn X (U ∩ V) = singIn X U ⊓ singIn X V := by
  ext n σ
  constructor
  · intro h
    exact ⟨fun t => (h t).1, fun t => (h t).2⟩
  · intro h t
    exact ⟨h.1 t, h.2 t⟩

end

end Submission.Cohomology
