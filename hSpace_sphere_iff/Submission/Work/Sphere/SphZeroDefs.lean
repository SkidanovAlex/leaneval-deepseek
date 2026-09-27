/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The zero sphere `S⁰` and its constant singular simplices

`S⁰ = Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1` is the two point space `{p,q}` with
`p = polePt 0` and `q = negPolePt 0`.  Every singular simplex of `S⁰` is constant (the standard
simplex `Δⁿ` is connected and `S⁰` is discrete), a fact proved in
`Submission/Work/Sphere/SphZeroSimplexConst.lean`.  This file collects the definitions needed to
state that fact and to compute the cohomology of `S⁰` from it:

* `basepoint n`: a chosen point of `Δⁿ`;
* `constSimplex n x`: the constant singular `n`-simplex at `x : S⁰`;
* `simplexVal n σ`: the value of `σ` at the basepoint of `Δⁿ`.

The two elementary lemmas `simplexVal_constSimplex` (the value of a constant simplex is the point)
and `face_constSimplex` (the faces of a constant simplex are constant simplices at the same point)
are proved here.
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Sphere.Suspension

open CategoryTheory Simplicial Opposite

namespace Work.Sphere

noncomputable section

/-- A chosen basepoint of the standard `n`-simplex `Δⁿ`: the `0`-th vertex. -/
def basepoint (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) :=
  ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩

/-- The constant singular `n`-simplex of `S⁰` at a point `x`. -/
def constSimplex (n : ℕ) (x : Submission.Sphere.Sph 0) :
    (Submission.Sphere.singSph 0).obj (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSetObjEquivT (Submission.Sphere.Sph 0) (Opposite.op (SimplexCategory.mk n))).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) x)

/-- The value at the basepoint of `Δⁿ` of a singular `n`-simplex of `S⁰`. -/
def simplexVal (n : ℕ)
    (σ : (Submission.Sphere.singSph 0).obj (Opposite.op (SimplexCategory.mk n))) :
    Submission.Sphere.Sph 0 :=
  (TopCat.toSSetObjEquivT (Submission.Sphere.Sph 0) (Opposite.op (SimplexCategory.mk n))) σ
    (basepoint n)

/-- The value of a constant simplex is the point it is constant at. -/
lemma simplexVal_constSimplex (n : ℕ) (x : Submission.Sphere.Sph 0) :
    simplexVal n (constSimplex n x) = x := by
  simp [simplexVal, constSimplex]

/-- The faces of a constant simplex are the constant simplices at the same point. -/
lemma face_constSimplex (n : ℕ) (i : Fin (n + 2)) (x : Submission.Sphere.Sph 0) :
    (Submission.Sphere.singSph 0).map (SimplexCategory.δ i).op (constSimplex (n + 1) x)
      = constSimplex n x := by
  apply (TopCat.toSSetObjEquivT (Submission.Sphere.Sph 0)
    (Opposite.op (SimplexCategory.mk n))).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  rw [TopCat.toSSetObjEquivT_naturality_apply]
  simp [constSimplex]

end

end Work.Sphere
