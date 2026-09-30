/-
# The generic-fibre sum of a pencil

Let `C` be a curve over a field `k`, `h ∈ K(C)` transcendental over `k`, `K := k(h) ⊆ K(C)`,
`E := K(C)` and `N` a finite Galois extension of `K` containing (the images of) all `K`-embeddings
of `E`: for instance `N` = the normal closure of `E/K`.  For every `K`-embedding
`σ : E →ₐ[K] N` the composite

  `Spec N --Spec σ--> Spec E --(generic point of C)--> C`

is an `N`-point of `C`; composed with `f : C.toOver ⟶ A` (A a commutative group scheme over `k`)
it gives an `N`-point of `A`.  The **generic-fibre sum** `genericSum` is the product of these
`n = [E : K]` points, an element of `A(N)`.

It is the "value at the generic point of the pencil" of the fibrewise-sum morphism:  the `n`
points above are exactly the geometric points of the generic fibre of the pencil of `h`.  The two
facts about it that the proof of the key lemma uses are

* `Work.KeyLemma.Curve.genericSum_galois` (in `genericSum_galois.lean`): `genericSum` is
  invariant under `Gal(N/K)` (which permutes the `σ`),
* `Work.KeyLemma.Curve.exists_genericSum_descend` (in `exists_genericSum_descend.lean`): hence it
  descends to an element `a ∈ A(K)`.

## Main definitions

* `Work.KeyLemma.Curve.baseField C h` : `k(h) ⊆ K(C)`
* `Work.KeyLemma.Curve.genericPt C` : the generic point `Spec K(C) ⟶ C`
* `Work.KeyLemma.Curve.conjPt`, `conjPtOver` : the conjugate `N`-points
* `Work.KeyLemma.Curve.genericSumOver`, `genericSum` : their product
-/
import Mathlib
import Submission.Work.Descent.galoisDescent_point
import Submission.Work.CurveBasics.Linear.FunctionFieldPoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma.Curve

open Work.CurveBasics

noncomputable section

variable {k : Type u} [Field k]

/-- The subfield `k(h) ⊆ K(C)` generated over `k` by a rational function `h`. -/
abbrev baseField (C : Curve k) (h : C.functionField) : IntermediateField k ↥C.functionField :=
  IntermediateField.adjoin k ({h} : Set ↥C.functionField)

/-- The generic point of `C`, as a morphism `Spec K(C) ⟶ C`. -/
abbrev genericPt (C : Curve k) : Spec (CommRingCat.of ↥C.functionField) ⟶ C.left :=
  C.left.fromSpecStalk (genericPoint C.left)

/-- `Spec N` as a `k`-scheme. -/
abbrev specOver (N : Type u) [Field N] [Algebra k N] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k N)))

variable (C : Curve k) (h : C.functionField)

/-- The `N`-point of `C` attached to a `K`-embedding `σ : K(C) →ₐ[K] N`: the generic point of `C`
base changed along `σ`. -/
abbrev conjPt (N : Type u) [Field N] [Algebra ↥(baseField C h) N]
    (σ : ↥C.functionField →ₐ[↥(baseField C h)] N) :
    Spec (CommRingCat.of N) ⟶ C.left :=
  Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ genericPt C

variable {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A)

section Sum

variable (N : Type u) [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
  [IsScalarTower k ↥(baseField C h) N]
  [FiniteDimensional ↥(baseField C h) ↥C.functionField]

/-- The image in `A` of the conjugate `N`-point attached to `σ`. -/
abbrev conjPtOver (σ : ↥C.functionField →ₐ[↥(baseField C h)] N) : specOver N ⟶ A :=
  Over.homMk (conjPt C h N σ ≫ f.left) (by
    rw [Category.assoc, Over.w f]
    dsimp only [conjPt, genericPt, specOver]
    rw [Category.assoc, Curve.fromSpecStalk_genericPoint_comp_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact (AlgHom.commutes σ x).trans (IsScalarTower.algebraMap_apply k ↥(baseField C h) N x).symm)

/-- **The generic-fibre sum**: the product in `A(N)` of the images of the `n = [K(C) : k(h)]`
conjugate points of the generic fibre of the pencil of `h`. -/
abbrev genericSumOver : specOver N ⟶ A :=
  ∏ σ : ↥C.functionField →ₐ[↥(baseField C h)] N, conjPtOver (C := C) (h := h) (N := N) f σ

/-- The generic-fibre sum, as a morphism `Spec N ⟶ A`. -/
abbrev genericSum : Spec (CommRingCat.of N) ⟶ A.left :=
  (genericSumOver (C := C) (h := h) (N := N) f).left

end Sum

end

end Work.KeyLemma.Curve
