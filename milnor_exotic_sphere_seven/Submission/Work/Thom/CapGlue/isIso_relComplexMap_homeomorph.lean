import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.relCohHomeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory

namespace Work.Thom.CapGlue

/-- **A homeomorphism of pairs induces an isomorphism on relative cohomology.**

For a homeomorphism `e : X ≃ₜ Y` carrying a subset `A ⊆ X` onto a subset `B ⊆ Y`
(the hypothesis `he : ∀ x, x ∈ A ↔ e x ∈ B`), the induced map of relative cochain
complexes `C^*(Y,B;R) ⟶ C^*(X,A;R)` of `Work.Cohomology.relComplexMap` is an isomorphism
in homology in every degree, with inverse induced by `e.symm`.

This is the degreewise restatement of `Work.Thom.relCohHomeomorph` (relative cohomology is
invariant under a homeomorphism of pairs): an `Iso` of `R`-modules has an `IsIso` underlying
morphism, and the pair map of `e.symm` gives the two-sided inverse at the level of the
homology functor via `Work.Thom.relCohMap_comp'`, `relCohMap_congr'` and `relCohMap_id'`. -/
theorem isIso_relComplexMap_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B)
    (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap R A B
      (TopCat.ofHom (e : C(X, Y))) (fun x hx => (he x).mp hx)) n) := by
  -- `e` carries `A` into `B`, and `e.symm` carries `B` back into `A`.
  have hf : ∀ x ∈ A, (e : C(X, Y)) x ∈ B := fun x hx => (he x).mp hx
  have hg : ∀ y ∈ B, (e.symm : C(Y, X)) y ∈ A :=
    fun y hy => (he (e.symm y)).mpr (by simpa using hy)
  -- The two composites of `e` with `e.symm` are the identities.
  have hcompY : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
    ext y; exact e.apply_symm_apply y
  have hcompX : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext x; exact e.symm_apply_apply x
  -- The inverse is the pullback of relative cohomology along `e.symm`.
  refine IsIso.mk ⟨Work.Thom.relCohMap (e.symm : C(Y, X)) B A hg R n, ?_, ?_⟩
  · -- `relCohMap e ≫ relCohMap e.symm = 𝟙`, on `H^n(Y,B;R)`.
    exact (Work.Thom.relCohMap_comp' (X := Y) (Y := X) (Z := Y) (A := B) (B := A) (C := B)
      (f := (e.symm : C(Y, X))) (g := (e : C(X, Y))) (hf := hg) (hg := hf)
      (R := R) (n := n) (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy))).trans
      ((Work.Thom.relCohMap_congr' (f := (e : C(X, Y)).comp (e.symm : C(Y, X)))
          (f' := ContinuousMap.id Y) B B hcompY
          (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy)) (fun _ hy => hy) R n).trans
        (Work.Thom.relCohMap_id' B R n))
  · -- `relCohMap e.symm ≫ relCohMap e = 𝟙`, on `H^n(X,A;R)`.
    exact (Work.Thom.relCohMap_comp' (X := X) (Y := Y) (Z := X) (A := A) (B := B) (C := A)
      (f := (e : C(X, Y))) (g := (e.symm : C(Y, X))) (hf := hf) (hg := hg)
      (R := R) (n := n) (fun x hx => hg ((e : C(X, Y)) x) (hf x hx))).trans
      ((Work.Thom.relCohMap_congr' (f := (e.symm : C(Y, X)).comp (e : C(X, Y)))
          (f' := ContinuousMap.id X) A A hcompX
          (fun x hx => hg ((e : C(X, Y)) x) (hf x hx)) (fun _ hx => hx) R n).trans
        (Work.Thom.relCohMap_id' A R n))

end Work.Thom.CapGlue
