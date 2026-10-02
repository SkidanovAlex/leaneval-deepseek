import Submission.Work.ThomBordism.Grassmann.Model

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# A homotopy equivalence of pairs induces an isomorphism on relative cohomology

If `f : (X,A) → (Y,B)` and `g : (Y,B) → (X,A)` are maps of pairs which are mutually inverse up to
homotopies of pairs (i.e. there are homotopies `g ∘ f ≃ id_X` preserving `A` and `f ∘ g ≃ id_Y`
preserving `B`), then the pullback `f^* : H^n(Y,B;ℤ) → H^n(X,A;ℤ)` is a bijection in every degree.

The proof composes the functoriality of `relCohMap` (`relCohMap_compA`, `relCohMap_idA`) with the
homotopy invariance of relative cohomology for maps of pairs (`Work.Thom.relCohMap_homotopic`),
exactly as `Work.Thom.bijective_relCohMap_of_homeomorphA` does for homeomorphisms of pairs.
-/

namespace Work.ThomBordism.Grassmann

open CategoryTheory

noncomputable section

/-- **A homotopy equivalence of pairs induces a bijection on relative cohomology.**

`P` is a homotopy of pairs from `g ∘ f` to the identity of `X` (preserving `A`), and `Q` one from
`f ∘ g` to the identity of `Y` (preserving `B`).  Then `Work.Thom.relCohMap f A B hf` is
bijective. -/
theorem relCohMap_pairHomotopy {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (g : C(Y, X))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ A)
    (P : ContinuousMap.Homotopy (g.comp f) (ContinuousMap.id X))
    (hP : ∀ t x, x ∈ A → P (t, x) ∈ A)
    (Q : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id Y))
    (hQ : ∀ t y, y ∈ B → Q (t, y) ∈ B) (n : ℕ) :
    Function.Bijective (Work.Thom.relCohMap f A B hf ℤ n).hom := by
  have hgf : ∀ x ∈ A, (g.comp f) x ∈ A := fun x hx => hg (f x) (hf x hx)
  have hid : ∀ x ∈ A, (ContinuousMap.id X) x ∈ A := fun _ hx => hx
  have hfg : ∀ y ∈ B, (f.comp g) y ∈ B := fun y hy => hf (g y) (hg y hy)
  have hidY : ∀ y ∈ B, (ContinuousMap.id Y) y ∈ B := fun _ hy => hy
  -- `relCohMap f` is a right inverse of `relCohMap g`
  have hcomp1 : CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap g B A hg ℤ n)
      (Work.Thom.relCohMap f A B hf ℤ n) = 𝟙 (Work.Thom.RelCoh ℤ n X A) :=
    (Work.Thom.relCohMap_compA A B A f g hf hg
        (fun x hx => hg (f x) (hf x hx)) ℤ n).trans
      ((Work.Thom.relCohMap_homotopic A A hgf hid P hP ℤ n).trans
        (Work.Thom.relCohMap_idA A ℤ n))
  -- `relCohMap g` is a right inverse of `relCohMap f`
  have hcomp2 : CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap f A B hf ℤ n)
      (Work.Thom.relCohMap g B A hg ℤ n) = 𝟙 (Work.Thom.RelCoh ℤ n Y B) :=
    (Work.Thom.relCohMap_compA B A B g f hg hf
        (fun y hy => hf (g y) (hg y hy)) ℤ n).trans
      ((Work.Thom.relCohMap_homotopic B B hfg hidY Q hQ ℤ n).trans
        (Work.Thom.relCohMap_idA B ℤ n))
  -- both composites of the underlying linear maps are the identity
  have hlin1 : (Work.Thom.relCohMap f A B hf ℤ n).hom.comp
      (Work.Thom.relCohMap g B A hg ℤ n).hom = LinearMap.id := by
    have := congrArg (fun φ : Work.Thom.RelCoh ℤ n X A ⟶ Work.Thom.RelCoh ℤ n X A => φ.hom)
      hcomp1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  have hlin2 : (Work.Thom.relCohMap g B A hg ℤ n).hom.comp
      (Work.Thom.relCohMap f A B hf ℤ n).hom = LinearMap.id := by
    have := congrArg (fun φ : Work.Thom.RelCoh ℤ n Y B ⟶ Work.Thom.RelCoh ℤ n Y B => φ.hom)
      hcomp2
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  constructor
  · intro a b hab
    have ha := LinearMap.congr_fun hlin2 a
    have hb := LinearMap.congr_fun hlin2 b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [hab] at ha
    exact ha.symm.trans hb
  · intro y
    refine ⟨(Work.Thom.relCohMap g B A hg ℤ n).hom y, ?_⟩
    have hy := LinearMap.congr_fun hlin1 y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hy
    exact hy

end

end Work.ThomBordism.Grassmann
