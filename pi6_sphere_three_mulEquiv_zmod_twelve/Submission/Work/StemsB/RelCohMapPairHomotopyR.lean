import Mathlib
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.StemsB.AToolsR

/-!
# A homotopy equivalence of pairs induces an isomorphism on relative cohomology, over any ring

`Submission/Work/ThomBordism/Grassmann/relCohMap_pairHomotopy.lean` proves, over `ℤ`, that if
`f : (X,A) → (Y,B)` and `g : (Y,B) → (X,A)` are mutually inverse up to homotopies of pairs then the
pullback `f^* : H^n(Y,B;ℤ) → H^n(X,A;ℤ)` is bijective in every degree.  Its proof uses only
`Work.Thom.relCohMap_compA`, `Work.Thom.relCohMap_idA` and `Work.Thom.relCohMap_homotopic`, all of
which are stated for an arbitrary commutative ring, so the same proof gives the statement over any
`R`.  This file records that form; the `ℤ` original is untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

namespace Work.StemsB

open CategoryTheory

noncomputable section

variable (R : Type) [CommRing R]

/-- **A homotopy equivalence of pairs induces a bijection on relative cohomology**, over `R`.

`P` is a homotopy of pairs from `g ∘ f` to the identity of `X` (preserving `A`), and `Q` one from
`f ∘ g` to the identity of `Y` (preserving `B`).  Then `Work.Thom.relCohMap f A B hf` is
bijective. -/
theorem relCohMap_pairHomotopyR {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (g : C(Y, X))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ A)
    (P : ContinuousMap.Homotopy (g.comp f) (ContinuousMap.id X))
    (hP : ∀ t x, x ∈ A → P (t, x) ∈ A)
    (Q : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id Y))
    (hQ : ∀ t y, y ∈ B → Q (t, y) ∈ B) (n : ℕ) :
    Function.Bijective (Work.Thom.relCohMap f A B hf R n).hom := by
  have hgf : ∀ x ∈ A, (g.comp f) x ∈ A := fun x hx => hg (f x) (hf x hx)
  have hid : ∀ x ∈ A, (ContinuousMap.id X) x ∈ A := fun _ hx => hx
  have hfg : ∀ y ∈ B, (f.comp g) y ∈ B := fun y hy => hf (g y) (hg y hy)
  have hidY : ∀ y ∈ B, (ContinuousMap.id Y) y ∈ B := fun _ hy => hy
  -- `relCohMap f` is a right inverse of `relCohMap g`
  have hcomp1 : CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap g B A hg R n)
      (Work.Thom.relCohMap f A B hf R n) = 𝟙 (Work.Thom.RelCoh R n X A) :=
    (Work.Thom.relCohMap_compA A B A f g hf hg
        (fun x hx => hg (f x) (hf x hx)) R n).trans
      ((Work.Thom.relCohMap_homotopic A A hgf hid P hP R n).trans
        (Work.Thom.relCohMap_idA A R n))
  -- `relCohMap g` is a right inverse of `relCohMap f`
  have hcomp2 : CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap f A B hf R n)
      (Work.Thom.relCohMap g B A hg R n) = 𝟙 (Work.Thom.RelCoh R n Y B) :=
    (Work.Thom.relCohMap_compA B A B g f hg hf
        (fun y hy => hf (g y) (hg y hy)) R n).trans
      ((Work.Thom.relCohMap_homotopic B B hfg hidY Q hQ R n).trans
        (Work.Thom.relCohMap_idA B R n))
  -- both composites of the underlying linear maps are the identity
  have hlin1 : (Work.Thom.relCohMap f A B hf R n).hom.comp
      (Work.Thom.relCohMap g B A hg R n).hom = LinearMap.id := by
    have := congrArg (fun φ : Work.Thom.RelCoh R n X A ⟶ Work.Thom.RelCoh R n X A => φ.hom)
      hcomp1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  have hlin2 : (Work.Thom.relCohMap g B A hg R n).hom.comp
      (Work.Thom.relCohMap f A B hf R n).hom = LinearMap.id := by
    have := congrArg (fun φ : Work.Thom.RelCoh R n Y B ⟶ Work.Thom.RelCoh R n Y B => φ.hom)
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
    refine ⟨(Work.Thom.relCohMap g B A hg R n).hom y, ?_⟩
    have hy := LinearMap.congr_fun hlin1 y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hy
    exact hy

end

end Work.StemsB
