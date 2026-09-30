import Mathlib
import Submission.Work.Thom.Cohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-!
# Homotopy equivalences induce isomorphisms on cohomology

If `e : C(X,Y)` is the forward map of a homotopy equivalence (with homotopy inverse `g` and the two
homotopies `g ∘ e ≃ id` and `e ∘ g ≃ id`), then `CohMap e R n : H^n(Y;R) → H^n(X;R)` is bijective:
`CohMap_homotopic` turns the homotopies into the identities `CohMap e ≫ CohMap g = id` and
`CohMap g ≫ CohMap e = id`.

This is the tool that lets a *homotopy equivalence of pairs of spaces* transport the hypotheses of
`Work.Thom.suspensionStep_bijective`.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- The pullback of a composite is the composite of the pullbacks, in the `LinearMap` form needed
below. -/
theorem CohMap_linear_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (R : Type) [CommRing R] (n : ℕ) :
    ((CohMap f R n).hom).comp ((CohMap g R n).hom) = (CohMap (g.comp f) R n).hom := by
  have h := congrArg (fun φ : Coh R n Z ⟶ Coh R n X => φ.hom) (CohMap_comp f g R n)
  simpa [ModuleCat.hom_comp] using h.symm

/-- **A homotopy equivalence induces a bijection on cohomology.** -/
theorem bijective_CohMap_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (R : Type) [CommRing R] (n : ℕ) :
    Function.Bijective (CohMap e.toFun R n).hom := by
  have key : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
      (f : C(A, B)) (g : C(B, A)), ContinuousMap.Homotopic (g.comp f) (ContinuousMap.id A) →
      ((CohMap f R n).hom).comp ((CohMap g R n).hom) = LinearMap.id := by
    intro A B _ _ f g hh
    rw [CohMap_linear_comp f g R n]
    have hone : CohMap (g.comp f) R n = 𝟙 (Coh R n A) := by
      rw [CohMap_homotopic hh R n, CohMap_id]
    rw [hone, ModuleCat.hom_id]
  have h1 := key e.toFun e.invFun e.left_inv
  have h2 := key e.invFun e.toFun e.right_inv
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have hx := LinearMap.congr_fun h2 x
    have hy := LinearMap.congr_fun h2 y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [hxy] at hx
    exact hx.symm.trans hy
  · exact ⟨(CohMap e.invFun R n).hom y, LinearMap.congr_fun h1 y⟩

end

end Work.Thom
