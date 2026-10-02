import Mathlib
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.relCohMap_comp
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Homotopy invariance of relative cohomology for a homotopy defined only on a neighbourhood

If `X ∖ A` is at most a single point `p`, `U` is an open neighbourhood of `p`, and `f g : X → Y`
are maps of pairs `(X,A) → (Y,B)` which are homotopic **through maps of pairs** by a homotopy
`H : I × U → Y` defined only on `U`, then `f` and `g` induce the same map
`H^n(Y,B;R) → H^n(X,A;R)`.

The point is that `A` and `U` are open and cover `X` (because `X ∖ A ⊆ {p} ⊆ U`), so by excision
(`Work.Cohomology.capRel_excision_isIso`, i.e. the inclusion of pairs `(U, U ∩ A) → (X, A)` is an
isomorphism on relative cohomology) the pullback along `f` is the composite of the pullback along
`f|_U` with the inverse of that excision isomorphism; and on `U` the maps `f|_U` and `g|_U` are
homotopic through maps of pairs, so `Work.Thom.relCohMap_homotopic` applies.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped unitInterval
open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- **Homotopy invariance of relative cohomology for maps of pairs, for a homotopy defined only on
a neighbourhood `U` of the single point where `A` may fail to be all of `X`.** -/
theorem relCohMap_eq_of_homotopicOn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (hA : IsOpen A) {p : X} (hp : ({p}ᶜ : Set X) ⊆ A)
    {U : Set X} (hU : IsOpen U) (hpU : p ∈ U) {B : Set Y} {f g : C(X, Y)}
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (H : C(unitInterval × ↥U, Y)) (hH0 : ∀ x : ↥U, H (0, x) = f x)
    (hH1 : ∀ x : ↥U, H (1, x) = g x)
    (hH : ∀ (t : unitInterval) (x : ↥U), (x : X) ∈ A → H (t, x) ∈ B) (n : ℕ) :
    Work.Thom.relCohMap f A B hf ℤ n = Work.Thom.relCohMap g A B hg ℤ n := by
  -- `A` and `U` are open and cover `X`, since `X ∖ A ⊆ {p} ⊆ U`.
  have hAU : U ∪ A = (Set.univ : Set X) := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ A
    · exact Or.inr hx
    · refine Or.inl ?_
      by_contra hxu
      have hxp : x = p := by
        by_contra hne
        exact hx (hp hne)
      exact hxu (hxp ▸ hpU)
  -- The various incarnations of the inclusion `U ↪ X`.
  let A' : Set ↥U := {y | (y : X) ∈ A}
  let ι : C(↥U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  -- Excision: the inclusion of pairs `(U, U ∩ A) → (X, A)` is an isomorphism on relative
  -- cohomology.
  have hEx : CategoryTheory.IsIso (Work.Thom.relCohMap ι A' A (fun y hy => hy) ℤ n) :=
    Work.Cohomology.capRel_excision_isIso (TopCat.of X) U A hU hA hAU n (fun y hy => hy)
  -- The restrictions of `f` and `g` to `U` still carry `U ∩ A` into `B`.
  have hf' : ∀ y ∈ A', (f.comp ι) y ∈ B := fun y hy => hf y hy
  have hg' : ∀ y ∈ A', (g.comp ι) y ∈ B := fun y hy => hg y hy
  -- Functoriality of the pullback in relative cohomology.
  have h1 : Work.Thom.relCohMap f A B hf ℤ n ≫ Work.Thom.relCohMap ι A' A (fun y hy => hy) ℤ n
      = Work.Thom.relCohMap (f.comp ι) A' B hf' ℤ n :=
    Work.Thom.relCohMap_comp A' A B ι f (fun y hy => hy) hf hf' ℤ n
  have h2 : Work.Thom.relCohMap g A B hg ℤ n ≫ Work.Thom.relCohMap ι A' A (fun y hy => hy) ℤ n
      = Work.Thom.relCohMap (g.comp ι) A' B hg' ℤ n :=
    Work.Thom.relCohMap_comp A' A B ι g (fun y hy => hy) hg hg' ℤ n
  -- Homotopy invariance on `U`.
  have hhom : Work.Thom.relCohMap (f.comp ι) A' B hf' ℤ n
      = Work.Thom.relCohMap (g.comp ι) A' B hg' ℤ n :=
    Work.Thom.relCohMap_homotopic A' B hf' hg'
      (ContinuousMap.Homotopy.mk H hH0 hH1) (fun t x hx => hH t x hx) ℤ n
  -- Cancel the excision isomorphism.
  have key : Work.Thom.relCohMap f A B hf ℤ n ≫ Work.Thom.relCohMap ι A' A (fun y hy => hy) ℤ n
      = Work.Thom.relCohMap g A B hg ℤ n
          ≫ Work.Thom.relCohMap ι A' A (fun y hy => hy) ℤ n := by
    rw [h1, h2]
    exact hhom
  exact (CategoryTheory.cancel_mono (Work.Thom.relCohMap ι A' A (fun y hy => hy) ℤ n)).1 key

end

end Work.ThomBordism
