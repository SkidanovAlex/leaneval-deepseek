import Submission.Work.CWIND.GClass.MVTransport
import Submission.Work.CONDMV.FreeMono.mono_free_map

/-!
# The functors `A` and `C` preserve monomorphisms of spaces

For a monomorphism `f : Y ⟶ Z` of spaces, the degree `n` part of the map `A(Y) ⟶ A(Z)` induced
by `A` is `ℤ[C(Δⁿ, Y)] ⟶ ℤ[C(Δⁿ, Z)]`, induced by postcomposition with `f`.  That map is
injective as soon as `f` is, and the free light condensed abelian group functor sends
monomorphisms of light condensed sets to monomorphisms
(`Work.CONDMV.FreeMono.free_preservesMonomorphisms`); finally extension by zero preserves
monomorphisms (`Work.CWIND.GClass.mono_extendMap_downNat`).  The same argument applies to the
singular chain functor `C = singC ⋙ GG`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

/-- Postcomposition with a monomorphism of topological spaces is a monomorphism of the
compact-open mapping spaces. -/
lemma mono_singSpacePostcomp {Y Z : TopCat.{0}} (f : Y ⟶ Z) [Mono f] (n : ℕ) :
    Mono (singSpacePostcomp f n) := by
  have hf : Function.Injective f.hom := (TopCat.mono_iff_injective f).1 inferInstance
  rw [TopCat.mono_iff_injective]
  intro g₁ g₂ h
  have h' : ∀ s : Δ n, f.hom (g₁ s) = f.hom (g₂ s) := by
    intro s
    have h₂ := congrArg (fun (q : C(Δ n, Z)) => q s) h
    simpa using h₂
  ext s
  exact hf (h' s)

/-- The map of light condensed sets induced by a monomorphism of spaces is a monomorphism. -/
lemma mono_topCatToLightCondSet_map {Y Z : TopCat.{0}} (g : Y ⟶ Z) [Mono g] :
    Mono (topCatToLightCondSet.map g) := by
  haveI : Functor.IsRightAdjoint topCatToLightCondSet.{0} :=
    LightCondSet.topCatAdjunction.{0}.isRightAdjoint
  exact inferInstance

/-- The free light condensed abelian group functor on a space preserves monomorphisms. -/
lemma mono_freeLightCondAbOfTop_map {Y Z : TopCat.{0}} (g : Y ⟶ Z) [Mono g] :
    Mono (freeLightCondAbOfTopFunctor.map g) := by
  haveI := Work.CONDMV.FreeMono.free_preservesMonomorphisms
  haveI : Mono (topCatToLightCondSet.map g) := mono_topCatToLightCondSet_map g
  show Mono ((free ℤ).map (topCatToLightCondSet.map g))
  exact inferInstance

/-- The alternating face map complex of `n ↦ ℤ[X^{Δⁿ}]` preserves monomorphisms. -/
lemma mono_AchainFunctor_map {Y Z : TopCat.{0}} (f : Y ⟶ Z) [Mono f] :
    Mono (AchainFunctor.map f) := by
  have hcomp : ∀ n : ℕ, (AchainFunctor.map f).f n =
      freeLightCondAbOfTopFunctor.map (singSpacePostcomp f n) := by
    intro n
    rw [show (AchainFunctor.map f).f n =
      (YFunctor.map f).app (Opposite.op (SimplexCategory.mk n)) from rfl]
    rfl
  refine HomologicalComplex.mono_of_mono_f _ (fun n => ?_)
  rw [hcomp n]
  haveI : Mono (singSpacePostcomp f n) := mono_singSpacePostcomp f n
  exact mono_freeLightCondAbOfTop_map _

/-- The complex `A` preserves monomorphisms of spaces. -/
lemma mono_AFunctor_map {Y Z : TopCat.{0}} (f : Y ⟶ Z) [Mono f] : Mono (AFunctor.map f) := by
  have h₁ : Mono (AchainFunctor.map f) := mono_AchainFunctor_map f
  have h₂ : AFunctor.map f = HomologicalComplex.extendMap (AchainFunctor.map f)
      ComplexShape.embeddingDownNat := rfl
  rw [h₂]
  exact mono_extendMap_downNat _ h₁

/-- The map `A(A) ⟶ A(B)` induced by the inclusion of a subset is a monomorphism. -/
lemma mono_AFunctor_map_incl {X : TopCat.{0}} {A B : Set X} (h : A ⊆ B) :
    Mono (AFunctor.map (incl h)) := by
  haveI : Mono (incl h) := (TopCat.mono_iff_injective _).2 (by
    simpa [Submission.Blueprint.incl] using Set.inclusion_injective h)
  exact mono_AFunctor_map _

/-- The map `C(A) ⟶ C(B)` induced by an arbitrary monomorphism of spaces is a monomorphism. -/
lemma mono_Cfun_map {Y Z : TopCat.{0}} (f : Y ⟶ Z) [Mono f] : Mono (Cfun.map f) := by
  haveI : Mono (singC.map f) := inferInstance
  have h₂ : Cfun.map f = GG.map (singC.map f) := rfl
  rw [h₂]
  exact GG_preserves_mono _ inferInstance

/-- The map `C(A) ⟶ C(B)` induced by the inclusion of a subset is a monomorphism. -/
lemma mono_Cfun_map_incl {X : TopCat.{0}} {A B : Set X} (h : A ⊆ B) :
    Mono (Cfun.map (incl h)) := by
  haveI : Mono (incl h) := (TopCat.mono_iff_injective _).2 (by
    simpa [Submission.Blueprint.incl] using Set.inclusion_injective h)
  exact mono_Cfun_map _

end Work.CWIND.GClass
