import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.BFun

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint Opposite

/-!
# CWIND/BFun: `underlying` is bijective on maps out of `ℤ[X^{Δⁿ}]` for `X` a subsingleton

For a topological space `X` with at most one point, the mapping space `Y = X^{Δⁿ} = C(Δⁿ, X)` is a
subsingleton, and the light condensed set `A = topCatToLightCondSet.obj Y` is *constant*: it is the
terminal sheaf when `X` is nonempty and the initial sheaf when `X = ∅`.  Consequently the counit
`LocallyConstant(·, A(∗)) ⟶ A` of the adjunction `LocallyConstant ⊣ underlying` is an isomorphism,
and the general lemma `bijective_map_of_isIso_counit` then identifies `underlying.map` on
`Hom(A, F)` with the adjunction bijection `Hom(A, F) ≅ Hom(A(∗), F(∗))`.
-/

/-- **General lemma.** If the counit of an adjunction `L ⊣ R` at an object `A` is an isomorphism,
then `R` induces a bijection `Hom(A, F) ≃ Hom(R A, R F)`. -/
theorem bijective_map_of_isIso_counit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : D) (h : IsIso (adj.counit.app A))
    (F : D) : Function.Bijective (fun t : A ⟶ F => R.map t) := by
  haveI := h
  have hkey : ∀ t : A ⟶ F, adj.homEquiv (R.obj A) F (adj.counit.app A ≫ t) = R.map t := by
    intro t
    show adj.unit.app (R.obj A) ≫ R.map (adj.counit.app A ≫ t) = R.map t
    rw [Functor.map_comp, ← Category.assoc, adj.right_triangle_components]
    simp
  refine ⟨fun t₁ t₂ ht => ?_, fun s => ?_⟩
  · have ht' : R.map t₁ = R.map t₂ := ht
    have h1 : adj.homEquiv (R.obj A) F (adj.counit.app A ≫ t₁)
        = adj.homEquiv (R.obj A) F (adj.counit.app A ≫ t₂) := by
      rw [hkey t₁, hkey t₂, ht']
    have h2 : adj.counit.app A ≫ t₁ = adj.counit.app A ≫ t₂ :=
      (adj.homEquiv (R.obj A) F).injective h1
    have h3 := congrArg (fun k => inv (adj.counit.app A) ≫ k) h2
    simpa [Category.assoc] using h3
  · obtain ⟨u, hu⟩ := (adj.homEquiv (R.obj A) F).surjective s
    refine ⟨inv (adj.counit.app A) ≫ u, ?_⟩
    show R.map (inv (adj.counit.app A) ≫ u) = s
    rw [← hkey (inv (adj.counit.app A) ≫ u), ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp]
    exact hu

/-! ## The object `A(S) = C(S, Y)` -/

/-- The value of `topCatToLightCondSet.obj Y` at a light profinite set `S` is the set of continuous
maps `S → Y`. -/
lemma obj_obj_eq (Y : TopCat.{0}) (S : LightProfinite.{0}) :
    ((topCatToLightCondSet.obj Y).obj.obj (op S)) = C(↥S.toTop, ↥Y) := by
  dsimp only [topCatToLightCondSet]
  rw [topCatToSheafCompHausLike_obj, TopCat.toSheafCompHausLike_obj_obj]
  rfl

/-- A locally constant function into a subsingleton is a subsingleton. -/
lemma subsingleton_locallyConstant {α β : Type*} [TopologicalSpace α] [Subsingleton β] :
    Subsingleton (LocallyConstant α β) :=
  ⟨fun f g => LocallyConstant.ext fun _ => Subsingleton.elim _ _⟩

/-- The (bundled) empty function out of an empty type is locally constant. -/
lemma locallyConstant_isEmpty {α β : Type*} [TopologicalSpace α] [IsEmpty α] :
    Nonempty (LocallyConstant α β) :=
  ⟨⟨fun x => isEmptyElim x, fun s => by
      rw [show (fun x : α => isEmptyElim x) ⁻¹' s = ∅ from by
        ext x
        exact ⟨fun _ => isEmptyElim x, fun h => h.elim⟩]
      exact isOpen_empty⟩⟩

/-! ## The component of the counit -/

/-- The component at `op S` of the counit of the adjunction
`LightCondSet.LocallyConstant.functor ⊣ LightCondSet.underlying` is `counitAppApp`. -/
lemma counit_app_app_eq (Y : TopCat.{0}) (S : LightProfinite.{0}) :
    ((LightCondSet.LocallyConstant.adjunction.counit.app (topCatToLightCondSet.obj Y)).hom.app
        (op S))
      = CompHausLike.LocallyConstant.counitAppApp S (topCatToLightCondSet.obj Y).obj := by
  rw [LightCondSet.LocallyConstant.adjunction, CompHausLike.LocallyConstant.adjunction_counit]
  show (CompHausLike.LocallyConstant.counitApp (topCatToLightCondSet.obj Y).obj).app (op S) = _
  rw [CompHausLike.LocallyConstant.counitApp_app]

/-- For a subsingleton space `Y`, the component of the counit at `S` is bijective: both the set of
locally constant maps `S ⟶ Y ≅ ·` and the set of continuous maps `S ⟶ Y` are subsingletons. -/
lemma bijective_counitAppApp (Y : TopCat.{0}) [Subsingleton ↥Y] (S : LightProfinite.{0}) :
    Function.Bijective (CompHausLike.LocallyConstant.counitAppApp S
      (topCatToLightCondSet.obj Y).obj) := by
  haveI hcod : Subsingleton (((topCatToLightCondSet.obj Y).obj.obj (op S))) := by
    rw [obj_obj_eq Y S]
    infer_instance
  haveI hdom : Subsingleton (LocallyConstant (↥S.toTop)
      ((topCatToLightCondSet.obj Y).obj.obj (op (↧PUnit)))) := by
    rw [obj_obj_eq Y ↧PUnit]
    exact subsingleton_locallyConstant
  refine ⟨fun f g _ => Subsingleton.elim f g, fun a => ?_⟩
  by_cases hY : Nonempty ↥Y
  · have hu : ((topCatToLightCondSet.obj Y).obj.obj (op (↧PUnit))) := by
      rw [obj_obj_eq Y ↧PUnit]
      exact ContinuousMap.const _ hY.some
    exact ⟨LocallyConstant.const (↥S.toTop) hu, Subsingleton.elim _ _⟩
  · rw [not_nonempty_iff] at hY
    by_cases hS : Nonempty ↥S
    · have hem : IsEmpty (((topCatToLightCondSet.obj Y).obj.obj (op S))) := by
        rw [obj_obj_eq Y S]
        exact ⟨fun f => hY.false (f (show ↥S.toTop from hS.some))⟩
      exact (hem.false a).elim
    · haveI : IsEmpty ↥S.toTop := not_nonempty_iff.mp hS
      refine ⟨(locallyConstant_isEmpty (α := ↥S.toTop)
        (β := ((topCatToLightCondSet.obj Y).obj.obj (op (↧PUnit))))).some,
        Subsingleton.elim _ _⟩

/-- The counit of `LightCondSet.LocallyConstant.functor ⊣ LightCondSet.underlying` at
`A = topCatToLightCondSet.obj Y`, for `Y` a subsingleton space, is an isomorphism. -/
theorem isIso_counit (Y : TopCat.{0}) [Subsingleton ↥Y] :
    IsIso (LightCondSet.LocallyConstant.adjunction.counit.app (topCatToLightCondSet.obj Y)) := by
  rw [← ObjectProperty.isIso_hom_iff]
  rw [NatTrans.isIso_iff_isIso_app]
  intro S
  rw [counit_app_app_eq Y (unop S)]
  exact (isIso_iff_bijective _).mpr (bijective_counitAppApp Y (unop S))

/-! ## The main theorem -/

theorem underlyingBijective (X : TopCat.{0}) [Subsingleton ↥X] (n : ℕ) (F : LightCondSet.{0}) :
    Function.Bijective (fun t : topCatToLightCondSet.obj (Work.CWIND.singSpace X n) ⟶ F =>
      (LightCondSet.underlying).map t) := by
  haveI : Subsingleton ↥(Work.CWIND.singSpace X n) := inferInstance
  exact bijective_map_of_isIso_counit LightCondSet.LocallyConstant.adjunction
    (topCatToLightCondSet.obj (Work.CWIND.singSpace X n)) (isIso_counit _) F

end Work.CWIND.BFun
