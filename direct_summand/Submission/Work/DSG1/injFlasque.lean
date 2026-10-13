import Mathlib
import Submission.Work.DSG1.Basic

namespace Work.DSG1

/-
**Injective sheaves of O_X-modules are flasque.**  Crux of area G1: Mathlib has no
extension-by-zero `j_!` for `SheafOfModules`, so the classical proof is unavailable.
The route used below avoids `j_!`:

Let `R := X.ringCatSheaf`.
1. `PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)` gives
   `PresheafOfModules.sheafification (𝟙 R.obj) ⊣ SheafOfModules.forget R ⋙
   PresheafOfModules.restrictScalars (𝟙 R.obj)`; the left adjoint preserves finite limits
   (`PresheafOfModules.Sheafification` instance `PreservesFiniteLimits (sheafification α)`),
   hence monomorphisms, and `restrictScalars (𝟙 R.obj)` is the identity.  Hence
   (`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`) `M.val :
   PresheafOfModules R.obj` is injective whenever `M : SheafOfModules R` is.
2. For `U : X.Opens` put `A U := PresheafOfModules.freeObj (yoneda.obj U)`
   (note `R.obj : (X.Opens)ᵒᵖ ⥤ RingCat`, so `yoneda.obj U : (X.Opens)ᵒᵖ ⥤ Type`).
   `freeHomEquiv` and `yonedaEquiv` give `(A U ⟶ G) ≃ G.presheaf.obj (op U)`, naturally in `U`.
3. For `V ≤ U` the morphism `A V ⟶ A U` induced by `yoneda.map (homOfLE h)` is a monomorphism
   (components are `(ModuleCat.free (R.obj X)).map` of an injective map of subsingletons, so
   `Finsupp.mapDomain_injective`); under the bijections of 2. it is the restriction map.
4. Injectivity of `M.val` applied to that mono makes `Hom(A U, M.val) → Hom(A V, M.val)`
   surjective (`Injective.factorThru`), which by 3. is `M(U) → M(V)`; conclude with
   `AddCommGrpCat.epi_iff_surjective`.
-/

open CategoryTheory AlgebraicGeometry Limits TopCat Opposite

universe u

set_option linter.style.haveILetI false

/-- (Implementation) The free `S`-module functor sends a pointwise injective map of presheaves of
types to a pointwise injective map of presheaves of modules: pointwise it is `Finsupp.mapDomain`. -/
private lemma free_obj_map_injective {C : Type u} [Category.{u} C] {S : Type u} [Ring S]
    {F G : Cᵒᵖ ⥤ Type u} (φ : F ⟶ G) (X : Cᵒᵖ)
    (hf : Function.Injective (φ.app X)) :
    Function.Injective ⇑(ConcreteCategory.hom ((ModuleCat.free S).map (φ.app X))) := by
  rw [show ⇑(ConcreteCategory.hom ((ModuleCat.free S).map (φ.app X))) =
      Finsupp.mapDomain (φ.app X) from rfl]
  exact Finsupp.mapDomain_injective hf

/-- **Injective sheaves of `𝒪_X`-modules are flasque.**

For `V ≤ U` open subsets of `X` and an injective `𝒪_X`-module `M`, the restriction
`Γ(U, M) ⟶ Γ(V, M)` is surjective.  Represent `Γ(U, ·)` and `Γ(V, ·)` by the free presheaves of
modules on the representable presheaves of `U` and `V`; since `V ≤ U` there is a monomorphism
`A V ⟶ A U`, and injectivity of the underlying presheaf of `M` makes the induced map on `Hom`s
surjective.  By naturality that map is the restriction, so every section over `V` extends. -/
theorem injFlasque {X : Scheme.{u}} (M : X.Modules) [Injective M] :
    TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj := by
  -- The forgetful functor `X.Modules ⥤ PresheafOfModules 𝓞_X` is a right adjoint
  -- (sheafification is its left adjoint), hence preserves injective objects.
  haveI hval : Injective M.1 :=
    Adjunction.map_injective (PresheafOfModules.sheafificationAdjunction
      (R₀ := X.ringCatSheaf.obj) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)) M
      ‹Injective M›
  refine ⟨fun {U V} i => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  -- Represent `Γ(U, ·)` and `Γ(V, ·)` by the free presheaves of modules on the representable
  -- presheaves of `U` and `V`.
  let A := PresheafOfModules.freeObj (R := X.ringCatSheaf.obj) (yoneda.obj V.unop)
  let B := PresheafOfModules.freeObj (R := X.ringCatSheaf.obj) (yoneda.obj U.unop)
  -- The canonical morphism of representables `yoneda.obj V.unop ⟶ yoneda.obj U.unop`
  -- (given by `i.unop : V.unop ⟶ U.unop`) induces `ψ : A ⟶ B`.
  let ψ : A ⟶ B := (PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i.unop)
  have hψ : Mono ψ := by
    apply PresheafOfModules.mono_of_injective
    intro W
    change Function.Injective ⇑(ConcreteCategory.hom
      (((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i.unop)).app W))
    rw [PresheafOfModules.free_map_app]
    haveI : Subsingleton ((yoneda.obj V.unop).obj W) :=
      inferInstanceAs (Subsingleton (W.unop ⟶ V.unop))
    exact free_obj_map_injective _ _ (fun a b _ => Subsingleton.elim a b)
  haveI : Mono ψ := hψ
  -- The identifications `Hom(A, M) ≃ Γ(V, M)` and `Hom(B, M) ≃ Γ(U, M)`.
  let Φ : ∀ (W : TopologicalSpace.Opens ↥X),
      (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj) (yoneda.obj W) ⟶ M.1) ≃
        (M.1.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).obj (Opposite.op W) :=
    fun W => (PresheafOfModules.freeHomEquiv (F := yoneda.obj W) (G := M.1)).trans yonedaEquiv
  -- Lift the section `s ∈ Γ(V, M)` along `ψ` using injectivity of `M`.
  let gs : A ⟶ M.1 := (Φ V.unop).symm s
  let w : B ⟶ M.1 := Injective.factorThru gs ψ
  have hw : ψ ≫ w = gs := Injective.comp_factorThru gs ψ
  refine ⟨(Φ U.unop) w, ?_⟩
  -- The map induced by `ψ` on `Hom`s is the restriction.
  have key : ConcreteCategory.hom (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map i)
        ((Φ U.unop) w) = (Φ V.unop) (ψ ≫ w) := by
    have e1 : (Φ U.unop) w = yonedaEquiv (PresheafOfModules.freeHomEquiv w) := rfl
    have e2 : (Φ V.unop) (ψ ≫ w)
        = yonedaEquiv (PresheafOfModules.freeHomEquiv (ψ ≫ w)) := rfl
    have h1 : PresheafOfModules.freeHomEquiv (ψ ≫ w)
        = yoneda.map i.unop ≫ PresheafOfModules.freeHomEquiv w := by
      rw [← PresheafOfModules.freeAdjunction_homEquiv (yoneda.obj V.unop) M.1,
        ← PresheafOfModules.freeAdjunction_homEquiv (yoneda.obj U.unop) M.1]
      exact Adjunction.homEquiv_naturality_left
        (adj := PresheafOfModules.freeAdjunction X.ringCatSheaf.obj)
        (f := yoneda.map i.unop) (g := w)
    rw [e1, e2, h1]
    exact yonedaEquiv_naturality (PresheafOfModules.freeHomEquiv w) i.unop
  rw [key, hw]
  exact Equiv.apply_symm_apply (Φ V.unop) s

end Work.DSG1
