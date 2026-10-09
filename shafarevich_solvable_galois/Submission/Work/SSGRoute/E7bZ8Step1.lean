import Mathlib
import Submission.Work.SSGRoute.E7bDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Z8, step 1: the base level of the cone, and its library companion

Two independent results.

* `Work.SSGRoute.resMap_id` — **library companion**: `Rep.resMap` of an identity morphism is the
  identity.  In `Mathlib/RepresentationTheory/Rep/Res.lean` both `Rep.resMap f` and
  `(Rep.resFunctor f).map` are *the same* `abbrev`-unfolded term, so `Functor.map_id` cannot fire
  by keyed matching on a goal written with `Rep.resMap`; the proof goes through
  `change` to the functorial form first.  This is useful well past E7b.

* `Work.SSGRoute.vanishesAbove_base` — **Z8, step 1**: with `L₀ = K`, `w₀ = w`,
  `f₀ = MonoidHom.id` and `ι₀ = 𝟙`, the composite level data of `SSGRoute.PTExt.VanishesAbove`
  reduce to `(g, ι₁)`, so the target's hypothesis *is*
  `VanishesAbove k K y K w (MonoidHom.id _) 𝟙`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **`Rep.resMap` of an identity is an identity.**  (`Rep.resMap f` and `(Rep.resFunctor f).map`
are the same term up to `abbrev`-unfolding, so this is `Functor.map_id` after a `change`.) -/
@[simp] theorem resMap_id {k : Type*} [Semiring k] {G : Type*} {H : Type*} [Monoid G] [Monoid H]
    (f : H →* G) {X : Rep k G} :
    Rep.resMap f (𝟙 X) = 𝟙 (Rep.res f X) := by
  change (Rep.resFunctor f).map (𝟙 X) = 𝟙 ((Rep.resFunctor f).obj X)
  rw [CategoryTheory.Functor.map_id]

/-- **Z8, step 1 (base level).**  With `L₀ = K`, `w₀ = w`, `f₀ = MonoidHom.id` and `ι₀ = 𝟙`, the
composite level data `(MonoidHom.id.comp g, Rep.resMap g 𝟙 ≫ ι₁)` reduce to `(g, ι₁)`, so the
target's hypothesis is `VanishesAbove k K y K w (MonoidHom.id _) 𝟙`. -/
theorem vanishesAbove_base (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
    (hy : ∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
        [FiniteDimensional k L] [IsGalois k L]
        (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
        (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
        (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
        (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
        (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
          ι.hom (Additive.ofMul u) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
        (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
        levelPair f ι y h = 0) :
    VanishesAbove k K y K w (MonoidHom.id _) (𝟙 _) := by
  intro L _ _ _ _ _ _ _ w' hw' g _hg ι₁ _hι₁ h
  have hA : (MonoidHom.id (MulAction.stabilizer (K ≃ₐ[k] K) w)).comp g = g :=
    MonoidHom.id_comp g
  have hB : Rep.resMap g (𝟙 (Rep.res (MonoidHom.id (MulAction.stabilizer (K ≃ₐ[k] K) w))
        (localUnitsK (k := k) w))) ≫ ι₁ = ι₁ := by
    rw [resMap_id]
    exact Category.id_comp ι₁
  try rw [hA]
  rw [hB]
  exact hy L w' hw' g _hg ι₁ _hι₁ h

end Work.SSGRoute
