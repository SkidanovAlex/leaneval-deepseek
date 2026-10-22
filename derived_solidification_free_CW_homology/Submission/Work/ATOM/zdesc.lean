import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

/-- Naturality of `homFreeEquiv` in the light profinite set: the free-forget adjunction followed by
the Yoneda equivalence sends `ℤ[f]` to the restriction map of the presheaf underlying `A`. -/
lemma homFreeEquiv_naturality {S T : LightProfinite.{0}} (f : S ⟶ T) {A : LightCondAb}
    (g : Work.ATOM.zfree T ⟶ A) :
    Work.ATOM.homFreeEquiv S A (Work.ATOM.zmap f ≫ g)
      = (A.obj.map f.op) (Work.ATOM.homFreeEquiv T A g) := by
  have h1 := Adjunction.homEquiv_naturality_left (freeForgetAdjunction ℤ)
    (X' := S.toCondensed) (X := T.toCondensed) (Y := A)
    (lightProfiniteToLightCondSet.map f) g
  have h2 := GrothendieckTopology.yonedaEquiv_naturality (J := coherentTopology LightProfinite)
    ((freeForgetAdjunction ℤ).homEquiv T.toCondensed A g) f
  have A1 : Work.ATOM.homFreeEquiv S A (Work.ATOM.zmap f ≫ g)
      = (coherentTopology LightProfinite).yonedaEquiv
          ((freeForgetAdjunction ℤ).homEquiv S.toCondensed A (Work.ATOM.zmap f ≫ g)) := rfl
  have A2 : (coherentTopology LightProfinite).yonedaEquiv
        ((freeForgetAdjunction ℤ).homEquiv S.toCondensed A (Work.ATOM.zmap f ≫ g))
      = (coherentTopology LightProfinite).yonedaEquiv
        (lightProfiniteToLightCondSet.map f ≫
          (freeForgetAdjunction ℤ).homEquiv T.toCondensed A g) :=
    congrArg _ h1
  exact A1.trans (A2.trans h2.symm)

/-- Descent for morphisms out of free light condensed abelian groups along a surjection of light
profinite sets: a morphism `φ : ℤ[T'] ⟶ M` whose two pullbacks to the kernel pair agree descends
uniquely to `ℤ[T]`.  (Toolkit of `NOTES_LEAD_solid_gaps1.md` §3.4; used to build `g : P ⟶ ℤ[S]`,
which is *not* a combination of `zmap`s.) -/
theorem zdesc {T' T : LightProfinite.{0}} (π : T' ⟶ T) (hπ : Function.Surjective π)
    {M : LightCondAb} (φ : Work.ATOM.zfree T' ⟶ M)
    (hφ : Work.ATOM.zmap (pullback.fst π π) ≫ φ = Work.ATOM.zmap (pullback.snd π π) ≫ φ) :
    ∃! ψ : Work.ATOM.zfree T ⟶ M, Work.ATOM.zmap π ≫ ψ = φ := by
  have hEff : EffectiveEpi π := (LightProfinite.effectiveEpi_iff_surjective π).mpr hπ
  -- The underlying presheaf of types of `M`, which is a sheaf for the coherent topology.
  let P : LightProfinite.{0}ᵒᵖ ⥤ Type := ((LightCondensed.forget ℤ).obj M).obj
  have hEC : regularTopology.EqualizerCondition P :=
    LightCondensed.equalizerCondition ((LightCondensed.forget ℤ).obj M)
  -- The equalizer condition, unwrapped into a statement about elements.
  have hP : ∀ y : P.obj (op T'),
      (ConcreteCategory.hom (P.map (pullback.fst π π).op)) y =
      (ConcreteCategory.hom (P.map (pullback.snd π π).op)) y →
      ∃! x : P.obj (op T), (ConcreteCategory.hom (P.map π.op)) x = y := by
    intro y hy
    exact (CategoryTheory.Limits.Types.type_equalizer_iff_unique (P.map π.op)
      (regularTopology.equalizerCondition_w P (pullback.cone π π))).mp
      (@hEC T' T π hEff (pullback.cone π π) (pullback.isLimit π π)) y hy
  let x : P.obj (op T') := Work.ATOM.homFreeEquiv T' M φ
  -- `x` satisfies the descent condition, by naturality of `homFreeEquiv` and `hφ`.
  have hxmem : (ConcreteCategory.hom (P.map (pullback.fst π π).op)) x =
      (ConcreteCategory.hom (P.map (pullback.snd π π).op)) x := by
    have h1 := homFreeEquiv_naturality (pullback.fst π π) φ
    have h2 := homFreeEquiv_naturality (pullback.snd π π) φ
    have h3 : Work.ATOM.homFreeEquiv (pullback π π) M (Work.ATOM.zmap (pullback.fst π π) ≫ φ)
        = Work.ATOM.homFreeEquiv (pullback π π) M (Work.ATOM.zmap (pullback.snd π π) ≫ φ) :=
      congrArg (Work.ATOM.homFreeEquiv (pullback π π) M) hφ
    have e1 : (ConcreteCategory.hom (P.map (pullback.fst π π).op)) x
        = (M.obj.map (pullback.fst π π).op) x :=
      LightCondensed.forget_obj_obj_map_hom_apply ℤ M (pullback.fst π π).op x
    have e2 : (ConcreteCategory.hom (P.map (pullback.snd π π).op)) x
        = (M.obj.map (pullback.snd π π).op) x :=
      LightCondensed.forget_obj_obj_map_hom_apply ℤ M (pullback.snd π π).op x
    exact e1.trans ((h1.symm.trans (h3.trans h2)).trans e2.symm)
  obtain ⟨y, hy, hyu⟩ := hP x hxmem
  have hyval : (M.obj.map π.op) y = Work.ATOM.homFreeEquiv T' M φ :=
    (LightCondensed.forget_obj_obj_map_hom_apply ℤ M π.op y).symm.trans hy
  refine ⟨(Work.ATOM.homFreeEquiv T M).symm y, ?_, ?_⟩
  · -- Existence: `ψ` maps to `φ` under `ℤ[π]`, by injectivity of `homFreeEquiv`.
    apply (Work.ATOM.homFreeEquiv T' M).injective
    refine (homFreeEquiv_naturality π ((Work.ATOM.homFreeEquiv T M).symm y)).trans ?_
    have h2 : (Work.ATOM.homFreeEquiv T M) ((Work.ATOM.homFreeEquiv T M).symm y) = y :=
      Equiv.apply_symm_apply (Work.ATOM.homFreeEquiv T M) y
    exact (congrArg (M.obj.map π.op) h2).trans hyval
  · -- Uniqueness: any `ψ'` with `ℤ[π] ψ' = φ` yields a section of `M` over `T` mapping to `x`.
    intro ψ' hψ'
    have hthis : Work.ATOM.homFreeEquiv T M ψ' = y := by
      apply hyu
      have e1 : (ConcreteCategory.hom (P.map π.op)) (Work.ATOM.homFreeEquiv T M ψ')
          = (M.obj.map π.op) (Work.ATOM.homFreeEquiv T M ψ') :=
        LightCondensed.forget_obj_obj_map_hom_apply ℤ M π.op (Work.ATOM.homFreeEquiv T M ψ')
      have e2 : (M.obj.map π.op) (Work.ATOM.homFreeEquiv T M ψ')
          = Work.ATOM.homFreeEquiv T' M (Work.ATOM.zmap π ≫ ψ') :=
        (homFreeEquiv_naturality π ψ').symm
      have e3 : Work.ATOM.homFreeEquiv T' M (Work.ATOM.zmap π ≫ ψ')
          = Work.ATOM.homFreeEquiv T' M φ :=
        congrArg (Work.ATOM.homFreeEquiv T' M) hψ'
      exact e1.trans (e2.trans e3)
    exact (Equiv.symm_apply_apply (Work.ATOM.homFreeEquiv T M) ψ').symm.trans
      (congrArg (Work.ATOM.homFreeEquiv T M).symm hthis)

end Work.ATOM
