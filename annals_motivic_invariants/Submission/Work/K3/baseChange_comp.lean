import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

/-! ## Transitivity of base change

`baseChange K L X` is the fibred product `X ×_{Spec K} Spec L`.  The transitivity of base change
is the standard "pullback of a pullback is a pullback" statement for the cospan
`Spec M ⟶ Spec L ⟶ Spec K`; it is proved below in its general categorical form
(`pullback_pullback_iso`) and then applied to the structure morphisms of the successive field
extensions, using `specMap_comp` to identify `specMap L M ≫ specMap K L` with `specMap K M`.-/

/-- **Composition of the structure morphisms of two successive field extensions**:
`Spec M ⟶ Spec L ⟶ Spec K` is `Spec M ⟶ Spec K`. -/
lemma specMap_comp (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    Work.K3.specMap L M ≫ Work.K3.specMap K L = Work.K3.specMap K M := by
  unfold Work.K3.specMap
  rw [← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]

/-- **Pullback of a pullback** (general categorical form): if `h = g ≫ f`, the pullback of
`g : W ⟶ U` along the projection `U ×_V T ⟶ U` of the pullback of `f : U ⟶ V` along
`w : T ⟶ V` is the pullback of `h` along `w`.  The isomorphism can be chosen over `W`, i.e. it
intertwines the two projections to `W`. -/
lemma pullback_pullback_iso {C : Type u} [Category.{v} C] [HasPullbacks C] {T U W V : C}
    (f : U ⟶ V) (g : W ⟶ U) (w : T ⟶ V) (h : W ⟶ V) (hg : g ≫ f = h) :
    ∃ e : pullback g (pullback.fst f w) ≅ pullback h w,
      e.hom ≫ pullback.fst h w = pullback.fst g (pullback.fst f w) := by
  have hA : IsPullback (pullback.fst g (pullback.fst f w))
      (pullback.snd g (pullback.fst f w) ≫ pullback.snd f w) h w := by
    have h₀ := (IsPullback.of_hasPullback g (pullback.fst f w)).paste_vert
      (IsPullback.of_hasPullback f w)
    rwa [hg] at h₀
  exact ⟨hA.isoIsPullback W T (IsPullback.of_hasPullback h w),
    IsPullback.isoIsPullback_hom_fst W T hA (IsPullback.of_hasPullback h w)⟩

/-- **Transitivity of base change**, in the form compatible with the base structure: base
changing a `K`-scheme first to `L` and then to `M` is base changing it directly to `M`, by an
isomorphism over `Spec M`. -/
theorem baseChange_comp (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M] (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    ∃ e : Work.K3.baseChange L M (Work.K3.baseChange K L X) ≅ Work.K3.baseChange K M X,
      e.hom.IsOver (Spec (.of M)) := by
  obtain ⟨e, he⟩ := pullback_pullback_iso (specMap K L) (specMap L M) (X ↘ Spec (.of K))
    (specMap K M) (specMap_comp K L M)
  refine ⟨e, ?_⟩
  rw [Scheme.Hom.isOver_iff]
  exact he

end Work.K3
