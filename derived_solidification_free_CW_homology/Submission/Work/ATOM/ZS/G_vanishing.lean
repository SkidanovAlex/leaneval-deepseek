import Mathlib
import Submission.Work.ATOM.ZS.Topo.Maps

namespace Work.ATOM.ZS

open CategoryTheory MonoidalCategory LightCondensed

/-- Functoriality of `zmap = ℤ[-]`: `ℤ[-]` is a functor, so it preserves composition. -/
lemma zmap_comp {S T U : LightProfinite.{0}} (f : S ⟶ T) (g : T ⟶ U) :
    Work.ATOM.zmap (f ≫ g) = Work.ATOM.zmap f ≫ Work.ATOM.zmap g :=
  Functor.map_comp _ _ _

/-- The composite `{∞} × S ⟶ (ℕ∪{∞}) × S ⟶ ℕ∪{∞}` is the constant map at `∞`. -/
lemma whiskerRight_ι_psiN (S : LightProfinite.{0}) [Infinite S] :
    MonoidalCategory.whiskerRight LightCondensed.ι S ≫ Work.ATOM.psiN S =
      Work.ATOM.toPt (Work.ATOM.pt ⊗ S) ≫ LightCondensed.ι := by
  apply ConcreteCategory.hom_ext
  intro p
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rfl

/-- **The vanishing of `ψ` on `{∞} × S`.**  `ψ(∞,x) = ∞` (`Work.ATOM.psiN_infty`), so
`zmap ψ ≫ P_proj` kills the image of `zmap (whiskerRight ι S)`: the composite
`whiskerRight ι S ≫ ψ` is the constant map at `∞`, whose `zmap` is `P_map` composed with the
projection from `pt ⊗ S`, and `P_map ≫ P_proj = 0`.  Hence it descends along `Work.ATOM.EA S` to
`G : P ⊗ ℤ[S] ⟶ P`. -/
theorem G_vanishing (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫
      (Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj) = 0 := by
  -- the two `zmap`s combine, and the composite of the underlying maps is constant at `∞`
  have h₁ : Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫
        Work.ATOM.zmap (Work.ATOM.psiN S) =
      Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S ≫
        Work.ATOM.psiN S) :=
    (zmap_comp (MonoidalCategory.whiskerRight LightCondensed.ι S) (Work.ATOM.psiN S)).symm
  have h₂ : Work.ATOM.zmap (Work.ATOM.toPt (Work.ATOM.pt ⊗ S) ≫ LightCondensed.ι) =
      Work.ATOM.zmap (Work.ATOM.toPt (Work.ATOM.pt ⊗ S)) ≫ LightCondensed.P_map :=
    zmap_comp (Work.ATOM.toPt (Work.ATOM.pt ⊗ S)) LightCondensed.ι
  have hzero : LightCondensed.P_map ≫ LightCondensed.P_proj = 0 :=
    CategoryTheory.Limits.cokernel.condition LightCondensed.P_map
  rw [← Category.assoc, h₁, whiskerRight_ι_psiN S, h₂, Category.assoc, hzero]
  simp

end Work.ATOM.ZS
