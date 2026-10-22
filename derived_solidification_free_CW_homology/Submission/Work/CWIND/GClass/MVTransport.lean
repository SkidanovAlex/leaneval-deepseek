import Submission.Work.CWIND.GClass.GG_preserves_pushout

/-!
# The quasi-isomorphism of the Mayer–Vietoris comparison map

The singular-chain Mayer–Vietoris theorem (`SingMVProp`) says that for open `U, V ⊆ X` with
`U ∪ V = X`, the canonical map from the pushout of `C(U∩V) → C(U)`, `C(U∩V) → C(V)` to `C(X)`
is a quasi-isomorphism of `ℕ`-graded chain complexes of abelian groups.  To use it in the world
of cochain complexes of light condensed abelian groups, we apply the functor `GG`; the result
`GG_quasiIso_pushout_desc` shows that the image of the pushout-desc map is a quasi-isomorphism.
The compatibility between the pushout in the source and the pushout of the images is provided by
`GG_preserves_pushout` (`Submission/Work/CWIND/GClass/GG_preserves_pushout.lean`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

/-- The canonical comparison map from the pushout of the `GG`-images of two maps to the
`GG`-image of the pushout of the two maps. -/
noncomputable def GGpushoutComparison {K₀ K₁ K₂ : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f₁ : K₀ ⟶ K₁) (f₂ : K₀ ⟶ K₂) :
    pushout (GG.map f₁) (GG.map f₂) ⟶ GG.obj (pushout f₁ f₂) :=
  pushout.desc (GG.map (pushout.inl f₁ f₂)) (GG.map (pushout.inr f₁ f₂))
    (by rw [← GG.map_comp, ← GG.map_comp, pushout.condition])

lemma GGpushoutComparison_eq {K₀ K₁ K₂ : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f₁ : K₀ ⟶ K₁) (f₂ : K₀ ⟶ K₂) :
    GGpushoutComparison f₁ f₂ =
      pushout.desc (GG.map (pushout.inl f₁ f₂)) (GG.map (pushout.inr f₁ f₂))
        (by rw [← GG.map_comp, ← GG.map_comp, pushout.condition]) := rfl

/-- The canonical comparison map is an isomorphism. -/
instance isIso_GGpushoutComparison {K₀ K₁ K₂ : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f₁ : K₀ ⟶ K₁) (f₂ : K₀ ⟶ K₂) : IsIso (GGpushoutComparison f₁ f₂) := by
  have hp : IsPushout (GG.map f₁) (GG.map f₂) (GG.map (pushout.inl f₁ f₂))
      (GG.map (pushout.inr f₁ f₂)) :=
    GG_preserves_pushout (IsPushout.of_hasPushout f₁ f₂)
  have hp' : IsPushout (GG.map f₁) (GG.map f₂) (pushout.inl (GG.map f₁) (GG.map f₂))
      (pushout.inr (GG.map f₁) (GG.map f₂)) :=
    IsPushout.of_hasPushout (GG.map f₁) (GG.map f₂)
  have heq : GGpushoutComparison f₁ f₂ = (hp'.isoIsPushout _ _ hp).hom := by
    apply IsPushout.hom_ext hp'
    · rw [GGpushoutComparison_eq, pushout.inl_desc, IsPushout.inl_isoIsPushout_hom]
    · rw [GGpushoutComparison_eq, pushout.inr_desc, IsPushout.inr_isoIsPushout_hom]
  rw [heq]
  infer_instance

/-- The `GG`-image of the pushout comparison map of a pair of maps fitting into a commutative
square is a quasi-isomorphism, provided the pushout-comparison map of the pair is. -/
theorem GG_quasiIso_pushout_desc {K₀ K₁ K₂ M : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    {f₁ : K₀ ⟶ K₁} {f₂ : K₀ ⟶ K₂} {a₁ : K₁ ⟶ M} {a₂ : K₂ ⟶ M}
    (w : f₁ ≫ a₁ = f₂ ≫ a₂) (hu : QuasiIso (pushout.desc a₁ a₂ w)) :
    QuasiIso (pushout.desc (GG.map a₁) (GG.map a₂)
      (by rw [← GG.map_comp, ← GG.map_comp, w])) := by
  have w' : GG.map f₁ ≫ GG.map a₁ = GG.map f₂ ≫ GG.map a₂ := by
    rw [← GG.map_comp, ← GG.map_comp, w]
  change QuasiIso (pushout.desc (GG.map a₁) (GG.map a₂) w')
  have hcomp : GGpushoutComparison f₁ f₂ ≫ GG.map (pushout.desc a₁ a₂ w) =
      pushout.desc (GG.map a₁) (GG.map a₂) w' := by
    rw [GGpushoutComparison_eq]
    apply Limits.pushout.hom_ext
    · rw [← Category.assoc, Limits.pushout.inl_desc, ← Functor.map_comp,
        Limits.pushout.inl_desc, Limits.pushout.inl_desc]
    · rw [← Category.assoc, Limits.pushout.inr_desc, ← Functor.map_comp,
        Limits.pushout.inr_desc, Limits.pushout.inr_desc]
  rw [← hcomp]
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb (GGpushoutComparison f₁ f₂ ≫
    GG.map (pushout.desc a₁ a₂ w)), DerivedCategory.Q.map_comp]
  haveI hq : IsIso ((DerivedCategory.Q).map (GG.map (pushout.desc a₁ a₂ w))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb _).2 (GG_preserves_quasiIso _ hu)
  exact inferInstance

end Work.CWIND.GClass
