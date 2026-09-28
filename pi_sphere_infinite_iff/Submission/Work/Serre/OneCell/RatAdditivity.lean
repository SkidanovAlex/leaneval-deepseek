import Mathlib
import Submission.Work.Serre.serreC0SigmaHomology
import Submission.Work.StemsB.sphRatHomology

/-!
# Additivity of rational homology over a disjoint union

`Work.Serre.serreC0SigmaHomology` proves, over `ℤ`, that the canonical map
`∐ᵢ Hₙ(Xᵢ;ℤ) ⟶ Hₙ(Σᵢ Xᵢ;ℤ)` is an isomorphism.  Here we transfer this to `ℚ`: the target
theorem `Work.Serre.OneCell.oneCellPerCell` needs the *rational* homology of a disjoint union of
spaces, and the transfer is by flat base change `- ⊗[ℤ] ℚ` (which is a left adjoint, so it preserves
coproducts, and is exact, so it preserves homology).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct

namespace Work.Serre.OneCell

noncomputable section

/-- The base-change functor `- ⊗[ℤ] ℚ` on `ℤ`-modules. -/
abbrev ratF : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)

/-! ## A coproduct of zero objects is a zero object -/

/-- A coproduct of zero objects is a zero object. -/
theorem isZero_coproduct {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type}
    (M : ι → C) [HasCoproduct M] (h : ∀ i, IsZero (M i)) : IsZero (∐ M) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro i
  rw [Category.comp_id, comp_zero]
  exact IsZero.eq_zero_of_src (h i) (Sigma.ι M i)

/-! ## Base change of singular homology -/

/-- The base-change comparison `Hₖ(X;ℚ) ≅ (IntRatF)(Hₖ(X;ℤ))` for a topological space `X`. -/
noncomputable def ratHomologyBaseChange (X : TopCat) (k : ℕ) :
    (Work.Cohomology.singularChains ℚ X).homology k ≅
      ratF.obj ((Work.Cohomology.singularChains ℤ X).homology k) := by
  haveI hf : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI hfl : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI hfc : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) := inferInstance
  haveI hph : (ModuleCat.extendScalars (Int.castRingHom ℚ)).PreservesHomology := inferInstance
  haveI hcop : ∀ (S : Type),
      PreservesColimitsOfShape (Discrete S) (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    fun _ => inferInstance
  have hΦ : (ratF.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Work.Cohomology.singularChains ℤ X) ≅ Work.Cohomology.singularChains ℚ X :=
    Work.StemsB.SphRat.chainComplexBaseChange ratF (TopCat.toSSet.obj X)
        (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj X)
        Work.StemsB.SphRat.extendScalarsIntRatIso
  exact (HomologicalComplex.homologyMapIso hΦ k).symm ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange ratF
      (Work.Cohomology.singularChains ℤ X) k).some

/-! ## The object-level additivity -/

/-- **The rational homology of a disjoint union is the direct sum of the rational homologies of
the pieces.** -/
noncomputable def ratSigmaHomologyIso {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (k : ℕ) :
    (Work.Cohomology.singularChains ℚ (TopCat.of (Σ i, X i))).homology k ≅
      ∐ fun i => (Work.Cohomology.singularChains ℚ (TopCat.of (X i))).homology k := by
  haveI hcop : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) ratF :=
    fun _ => inferInstance
  have hγ : IsIso (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Σ i, X i))
        (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) k)) :=
    Work.Serre.serreC0SigmaHomology X k
  have eZ : (∐ fun i => (Work.Cohomology.singularChains ℤ (TopCat.of (X i))).homology k) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of (Σ i, X i))).homology k :=
    asIso (Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Σ i, X i))
        (TopCat.ofHom ⟨Sigma.mk i, continuous_sigmaMk⟩)) k))
  exact ratHomologyBaseChange (TopCat.of (Σ i, X i)) k ≪≫
    (ratF.mapIso eZ).symm ≪≫
    (Limits.PreservesCoproduct.iso ratF
      (fun i => (Work.Cohomology.singularChains ℤ (TopCat.of (X i))).homology k)) ≪≫
    Limits.Sigma.mapIso (fun i => (ratHomologyBaseChange (TopCat.of (X i)) k).symm)

/-- **The vanishing lemma**: if every piece of a disjoint union has vanishing rational homology in
degree `k`, so has the union. -/
theorem isZero_homology_sigma {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] (k : ℕ)
    (h : ∀ i, IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of (X i))).homology k)) :
    IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of (Σ i, X i))).homology k) :=
  IsZero.of_iso (isZero_coproduct _ h) (ratSigmaHomologyIso X k)

end

end Work.Serre.OneCell
