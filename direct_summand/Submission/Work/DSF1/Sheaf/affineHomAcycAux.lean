import Mathlib
import Submission.Work.DSF1.Sheaf.acyclicAffineHomDefs
import Submission.Work.DSF1.Sheaf.pushforward_injective
import Submission.Work.DSF1.Sheaf.isZero_iff_forall_modStalk

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-- Homology commutes with an exact functor (ℕ-indexed version). -/
theorem homology_iso_mapHomologicalComplex_nat {C : Type*} [CategoryTheory.Category C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive] [F.PreservesHomology] (K : CochainComplex C ℕ)
    (n : ℕ) :
    Nonempty (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      F.obj (K.homology n)) := by
  have h : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n = (K.sc n).map F := rfl
  exact ⟨by
    rw [show (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) =
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).homology from rfl, h]
    exact (K.sc n).mapHomologyIso F⟩

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Sections of a pushforward along an open immersion are sections over the preimage.** -/
theorem sectionsFunctor_comp_pushforward (W : X.Opens) (V : X.Opens) :
    (Work.DSF1.Sheaf.pushforwardι W ⋙ Work.DSF1.Sheaf.sectionsFunctor X V) =
      Work.DSF1.Sheaf.sectionsFunctor W.toScheme ((W.ι) ⁻¹ᵁ V) := rfl

/-- The complex of sections over `V` of the pushforward of a complex `K` on `W` is the complex of
sections over `W.ι ⁻¹ᵁ V` of `K`. -/
theorem sectionsComplex_pushforward_iso (W : X.Opens) (V : X.Opens)
    (K : CochainComplex W.toScheme.Modules ℕ) :
    Nonempty
      (((Work.DSF1.Sheaf.sectionsFunctor X V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≅
      (((Work.DSF1.Sheaf.sectionsFunctor W.toScheme ((W.ι) ⁻¹ᵁ V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K)) :=
  ⟨Iso.refl _⟩

/-- **Affine sections of the pushed forward resolution are acyclic.**  If `hL2` is the (delegated)
statement that the complex of sections of an injective resolution of `𝒪_W` over an affine open of
`W` is acyclic in positive degrees, then the same holds for the pushforward to `X` over any affine
open of `X`. -/
theorem isZero_homology_sections_pushforward_affine {W : X.Opens}
    (haff : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W))
    (I : CategoryTheory.InjectiveResolution (Work.DSF1.Sheaf.unitSheaf W))
    (hL2 : ∀ (U : W.toScheme.Opens), AlgebraicGeometry.IsAffineOpen U → ∀ n, 0 < n → IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
        (((Work.DSF1.Sheaf.sectionsFunctor W.toScheme U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)))
    (V : X.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) (n : ℕ) (hn : 0 < n) :
    IsZero ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
      (((Work.DSF1.Sheaf.sectionsFunctor X V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex))) := by
  haveI := haff
  have hU : AlgebraicGeometry.IsAffineOpen ((W.ι) ⁻¹ᵁ V) := hV.preimage W.ι
  obtain ⟨e⟩ := sectionsComplex_pushforward_iso W V I.cocomplex
  exact IsZero.of_iso (hL2 ((W.ι) ⁻¹ᵁ V) hU n hn)
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso e)

/-- A short complex of abelian groups is exact if and only if every element killed by the outgoing
map is in the image of the incoming map. -/
lemma ShortComplex.exact_iff_forall_exists {S : ShortComplex AddCommGrpCat.{u}} :
    S.Exact ↔ ∀ y : S.X₂, S.g y = 0 → ∃ x : S.X₁, S.f x = y := by
  constructor
  · intro hS y hy
    have hsurj : Function.Surjective (kernel.lift S.g S.f S.zero) := by
      rw [← AddCommGrpCat.epi_iff_surjective]
      exact S.exact_iff_epi_kernel_lift.mp hS
    have hy' : y ∈ (AddCommGrpCat.Hom.hom S.g).ker := by simpa using hy
    obtain ⟨x, hx⟩ := hsurj ((AddCommGrpCat.kernelIsoKer S.g).inv ⟨y, hy'⟩)
    refine ⟨x, ?_⟩
    have h1 : (kernel.ι S.g) ((kernel.lift S.g S.f S.zero) x) = (kernel.ι S.g)
        ((AddCommGrpCat.kernelIsoKer S.g).inv ⟨y, hy'⟩) := by rw [hx]
    simp only [← ConcreteCategory.comp_apply, Limits.kernel.lift_ι,
      AddCommGrpCat.kernelIsoKer_inv_comp_ι] at h1
    simpa using h1
  · intro h
    rw [S.exact_iff_epi_kernel_lift, AddCommGrpCat.epi_iff_surjective]
    intro y
    have hy : S.g (kernel.ι S.g y) = 0 := by
      have := ConcreteCategory.congr_hom (kernel.condition S.g) y
      simpa using this
    obtain ⟨x, hx⟩ := h (kernel.ι S.g y) hy
    refine ⟨x, ?_⟩
    apply ConcreteCategory.injective_of_mono_of_preservesPullback (kernel.ι S.g)
    simp only [← ConcreteCategory.comp_apply, Limits.kernel.lift_ι]
    exact hx

end Work.DSF1.Sheaf

