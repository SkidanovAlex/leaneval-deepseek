import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

/-! Helper lemmas for the finite case of `Work.ATOM.solidCofibrant_atom_of_finite`; kept in their
own namespace so that they cannot clash with other files of the `ATOM` area. -/
namespace FiniteAtom

/-- A surjection of light profinite sets onto a *finite* light profinite set splits.  Indeed
the domain is the disjoint union of the non-empty fibres, and choosing one point in each fibre
is continuous because a finite Hausdorff space is discrete. -/
theorem exists_section_of_finite {S T : LightProfinite.{0}} [Finite S] (π : T ⟶ S)
    (hπ : Epi π) : ∃ σ : S ⟶ T, σ ≫ π = 𝟙 S := by
  classical
  have hs : Function.Surjective (π : T → S) := (LightProfinite.epi_iff_surjective π).mp hπ
  choose t ht using hs
  exact ⟨ConcreteCategory.ofHom ⟨fun s => t s, continuous_of_discreteTopology⟩, by
    ext s
    simp [ht s]⟩

/-- For a finite light profinite set `S`, the free light condensed abelian group `ℤ[S]` is
projective.  Indeed, every epimorphism of light condensed abelian groups is locally surjective
on a cover of `S` by a *single* surjection `T ↠ S`
(`LightCondMod.factorsThru_lightProfinite_epi_of_epi`), and such a surjection splits by
`exists_section_of_finite`, which produces the required lift. -/
theorem projective_zfree_of_finite (S : LightProfinite.{0}) [Finite S] :
    Projective ((LightCondensed.free ℤ).obj S.toCondensed) where
  factors := by
    intro E X f e he
    haveI : Epi e := he
    let F := lightProfiniteToLightCondSet ⋙ LightCondensed.free ℤ
    obtain ⟨T, π, g, hπ, hcomm⟩ := LightCondMod.factorsThru_lightProfinite_epi_of_epi ℤ e f
    obtain ⟨σ, hσ⟩ := exists_section_of_finite π hπ
    refine ⟨F.map σ ≫ g, ?_⟩
    have h2 : F.map σ ≫ F.map π = 𝟙 (F.obj S) := by
      rw [← Functor.map_comp, hσ]
      simp
    calc (F.map σ ≫ g) ≫ e = F.map σ ≫ (g ≫ e) := Category.assoc ..
      _ = F.map σ ≫ (F.map π ≫ f) := by rw [← hcomm]
      _ = (F.map σ ≫ F.map π) ≫ f := (Category.assoc ..).symm
      _ = 𝟙 (F.obj S) ≫ f := by rw [h2]
      _ = f := Category.id_comp _

/-- A cochain complex concentrated in a single degree on a projective object is K-projective:
it is bounded below and all its terms are projective
(`CochainComplex.isKProjective_of_projective`). -/
theorem isKProjective_singleC (A : LightCondAb) [Projective A] (n : ℤ) :
    ((singleC n).obj A).IsKProjective := by
  have hX : ∀ m : ℤ, Projective (((singleC n).obj A).X m) := by
    intro m
    by_cases hm : m = n
    · rw [hm]
      exact CategoryTheory.Projective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n A).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n A m hm).projective
  haveI := hX
  exact CochainComplex.isKProjective_of_projective _ n

end FiniteAtom

/-- The atom on a *finite* light profinite set is solid-cofibrant (it is a coproduct of free
modules on a point, hence projective, hence K-projective). -/
theorem solidCofibrant_atom_of_finite (S : LightProfinite.{0}) [Finite S] (n : ℤ) :
    Submission.Blueprint.SolidCofibrant
      ((Work.ATOM.singleC n).obj ((LightCondensed.free ℤ).obj S.toCondensed)) := by
  haveI : Projective ((LightCondensed.free ℤ).obj S.toCondensed) :=
    FiniteAtom.projective_zfree_of_finite S
  haveI : ((Work.ATOM.singleC n).obj ((LightCondensed.free ℤ).obj S.toCondensed)).IsKProjective :=
    FiniteAtom.isKProjective_singleC _ n
  intro N
  exact CochainComplex.IsKProjective.Qh_map_bijective _
    (Submission.Blueprint.hq (Submission.Blueprint.ιC.obj N))

end

end Work.ATOM
