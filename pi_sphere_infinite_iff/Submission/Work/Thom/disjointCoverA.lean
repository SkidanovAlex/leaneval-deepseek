import Mathlib
import Submission.Work.Thom.Relocate.HonestFMV
import Submission.Work.Thom.TransgressionSquare
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **Naturality of the restriction `pdCohRes` with respect to the comparison isomorphism
`pdCohIso`**, stated at the level of `TopCat` and with the excluded set `A = ∅`.

The restriction `H^k(X) → H^k(U)` of the honest relative cohomology of the pair `(X,∅)`
transports under `pdCohIso` to the restriction `singularCohomologyMap ℤ (TopCat.of U) X
(subtypeIncl X U) k` of singular cohomology.

(Verbally this is `Work.Thom.pdCohRes_pdCohIso` of `Submission/Work/Thom/thomClass_of_cover.lean`,
which however lives in the `prod_sphere_aux` island; the proof below is self-contained in the
`prod_sphere_aux`-free island and only uses `Work.Thom.relCohMap_relToAbs`.) -/
theorem pdCohRes_pdCohIso_topcat (X : TopCat) (U : Set X) (n : ℕ) :
    Work.Cohomology.pdCohRes X (∅ : Set X) U n ≫ (Work.Thom.pdCohIso ↥U n).hom
      = (Work.Thom.pdCohIso ↥X n).hom
        ≫ Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥U) X
            (Work.Cohomology.subtypeIncl X U) n := by
  have h := Work.Thom.relCohMap_relToAbs (Work.Thom.subtypeMap U)
    ({y : U | (y : X) ∈ (∅ : Set X)}) (∅ : Set X) (fun y hy => hy) ℤ n
  rw [show Work.Cohomology.pdCohRes X (∅ : Set X) U n
      = Work.Thom.relCohMap (Work.Thom.subtypeMap U)
          ({y : U | (y : X) ∈ (∅ : Set X)}) (∅ : Set X) (fun y hy => hy) ℤ n from rfl,
    show Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥U) X
        (Work.Cohomology.subtypeIncl X U) n
      = Work.Thom.CohMap (Work.Thom.subtypeMap U) ℤ n from rfl,
    show (Work.Thom.pdCohIso ↥U n).hom
      = Work.Thom.relToAbs ℤ ({y : U | (y : X) ∈ (∅ : Set X)}) n from rfl,
    show (Work.Thom.pdCohIso ↥X n).hom = Work.Thom.relToAbs ℤ (∅ : Set X) n from rfl]
  exact h

/-- **The separating condition of a disjoint open cover, in the `prod_sphere_aux`-free island.**

This is the statement of `Work.Thom.eq_zero_of_singularCohomologyMap_eq_zero_of_disjoint`
(`Submission/Work/Thom/DisjointCover.lean`), which must NOT be reused: that module imports
`Submission.Work.Cohomology.isIso_smallIsoHom`, hence `Submission.Work.Cohomology.prod_sphere_aux`,
which declares `Work.Cohomology.Yt` — the same name as
`Submission.Work.Cohomology.CompatTrans.proj_pair_injective`, imported by every file of
`Submission/Work/TangentClasses/`, `Submission/Work/SignatureBordism/` and `Submission/Work/Thom/Interface.lean`.  So a *new* proof is required.

Plan: `Work.Thom.Relocate.HonestFMV.honestF_injective_of_disjoint` (a clean copy of
`Work.Thom.honestF_injective_of_disjoint` of `nonempty_thomClass_of_disjoint_cover.lean`) says that
the honest relative Mayer--Vietoris map `honestF X A U V n : pdCoh X A n → pdCohSub X A U n ⊞
pdCohSub X A V n` is injective when `U, V` are open, disjoint and cover `X`.  Its two components are
the restrictions `Work.Cohomology.pdCohRes`.  Conjugating with the canonical isomorphism
`Work.Thom.pdCohIso` (`Submission/Work/Thom/TransgressionSquare.lean`, giving
`pdCoh (TopCat.of X) ∅ n ≅ Coh ℤ n X` from `Work.Cohomology.relComplex_empty_homology_iso`)
identifies these with `singularCohomologyMap ℤ (TopCat.of ↥U) X (subtypeIncl X U) n` and the same
for `V`; the class in question is the image of `x` under the inverse of that isomorphism. -/
theorem disjointCoverA {X : TopCat} (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V) (hcov : U ∪ V = Set.univ) (n : ℕ)
    (x : Work.Cohomology.singularCohomology ℤ n X)
    (hU0 : (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥U) X
      (Work.Cohomology.subtypeIncl X U) n).hom x = 0)
    (hV0 : (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥V) X
      (Work.Cohomology.subtypeIncl X V) n).hom x = 0) : x = 0 := by
  have hnatU := pdCohRes_pdCohIso_topcat X U n
  have hnatV := pdCohRes_pdCohIso_topcat X V n
  -- the class `y : H^n(X,∅)` whose image under `pdCohIso` is `x`
  let y : Work.Cohomology.pdCoh X (∅ : Set X) n := (Work.Thom.pdCohIso ↥X n).symm.hom x
  have hy : (Work.Thom.pdCohIso ↥X n).hom y = x := by
    change (Work.Thom.pdCohIso ↥X n).hom ((Work.Thom.pdCohIso ↥X n).inv x) = x
    exact Iso.inv_hom_id_apply _ x
  -- it suffices to show that the two components of `honestF y` vanish
  have hzero : (Work.Cohomology.honestF X (∅ : Set X) U V n).hom y = 0 := by
    apply Work.Thom.biprod_eq_zero_of_fst_snd_eq_zero
    · have h2 : (ModuleCat.Hom.hom (biprod.fst :
          Work.Cohomology.pdCohSub X (∅ : Set X) U n ⊞ Work.Cohomology.pdCohSub X (∅ : Set X) V n
            ⟶ Work.Cohomology.pdCohSub X (∅ : Set X) U n))
          ((ModuleCat.Hom.hom (Work.Cohomology.honestF X (∅ : Set X) U V n)) y)
          = (ModuleCat.Hom.hom (Work.Cohomology.pdCohRes X (∅ : Set X) U n)) y := by
        have h := congrArg ModuleCat.Hom.hom (Work.Cohomology.honestF_fst' X (∅ : Set X) U V n)
        rw [ModuleCat.hom_comp] at h
        exact congrArg (fun f => f y) h
      rw [h2]
      have h4 : (Work.Thom.pdCohIso ↥U n).hom
            ((ModuleCat.Hom.hom (Work.Cohomology.pdCohRes X (∅ : Set X) U n)) y)
          = (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥U) X
              (Work.Cohomology.subtypeIncl X U) n).hom ((Work.Thom.pdCohIso ↥X n).hom y) := by
        have h3 := congrArg ModuleCat.Hom.hom hnatU
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h3
        exact congrArg (fun f => f y) h3
      rw [hy, hU0] at h4
      have hinj : Function.Injective (Work.Thom.pdCohIso ↥U n).hom :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      exact hinj (by rw [h4, map_zero])
    · have h2 : (ModuleCat.Hom.hom (biprod.snd :
          Work.Cohomology.pdCohSub X (∅ : Set X) U n ⊞ Work.Cohomology.pdCohSub X (∅ : Set X) V n
            ⟶ Work.Cohomology.pdCohSub X (∅ : Set X) V n))
          ((ModuleCat.Hom.hom (Work.Cohomology.honestF X (∅ : Set X) U V n)) y)
          = (ModuleCat.Hom.hom (Work.Cohomology.pdCohRes X (∅ : Set X) V n)) y := by
        have h := congrArg ModuleCat.Hom.hom (Work.Cohomology.honestF_snd' X (∅ : Set X) U V n)
        rw [ModuleCat.hom_comp] at h
        exact congrArg (fun f => f y) h
      rw [h2]
      have h4 : (Work.Thom.pdCohIso ↥V n).hom
            ((ModuleCat.Hom.hom (Work.Cohomology.pdCohRes X (∅ : Set X) V n)) y)
          = (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥V) X
              (Work.Cohomology.subtypeIncl X V) n).hom ((Work.Thom.pdCohIso ↥X n).hom y) := by
        have h3 := congrArg ModuleCat.Hom.hom hnatV
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h3
        exact congrArg (fun f => f y) h3
      rw [hy, hV0] at h4
      have hinj : Function.Injective (Work.Thom.pdCohIso ↥V n).hom :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      exact hinj (by rw [h4, map_zero])
  have hkey : y = 0 := Work.Thom.honestF_injective_of_disjoint X (∅ : Set X) U V hU hV hcov hd n
    (by rw [hzero, map_zero])
  rw [← hy, hkey, map_zero]

end

end Work.Thom
