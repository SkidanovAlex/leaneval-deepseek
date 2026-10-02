import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.lhAny_bijective_iff
import Submission.Work.LerayHirsch.Mv_exact
import Submission.Work.LerayHirsch.MvTM_translate
import Submission.Work.LerayHirsch.MvPieceTranslate
import Submission.Work.LerayHirsch.MvSquares
import Submission.Work.LerayHirsch.MvAux.HonestDegree
import Submission.Work.Thom.Ladder2
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.LerayHirsch.zetaPow_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [-instance] AddCommGroup.toIntModule

/-!
# The two-cover Mayer--Vietoris induction for Leray--Hirsch

This module assembles the two-cover step of the Leray--Hirsch induction:

> if the projectivisation of `Z` satisfies the Leray--Hirsch theorem over each of two open pieces
> `U`, `V` of the base and over their overlap, then it does so over all of `B`.

The proof runs the five lemma (`Work.Thom.five_lemma_LES'`, `Submission/Work/Thom/Ladder2.lean`)
on the two Mayer--Vietoris ladders of `Submission/Work/LerayHirsch/LhTwoCoverDefs.lean`

  `MvM k --MvF--> MvP k --MvG--> MvQ k --MvD--> MvM (k+1)`   (coefficients in the powers of `ζ`),
  `M₂ k --MvF₂--> P₂ k --MvG₂--> Q₂ k --MvDeltaTwo--> M₂ (k+1)`  (the cover of `P(E)`),

compared by `MvTM`, `MvTP = biprod.map MvTU MvTV`, `MvTQ`.  The exactness of the first ladder is
`Work.LerayHirsch.Mv_exact`, that of the second the honest Mayer--Vietoris exactness of
`Work.Cohomology.honest_exact₁/₂/₃`; the compatibility of the comparison with the three maps is
`Work.LerayHirsch.MvF_square`, `MvG_square`, `MvD_square`
(`Submission/Work/LerayHirsch/MvSquares.lean`); the comparison maps on the two pieces are
isomorphisms by `Work.LerayHirsch.isIso_MvTU` (`Submission/Work/LerayHirsch/MvPieceTranslate.lean`),
which identifies `MvTU` with the Leray--Hirsch map of `Z|_U`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section
variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- The comparison map `MvTP` on the two pieces is an isomorphism as soon as the two restricted
bundles satisfy Leray--Hirsch. -/
theorem isIso_MvTP (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B)
    (hU : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap U)) k))
    (hV : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap V)) k)) (k : ℕ) :
    CategoryTheory.IsIso (MvTP Z U V k) := by
  haveI h1 : CategoryTheory.IsIso (MvTU Z U k) := isIso_MvTU Z U hU k
  haveI h2 : CategoryTheory.IsIso (MvTV Z V k) := isIso_MvTV Z V hV k
  rw [MvTP_def]
  exact CategoryTheory.Iso.isIso_hom
    (CategoryTheory.Limits.biprod.mapIso (asIso (MvTU Z U k)) (asIso (MvTV Z V k)))

/-- **`lhAny` is bijective whenever `MvTM` is an isomorphism.** -/
theorem lhAny_bijective_of_isIso_MvTM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (k : ℕ) (h : CategoryTheory.IsIso (MvTM Z k)) :
    Function.Bijective (lhAny Z k) := by
  have hfun : lhAny Z k = fun (w : (i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B) =>
      (pdCohIso (ProjSpace Z) k).hom
        ((MvTM Z k).hom (fun (i : lhIdx m k) => (pdCohIso B (k - 2 * (i : ℕ))).inv (w i))) := by
    funext w
    rw [MvTM_translate Z k (fun (i : lhIdx m k) => (pdCohIso B (k - 2 * (i : ℕ))).inv (w i))]
    dsimp only []
    refine congrArg (lhAny Z k) ?_
    funext i
    exact (Iso.inv_hom_id_apply (pdCohIso B (k - 2 * (i : ℕ))) (w i)).symm
  rw [hfun]
  have h1 : Function.Bijective (fun (w : (i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B) =>
      fun (i : lhIdx m k) => (pdCohIso B (k - 2 * (i : ℕ))).inv (w i)) := by
    refine ⟨?_, ?_⟩
    · intro w w' hww
      funext i
      have hwwi : (pdCohIso B (k - 2 * (i : ℕ))).inv (w i)
          = (pdCohIso B (k - 2 * (i : ℕ))).inv (w' i) := congrFun hww i
      exact (CategoryTheory.ConcreteCategory.bijective_of_isIso
        (pdCohIso B (k - 2 * (i : ℕ))).inv).1 hwwi
    · intro v
      exact ⟨fun (i : lhIdx m k) => (pdCohIso B (k - 2 * (i : ℕ))).hom (v i),
        funext (fun i => Iso.hom_inv_id_apply (pdCohIso B (k - 2 * (i : ℕ))) (v i))⟩
  have h2 : Function.Bijective (MvTM Z k).hom := by
    rw [isIso_iff_mono_and_epi, ModuleCat.mono_iff_injective, ModuleCat.epi_iff_surjective] at h
    exact h
  have h3 : Function.Bijective (pdCohIso (ProjSpace Z) k).hom :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso _
  show Function.Bijective ((pdCohIso (ProjSpace Z) k).hom ∘ (MvTM Z k).hom ∘
    (fun (w : (i : lhIdx m k) → Coh ℤ (k - 2 * (i : ℕ)) B) (i : lhIdx m k) =>
      (pdCohIso B (k - 2 * (i : ℕ))).inv (w i)))
  exact h3.comp (h2.comp h1)

/-- **The five lemma for the two-cover ladder**: the comparison `MvTM` is an isomorphism in every
degree as soon as it is on the pieces. -/
theorem isIso_MvTM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hU'' : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap U)) k))
    (hV'' : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap V)) k))
    (hUV'' : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap (U ∩ V))) k)) :
    ∀ k : ℕ, CategoryTheory.IsIso (MvTM Z k) := by
  have hcov' : projMap Z ⁻¹' U ∪ projMap Z ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hcov, Set.preimage_univ]
  have hU' : IsOpen (projMap Z ⁻¹' U) := hU.preimage (projMap Z).continuous
  have hV' : IsOpen (projMap Z ⁻¹' V) := hV.preimage (projMap Z).continuous
  obtain ⟨hex1, hex2, hex3, hex4⟩ := Mv_exact (B := B) (m := m) (U := U) (V := V) hU hV hcov
  exact five_lemma_LES'
    (M₁ := fun k => MvM B m k) (P₁ := fun k => MvP B m k U V) (Q₁ := fun k => MvQ B m k U V)
    (M₂ := fun k => pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) k)
    (P₂ := fun k => pdCohBiprod (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) k)
    (Q₂ := fun k => pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
      (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k)
    (F₁ := fun k => MvF (B := B) m k U V) (G₁ := fun k => MvG (B := B) m k U V)
    (δ₁ := fun k => MvD (B := B) m k U V hU hV hcov)
    (F₂ := fun k => MvF₂ Z U V k) (G₂ := fun k => MvG₂ Z U V k)
    (δ₂ := fun k => MvDeltaTwo Z hU hV hcov k)
    (e₂₁ := fun k => hex1 k) (e₃₁ := fun k => hex2 k) (e₁₁ := fun k => hex3 k)
    (e₂₂ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
      (honest_exact₂ (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) hU' hV' hcov' k))
    (e₃₂ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
      (honest_exact₃ (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) hU' hV' hcov' k))
    (e₁₂ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
      (honest_exact₁ (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
        (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) hU' hV' hcov' k))
    (TM := fun k => MvTM Z k) (TP := fun k => MvTP Z U V k) (TQ := fun k => MvTQ Z U V k)
    (f₁ := hex4)
    (f₂ := fun u hu => by
      have hk : u ∈ (honestF (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U) (projMap Z ⁻¹' V) 0).hom.ker := LinearMap.mem_ker.mpr hu
      rw [MvAux.honestF_ker_eq_bot (B := ProjSpace Z) (U := projMap Z ⁻¹' U)
        (V := projMap Z ⁻¹' V) hU' hV' hcov', Submodule.mem_bot] at hk
      exact ⟨0, by rw [hk, map_zero]⟩)
    (hF := fun k => MvF_square Z (B := B) (m := m) (U := U) (V := V) k)
    (hG := fun k => MvG_square Z (B := B) (m := m) (U := U) (V := V) k)
    (hδ := fun k => MvD_square Z (B := B) (m := m) (U := U) (V := V) hU hV hcov k)
    (hP := fun k => isIso_MvTP Z U V hU'' hV'' k)
    (hQ := fun k => isIso_MvTQ Z U V hUV'' k)

theorem lerayHirschFull_of_two_cover {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hU' : Work.LerayHirsch.LerayHirschFull (Work.Thom.bundleComap Z (Work.Thom.subtypeMap U)))
    (hV' : Work.LerayHirsch.LerayHirschFull (Work.Thom.bundleComap Z (Work.Thom.subtypeMap V)))
    (hUV' : Work.LerayHirsch.LerayHirschFull (Work.Thom.bundleComap Z (Work.Thom.subtypeMap (U ∩ V)))) :
    Work.LerayHirsch.LerayHirschFull Z := by
  refine (lhAny_bijective_iff Z).mp ?_
  intro k
  exact lhAny_bijective_of_isIso_MvTM Z k
    (isIso_MvTM Z hU hV hcov
      ((lhAny_bijective_iff (bundleComap Z (subtypeMap U))).mpr hU')
      ((lhAny_bijective_iff (bundleComap Z (subtypeMap V))).mpr hV')
      ((lhAny_bijective_iff (bundleComap Z (subtypeMap (U ∩ V)))).mpr hUV') k)

end

end Work.LerayHirsch
