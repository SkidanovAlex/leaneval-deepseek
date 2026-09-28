import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.smallChains_homology_iso_int
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.smallLift_cov
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.homologyPairShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The five lemma step of excision

This file assembles Eilenberg–Steenrod excision from the small-simplices machinery of the
workspace.  Let `A, V ⊆ X` be subsets with `interior A ∪ interior V = univ` (the classical
hypothesis `X = int A ∪ int B` of excision).  Then the inclusion of pairs `(V, A ∩ V) ↪ (X, A)`
is a homology isomorphism.

The proof compares the short exact sequence of the pair `(X, A)` with the short exact sequence

`0 ⟶ C_*(A) ⟶ C^{A,V}_*(X) ⟶ C^{A,V}_*(X)/C_*(A) ⟶ 0`

of the *small* chains of the cover `{A, V}`.  Its first two terms are the identity and the inclusion
`smallToSing A V`, and both induce isomorphisms on homology: the first trivially, the second by the
small-simplices theorem in the form `smallChains_homology_iso_int` (which needs exactly
`interior A ∪ interior V = univ`).  The five lemma
(`HomologicalComplex.HomologySequence.quasiIso_τ₃`) then shows that the induced map on the relative
complexes is a quasi-isomorphism.  The remaining input, that the quotient
`C^{A,V}_*(X)/C_*(A)` is the relative chain complex of the pair `(V, A ∩ V)`, is the separate
statement `coker_smallOfU_iso_relChains`, which is used here as a hypothesis so that the five lemma
step is independent of it.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The small chains of `U` sit inside the singular chains of `X` as the `U`-chains. -/
theorem smallOfU_comp_smallToSing (U V : Set X) :
    smallOfU U V ≫ smallToSing U V = inclChains X U := by
  have hlift : smallLiftU U V ≫ (smallSubcomplex U V).ι = TopCat.toSSet.map (inclUX U) :=
    SSet.Subcomplex.lift_ι _ _
  show SSet.chainComplexMap (smallLiftU U V) (ModuleCat.of ℤ ℤ) ≫
      SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ) = _
  rw [← Functor.map_comp, hlift]
  rfl

/-- The small chains of `V` sit inside the singular chains of `X` as the `V`-chains. -/
theorem smallOfV_comp_smallToSing (U V : Set X) :
    smallOfV U V ≫ smallToSing U V = inclChains X V := by
  have hlift : smallLiftV U V ≫ (smallSubcomplex U V).ι = TopCat.toSSet.map (inclUX V) :=
    SSet.Subcomplex.lift_ι _ _
  show SSet.chainComplexMap (smallLiftV U V) (ModuleCat.of ℤ ℤ) ≫
      SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ) = _
  rw [← Functor.map_comp, hlift]
  rfl

/-- The inclusion of the small chains of `U` into the small chains of `X` is injective. -/
theorem mono_smallOfU (U V : Set X) : Mono (smallOfU U V) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  have h1 : (inclChains X U).f n x = (inclChains X U).f n y := by
    have h2 : (smallOfU U V ≫ smallToSing U V).f n x = (smallOfU U V ≫ smallToSing U V).f n y := by
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hxy]
    simpa only [smallOfU_comp_smallToSing] using h2
  exact injective_chainComplexMap_subtypeIncl X U n h1

/-- **The five lemma step of excision.**  Assuming the identification
`C^{A,V}_*(X)/C_*(A) ≅ C_*(V)/C_*(A ∩ V)` of the relative small chains with the relative chains of
the pair `(V, A ∩ V)` (the statement `Work.Cohomology.coker_smallOfU_iso_relChains`), the inclusion
of pairs induces an isomorphism `Hₙ(X,A) ≅ Hₙ(V, A ∩ V)` for every `n`. -/
theorem excision_iso_rel_of_iso (A V : Set X) (hcov : interior A ∪ interior V = Set.univ) (n : ℕ)
    (hid : Nonempty (cokernel (smallOfU A V) ≅
      relChains (TopCat.of V) (setOf (fun x : V => (x : X) ∈ A)))) :
    Nonempty ((relChains X A).homology n ≅
      (relChains (TopCat.of V) (setOf (fun x : V => (x : X) ∈ A))).homology n) := by
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallOfU A V) (cokernel.π (smallOfU A V)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (smallOfU A V))
      (mono_smallOfU A V) inferInstance
  have hzero : smallOfU A V ≫ (smallToSing A V ≫ cokernel.π (inclChains X A)) = 0 := by
    rw [← Category.assoc, smallOfU_comp_smallToSing, cokernel.condition]
  let tau3 : cokernel (smallOfU A V) ⟶ relChains X A :=
    cokernel.desc (smallOfU A V) (smallToSing A V ≫ cokernel.π (inclChains X A)) hzero
  have hcomm1 : (𝟙 (singularChains ℤ (TopCat.of A))) ≫ (hPairShort X A).f
      = S.f ≫ smallToSing A V := by
    show inclChains X A = smallOfU A V ≫ smallToSing A V
    rw [smallOfU_comp_smallToSing]
  have hcomm2 : smallToSing A V ≫ (hPairShort X A).g = S.g ≫ tau3 := by
    show smallToSing A V ≫ cokernel.π (inclChains X A)
      = cokernel.π (smallOfU A V) ≫ tau3
    rw [show tau3 = cokernel.desc (smallOfU A V)
      (smallToSing A V ≫ cokernel.π (inclChains X A)) hzero from rfl]
    rw [cokernel.π_desc]
  let phi : S ⟶ hPairShort X A :=
    ShortComplex.homMk (𝟙 (singularChains ℤ (TopCat.of A))) (smallToSing A V) tau3 hcomm1 hcomm2
  have hq1 : QuasiIso phi.τ₁ := by
    haveI : IsIso phi.τ₁ := by
      rw [show phi.τ₁ = 𝟙 (singularChains ℤ (TopCat.of A)) from rfl]
      infer_instance
    infer_instance
  have hq2 : QuasiIso phi.τ₂ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact smallChains_homology_iso_int A V hcov i
  have hq3 : QuasiIso phi.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ phi hS (hPairShort_shortExact X A) hq1 hq2
  have hiso3 : IsIso (HomologicalComplex.homologyMap phi.τ₃ n) := by
    have h := hq3.quasiIsoAt n
    rwa [quasiIsoAt_iff_isIso_homologyMap] at h
  obtain ⟨e⟩ := hid
  exact ⟨(asIso (HomologicalComplex.homologyMap phi.τ₃ n)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso e⟩

/-- The hypothesis of excision in the form used above: `interior A ∪ interior (complement Z) = univ`
as soon as `closure Z ⊆ interior A`. -/
theorem univ_eq_interior_union_compl (A Z : Set X) (h : closure Z ⊆ interior A) :
    interior A ∪ interior {x : X | x ∉ Z} = Set.univ := by
  have hcompl : {x : X | x ∉ Z} = (Zᶜ : Set X) := rfl
  rw [hcompl, interior_compl]
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
  by_cases hx : x ∈ closure Z
  · exact Or.inl (h hx)
  · exact Or.inr hx

end

end Work.Cohomology
