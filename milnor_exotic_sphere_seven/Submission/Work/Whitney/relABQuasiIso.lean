import Mathlib
import Submission.Work.Cohomology.CompatTrans.relComplexIsoDualZ
import Submission.Work.Whitney.dualZCompatAux
import Submission.Work.Cohomology.smallChainsHomotopyEquivInt
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.smallProj_spec
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.smallChainSubmodule_eq_sup
import Submission.Work.Whitney.RelABComplex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion `C^*(X, A∪B;R) ⟶ C^*(X, A+B;R)` is a quasi-isomorphism

For open `A, B ⊆ X` and any commutative ring `R`, this file proves that the inclusion of cochain
complexes `pdABInclRelR : C^*(X, A∪B;R) ⟶ C^*(X, A+B;R)` is a quasi-isomorphism.

The proof is the coefficient-generic version of `Work.Cohomology.pdABCoh_quasiIso`: the small
chains of the cover `(A,B)` of `A ∪ B` corestrict to the singular chains of `A ∪ B`, giving a
degreewise split short exact sequence morphism all of whose entries except the cokernel map are
already known to be (dual) quasi-isomorphisms; the map `isIso_homologyMap_tau1` then produces the
quasi-isomorphism on the third term, which is identified with `pdABInclRelR` via the `ℤ`-duality of
the relative chain complexes.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

namespace Work.Whitney

open Work.Cohomology

noncomputable section

/-! ## The corestriction of the small simplices of `(A,B)` to the union `A ∪ B` -/

/-- A small simplex of `(A,B)` in `X` has image in `A ∪ B`, so it can be viewed as a simplex of
the subspace `A ∪ B`. -/
def relABUnionApp {M : TopCat} (U V : Set M) (n : SimplexCategoryᵒᵖ) :
    (smallSSet U V).obj n ⟶ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))).obj n :=
  ↾ fun (x : (smallSSet U V).obj n) =>
    (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) n).symm
      ⟨fun z => ⟨(TopCat.toSSetObjEquiv M n x.1) z, by
          rcases x.2 with h | h
          · exact Or.inl (h ⟨z, rfl⟩)
          · exact Or.inr (h ⟨z, rfl⟩)⟩,
       Continuous.subtype_mk (TopCat.toSSetObjEquiv M n x.1).continuous (fun z => by
          rcases x.2 with h | h
          · exact Or.inl (h ⟨z, rfl⟩)
          · exact Or.inr (h ⟨z, rfl⟩))⟩

/-- The corestriction map `small(U,V) ⟶ Simp(U ∪ V)`. -/
def relABUnionToSing {M : TopCat} (U V : Set M) :
    smallSSet U V ⟶ TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)) where
  app := relABUnionApp U V
  naturality n m f := by
    ext x
    apply (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) m).injective
    ext z
    rfl

/-- The trace of `U` on `U ∪ V`. -/
def relABTraceU {M : TopCat} (U V : Set M) : Set (TopCat.of (U ∪ V : Set M)) := {x | (x : M) ∈ U}

/-- The trace of `V` on `U ∪ V`. -/
def relABTraceV {M : TopCat} (U V : Set M) : Set (TopCat.of (U ∪ V : Set M)) := {x | (x : M) ∈ V}

theorem relABUnionToSing_comp_incl {M : TopCat} (U V : Set M) :
    relABUnionToSing U V ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))
    = (smallSubcomplex U V).ι := by
  ext n x
  apply (TopCat.toSSetObjEquiv M n).injective
  ext z
  rfl

theorem relABUnionToSing_range_le {M : TopCat} (U V : Set M) :
    SSet.Subcomplex.range (relABUnionToSing U V)
      ≤ smallSubcomplex (relABTraceU U V) (relABTraceV U V) := by
  intro n y hy
  rw [Subfunctor.range_obj] at hy
  obtain ⟨x, rfl⟩ := hy
  rcases x.2 with h | h
  · left; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩
  · right; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩

theorem relABOfUnionFun_range_le {M : TopCat} (U V : Set M) :
    SSet.Subcomplex.range ((smallSubcomplex (relABTraceU U V) (relABTraceV U V)).ι
        ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))) ≤ smallSubcomplex U V := by
  intro n y hy
  rw [Subfunctor.range_obj] at hy
  obtain ⟨x, rfl⟩ := hy
  rcases x.2 with h | h
  · left; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩
  · right; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩

/-- Corestriction to the small simplices of the union. -/
def relABUnionToSmall {M : TopCat} (U V : Set M) :
    smallSSet U V ⟶ smallSSet (relABTraceU U V) (relABTraceV U V) :=
  (smallSubcomplex (relABTraceU U V) (relABTraceV U V)).lift (relABUnionToSing U V)
    (relABUnionToSing_range_le U V)

/-- The inverse of the corestriction. -/
def relABUnionOfSmall {M : TopCat} (U V : Set M) :
    smallSSet (relABTraceU U V) (relABTraceV U V) ⟶ smallSSet U V :=
  (smallSubcomplex U V).lift ((smallSubcomplex (relABTraceU U V) (relABTraceV U V)).ι
    ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))) (relABOfUnionFun_range_le U V)

theorem relABUnionOfSmall_comp {M : TopCat} (U V : Set M) :
    relABUnionOfSmall U V ≫ relABUnionToSing U V
      = (smallSubcomplex (relABTraceU U V) (relABTraceV U V)).ι := by
  ext n x
  apply (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) n).injective
  ext z
  rfl

theorem relABUnionToSmall_hom_inv {M : TopCat} (U V : Set M) :
    relABUnionToSmall U V ≫ relABUnionOfSmall U V = 𝟙 (smallSSet U V) := by
  unfold relABUnionToSmall relABUnionOfSmall
  rw [← cancel_mono (smallSubcomplex U V).ι]
  rw [Category.assoc]
  rw [SSet.Subcomplex.lift_ι]
  rw [← Category.assoc]
  rw [SSet.Subcomplex.lift_ι]
  rw [relABUnionToSing_comp_incl]
  rw [Category.id_comp]

theorem relABUnionOfSmall_inv_hom {M : TopCat} (U V : Set M) :
    relABUnionOfSmall U V ≫ relABUnionToSmall U V
      = 𝟙 (smallSSet (relABTraceU U V) (relABTraceV U V)) := by
  unfold relABUnionToSmall relABUnionOfSmall
  rw [← cancel_mono (smallSubcomplex (relABTraceU U V) (relABTraceV U V)).ι]
  rw [Category.assoc]
  rw [SSet.Subcomplex.lift_ι]
  rw [show SSet.Subcomplex.lift ((smallSubcomplex (relABTraceU U V) (relABTraceV U V)).ι
        ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))) (relABOfUnionFun_range_le U V)
      ≫ relABUnionToSing U V
      = (smallSubcomplex (relABTraceU U V) (relABTraceV U V)).ι from relABUnionOfSmall_comp U V]
  rw [Category.id_comp]



/-! ## The corestriction chain map `K → C_*(A ∪ B)` and its homotopy equivalence -/

/-- The chain map `C^{A,B}_*(X) ⟶ C_*(A ∪ B)` given by corestricting small simplices. -/
def relABPhi {M : TopCat} (A B : Set M) :
    smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set M)) :=
  SSet.chainComplexMap (relABUnionToSing A B) (ModuleCat.of ℤ ℤ)

lemma isIso_dualZMap_of_iso {C D : ChainComplex (ModuleCat ℤ) ℕ} (R : Type) [CommRing R]
    (f : C ⟶ D) [IsIso f] : IsIso (dualZMapCompat R C D f) := by
  refine ⟨dualZMapCompat R D C (CategoryTheory.inv f), ?_, ?_⟩
  · rw [← dualZMapCompat_comp, IsIso.inv_hom_id f, dualZMapCompat_id]
  · rw [← dualZMapCompat_comp, IsIso.hom_inv_id f, dualZMapCompat_id]

def relABDualZIsoOfIso {C D : ChainComplex (ModuleCat ℤ) ℕ} (R : Type) [CommRing R]
    (e : C ≅ D) : dualZCompat R C ≅ dualZCompat R D :=
  ⟨dualZMapCompat R D C e.inv, dualZMapCompat R C D e.hom,
    (by rw [← dualZMapCompat_comp, e.hom_inv_id, dualZMapCompat_id]),
    (by rw [← dualZMapCompat_comp, e.inv_hom_id, dualZMapCompat_id])⟩

theorem relABPhi_comp_incl {M : TopCat} (A B : Set M) :
    relABPhi A B ≫ SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl M (A ∪ B)))
        (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (smallSubcomplex A B).ι (ModuleCat.of ℤ ℤ) := by
  rw [relABPhi, ← Functor.map_comp, relABUnionToSing_comp_incl]

theorem relABPhi_dualZ_quasiIso (R : Type) [CommRing R] {M : TopCat} {A B : Set M}
    (hA : IsOpen A) (hB : IsOpen B) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (dualZMapCompat R (smallChains A B) (singularChains ℤ (TopCat.of (A ∪ B : Set M)))
        (relABPhi A B)) m) := by
  have hU : IsOpen (relABTraceU A B) := hA.preimage continuous_subtype_val
  have hV : IsOpen (relABTraceV A B) := hB.preimage continuous_subtype_val
  have hcov : interior (relABTraceU A B) ∪ interior (relABTraceV A B) = Set.univ := by
    rw [hU.interior_eq, hV.interior_eq]
    ext x
    constructor
    · intro _; exact trivial
    · intro _
      rcases x.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨e, he⟩ := smallChainsHomotopyEquivInt (X := TopCat.of (A ∪ B : Set M))
    (relABTraceU A B) (relABTraceV A B) hcov
  have hfac : relABPhi A B
      = SSet.chainComplexMap (relABUnionToSmall A B) (ModuleCat.of ℤ ℤ) ≫ e.hom := by
    have h1 : relABUnionToSing A B
        = relABUnionToSmall A B
          ≫ (smallSubcomplex (relABTraceU A B) (relABTraceV A B)).ι :=
      (SSet.Subcomplex.lift_ι _ _).symm
    rw [relABPhi, he, h1]
    change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (relABUnionToSmall A B
            ≫ (smallSubcomplex (relABTraceU A B) (relABTraceV A B)).ι)
        = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
            (relABUnionToSmall A B)
          ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
              (smallSubcomplex (relABTraceU A B) (relABTraceV A B)).ι
    rw [Functor.map_comp]
  rw [hfac]
  simp only [dualZMapCompat_comp, HomologicalComplex.homologyMap_comp]
  haveI h1 : IsIso (HomologicalComplex.homologyMap
      (dualZMapCompat R (smallChains (relABTraceU A B) (relABTraceV A B))
        (singularChains ℤ (TopCat.of (A ∪ B : Set M))) e.hom) m) :=
    isIso_homologyMap_dualZMapCompat R e m
  haveI hisoSS : IsIso (relABUnionToSmall A B) :=
    ⟨relABUnionOfSmall A B, relABUnionToSmall_hom_inv A B, relABUnionOfSmall_inv_hom A B⟩
  haveI hiso : IsIso (SSet.chainComplexMap (relABUnionToSmall A B) (ModuleCat.of ℤ ℤ)) := by
    change IsIso (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (relABUnionToSmall A B))
    exact Functor.map_isIso _ (relABUnionToSmall A B)
  haveI hdual : IsIso (dualZMapCompat R (smallChains A B)
      (smallChains (relABTraceU A B) (relABTraceV A B))
      (SSet.chainComplexMap (relABUnionToSmall A B) (ModuleCat.of ℤ ℤ))) :=
    isIso_dualZMap_of_iso R _
  haveI h2 : IsIso (HomologicalComplex.homologyMap
      (dualZMapCompat R (smallChains A B)
        (smallChains (relABTraceU A B) (relABTraceV A B))
        (SSet.chainComplexMap (relABUnionToSmall A B) (ModuleCat.of ℤ ℤ))) m) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) m)
      (dualZMapCompat R (smallChains A B)
        (smallChains (relABTraceU A B) (relABTraceV A B))
        (SSet.chainComplexMap (relABUnionToSmall A B) (ModuleCat.of ℤ ℤ)))
  exact inferInstance


/-! ## The five-lemma: the cokernel map on chains dualises to a quasi-isomorphism -/

lemma mono_smallToSing {M : TopCat} (A B : Set M) : Mono (smallToSing A B) :=
  HomologicalComplex.mono_of_mono_f _
    (fun n => (ModuleCat.mono_iff_injective _).mpr (smallToSing_f_injective A B n))

lemma relABPhi_comp_incl' {M : TopCat} (A B : Set M) :
    relABPhi A B ≫ inclChains M (A ∪ B) = smallToSing A B := by
  change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (relABUnionToSing A B)
      ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.toSSet.map (subtypeIncl M (A ∪ B)))
    = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (smallSubcomplex A B).ι
  rw [← Functor.map_comp, relABUnionToSing_comp_incl]

lemma isDegreewiseSplit_pair' (X : TopCat) (A : Set X) : IsDegreewiseSplitCompat (hPairShort X A) := by
  intro n
  refine ⟨chainRetract ℤ X A n, ?_⟩
  show (inclChains X A).f n ≫ chainRetract ℤ X A n = 𝟙 _
  rw [inclChains, chainMap]
  exact chainRetract_spec ℤ X A n

lemma isDegreewiseSplit_small' {M : TopCat} (A B : Set M) :
    IsDegreewiseSplitCompat (ShortComplex.mk (smallToSing A B) (cokernel.π (smallToSing A B))
      (cokernel.condition _)) := by
  intro n
  refine ⟨smallProj A B n, ?_⟩
  exact (smallProj_spec A B).1 n

/-- The map on cokernels `C_*(X)/(C_*(A)+C_*(B)) ⟶ C_*(X)/C_*(A ∪ B)`. -/
noncomputable def relABq {M : TopCat} (A B : Set M) :
    cokernel (smallToSing A B) ⟶ relChains M (A ∪ B) :=
  cokernel.desc (smallToSing A B) (cokernel.π (inclChains M (A ∪ B))) (by
    rw [← relABPhi_comp_incl' A B, Category.assoc, cokernel.condition]
    simp)

set_option maxHeartbeats 4000000 in
theorem relABq_dualZ_quasiIso (R : Type) [CommRing R] {M : TopCat} {A B : Set M}
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (dualZMapCompat R (cokernel (smallToSing A B)) (relChains M (A ∪ B)) (relABq A B)) n) := by
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallToSing A B) (cokernel.π (smallToSing A B)) (cokernel.condition _)
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) (mono_smallToSing A B)
      inferInstance
  have hs₁ : IsDegreewiseSplitCompat S₁ := isDegreewiseSplit_small' A B
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort M (A ∪ B)
  have hS₂ : S₂.ShortExact := hPairShort_shortExact M (A ∪ B)
  have hs₂ : IsDegreewiseSplitCompat S₂ := isDegreewiseSplit_pair' M (A ∪ B)
  have hcomm1 : relABPhi A B ≫ S₂.f = S₁.f ≫ 𝟙 S₁.X₂ := by
    rw [Category.comp_id]
    exact relABPhi_comp_incl' A B
  have hcomm2 : (𝟙 S₁.X₂) ≫ S₂.g = S₁.g ≫ relABq A B := by
    rw [Category.id_comp]
    show cokernel.π (inclChains M (A ∪ B))
      = cokernel.π (smallToSing A B) ≫ relABq A B
    rw [show relABq A B = cokernel.desc (smallToSing A B)
        (cokernel.π (inclChains M (A ∪ B))) _ from rfl]
    rw [cokernel.π_desc]
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (relABPhi A B) (𝟙 S₁.X₂) (relABq A B) hcomm1 hcomm2
  have hT₁ : (dualZShortCompat R S₁).ShortExact := dualZSplitExactCompat R hS₁ hs₁
  have hT₂ : (dualZShortCompat R S₂).ShortExact := dualZSplitExactCompat R hS₂ hs₂
  let θ : dualZShortCompat R S₂ ⟶ dualZShortCompat R S₁ :=
    ShortComplex.homMk
      (dualZMapCompat R (cokernel (smallToSing A B)) (relChains M (A ∪ B : Set M)) (relABq A B))
      (dualZMapCompat R (singularChains ℤ M) (singularChains ℤ M) (𝟙 (singularChains ℤ M)))
      (dualZMapCompat R (smallChains A B) (singularChains ℤ (TopCat.of (A ∪ B : Set M))) (relABPhi A B))
      (by
        show dualZMapCompat R (cokernel (smallToSing A B)) (relChains M (A ∪ B : Set M)) (relABq A B)
            ≫ dualZMapCompat R (singularChains ℤ M) (cokernel (smallToSing A B))
                (cokernel.π (smallToSing A B))
          = dualZMapCompat R (singularChains ℤ M) (relChains M (A ∪ B : Set M))
                (cokernel.π (inclChains M (A ∪ B : Set M)))
            ≫ dualZMapCompat R (singularChains ℤ M) (singularChains ℤ M)
                (𝟙 (singularChains ℤ M))
        rw [← dualZMapCompat_comp, ← dualZMapCompat_comp]
        rw [show cokernel.π (smallToSing A B) ≫ relABq A B
            = 𝟙 (singularChains ℤ M) ≫ cokernel.π (inclChains M (A ∪ B : Set M)) from by
          rw [Category.id_comp]
          show cokernel.π (smallToSing A B) ≫ relABq A B
            = cokernel.π (inclChains M (A ∪ B : Set M))
          rw [show relABq A B = cokernel.desc (smallToSing A B)
              (cokernel.π (inclChains M (A ∪ B : Set M))) _ from rfl]
          rw [cokernel.π_desc]])
      (by
        show dualZMapCompat R (singularChains ℤ M) (singularChains ℤ M) (𝟙 (singularChains ℤ M))
            ≫ dualZMapCompat R (smallChains A B) (singularChains ℤ M) (smallToSing A B)
          = dualZMapCompat R (singularChains ℤ (TopCat.of (A ∪ B : Set M))) (singularChains ℤ M)
                (inclChains M (A ∪ B : Set M))
            ≫ dualZMapCompat R (smallChains A B) (singularChains ℤ (TopCat.of (A ∪ B : Set M)))
                (relABPhi A B)
        rw [← dualZMapCompat_comp, ← dualZMapCompat_comp]
        rw [Category.comp_id, relABPhi_comp_incl'])
  have hθ₂ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₂ m) := by
    intro m
    have h2 : θ.τ₂ = dualZMapCompat R (singularChains ℤ M) (singularChains ℤ M)
        (𝟙 (singularChains ℤ M)) := rfl
    rw [h2, dualZMapCompat_id]
    exact (HomologicalComplex.homologyMap_id (dualZCompat R (singularChains ℤ M)) m).symm ▸ IsIso.id _
  have hθ₃ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₃ m) := by
    intro m
    have h3 : θ.τ₃ = dualZMapCompat R (smallChains A B) (singularChains ℤ (TopCat.of (A ∪ B : Set M)))
        (relABPhi A B) := rfl
    rw [h3]
    exact relABPhi_dualZ_quasiIso R hA hB m
  have hθ₁ : ∀ m, IsIso (HomologicalComplex.homologyMap θ.τ₁ m) :=
    isIso_homologyMap_tau1 R θ hT₂ hT₁ hθ₂ hθ₃
  have hq : θ.τ₁ = dualZMapCompat R (cokernel (smallToSing A B)) (relChains M (A ∪ B))
      (relABq A B) := rfl
  rw [← hq]
  exact hθ₁ n


/-! ## The identification `C^*(X,A+B;R) ≅ Hom_ℤ(C_*(X)/(C_*(A)+C_*(B)), R)` -/

section E2

variable {M : TopCat} (A B : Set M)

lemma cokerSmall_ker (n : ℕ) :
    LinearMap.ker (((cokernel.π (smallToSing A B)).f n).hom)
      = LinearMap.range ((smallToSing A B).f n).hom := by
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallToSing A B) (cokernel.π (smallToSing A B)) (cokernel.condition _)
  have hex : S.Exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  have hd := (HomologicalComplex.exact_iff_degreewise_exact S).1 hex n
  have h := (ShortComplex.moduleCat_exact_iff
    (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n))).1 hd
  have hg : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g
      = (cokernel.π (smallToSing A B)).f n := by
    rw [ShortComplex.map_g]; rfl
  have hf : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f
      = (smallToSing A B).f n := by
    rw [ShortComplex.map_f]; rfl
  rw [hg, hf] at h
  refine le_antisymm ?_ ?_
  · rintro z hz
    exact h z hz
  · rintro z ⟨y, rfl⟩
    show ((cokernel.π (smallToSing A B)).f n) ((smallToSing A B).f n y) = 0
    have h3 : (0 : smallChains A B ⟶ cokernel (smallToSing A B)).f n
        = (smallToSing A B).f n ≫ (cokernel.π (smallToSing A B)).f n := by
      rw [← HomologicalComplex.comp_f, cokernel.condition]
    have h4 := congrArg (fun (k : (smallChains A B).X n ⟶
      (cokernel (smallToSing A B)).X n) => k y) h3
    exact h4.symm

lemma cokerSmall_comp_inclChainsA :
    inclChains M A ≫ cokernel.π (smallToSing A B) = 0 := by
  rw [← smallOfU_comp_smallToSing A B, Category.assoc, cokernel.condition]
  simp

lemma cokerSmall_comp_inclChainsB :
    inclChains M B ≫ cokernel.π (smallToSing A B) = 0 := by
  rw [← smallOfV_comp_smallToSing A B, Category.assoc, cokernel.condition]
  simp

set_option maxHeartbeats 4000000 in
/-- The degreewise map `Hom_ℤ(C_*(X)/(C_*(A)+C_*(B)), R) ⟶ C^n(X,A+B;R)`. -/
noncomputable def abZLM (R : Type) [CommRing R] (n : ℕ) :
    ((cokernel (smallToSing A B)).X n →ₗ[ℤ] R) →ₗ[R] (pdABCohR (R := R) M A B).X n :=
  (((cochCoeffEquiv R M n).toLinearMap).comp
    (LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom)).codRestrict
    (pdABKernR (R := R) M A B n) (by
      intro φ
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [relKern, LinearMap.mem_ker]
        show ((restr R M A).f n).hom
          (cochCoeffEquiv R M n (LinearMap.lcomp R R
            ((cokernel.π (smallToSing A B)).f n).hom φ)) = 0
        rw [restr_f_apply R M A n]
        rw [← cochCoeffEquiv_natural R (subtypeIncl M A) n
          (LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom φ)]
        have hz : (LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom φ).comp
            ((chainMap ℤ (TopCat.of A) M (subtypeIncl M A)).f n).hom = 0 := by
          rw [LinearMap.lcomp_apply', LinearMap.comp_assoc]
          have h0 : ((cokernel.π (smallToSing A B)).f n).hom.comp
              ((inclChains M A).f n).hom = 0 := by
            rw [← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
              cokerSmall_comp_inclChainsA, HomologicalComplex.zero_f, ModuleCat.hom_zero]
          rw [show ((chainMap ℤ (TopCat.of A) M (subtypeIncl M A)).f n).hom
              = ((inclChains M A).f n).hom from rfl, h0, LinearMap.comp_zero]
        rw [hz, map_zero]
      · rw [relKern, LinearMap.mem_ker]
        show ((restr R M B).f n).hom
          (cochCoeffEquiv R M n (LinearMap.lcomp R R
            ((cokernel.π (smallToSing A B)).f n).hom φ)) = 0
        rw [restr_f_apply R M B n]
        rw [← cochCoeffEquiv_natural R (subtypeIncl M B) n
          (LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom φ)]
        have hz : (LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom φ).comp
            ((chainMap ℤ (TopCat.of B) M (subtypeIncl M B)).f n).hom = 0 := by
          rw [LinearMap.lcomp_apply', LinearMap.comp_assoc]
          have h0 : ((cokernel.π (smallToSing A B)).f n).hom.comp
              ((inclChains M B).f n).hom = 0 := by
            rw [← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
              cokerSmall_comp_inclChainsB, HomologicalComplex.zero_f, ModuleCat.hom_zero]
          rw [show ((chainMap ℤ (TopCat.of B) M (subtypeIncl M B)).f n).hom
              = ((inclChains M B).f n).hom from rfl, h0, LinearMap.comp_zero]
        rw [hz, map_zero])


lemma abZLM_apply (R : Type) [CommRing R] (n : ℕ) (φ : (cokernel (smallToSing A B)).X n →ₗ[ℤ] R) :
    (abZLM (A := A) (B := B) (R := R) n φ).1
      = cochCoeffEquiv R M n (φ.comp ((cokernel.π (smallToSing A B)).f n).hom) := by
  show ((cochCoeffEquiv R M n).toLinearMap)
      (LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom φ)
    = cochCoeffEquiv R M n (φ.comp ((cokernel.π (smallToSing A B)).f n).hom)
  rw [LinearMap.lcomp_apply']
  rfl

lemma cokerSmall_surjective (n : ℕ) :
    Function.Surjective (((cokernel.π (smallToSing A B)).f n).hom) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

lemma abZLM_injective (R : Type) [CommRing R] (n : ℕ) :
    Function.Injective (abZLM (A := A) (B := B) (R := R) n) := by
  intro φ ψ h
  have h2 : cochCoeffEquiv R M n (φ.comp ((cokernel.π (smallToSing A B)).f n).hom)
      = cochCoeffEquiv R M n (ψ.comp ((cokernel.π (smallToSing A B)).f n).hom) := by
    have hh := congrArg Subtype.val h
    rwa [abZLM_apply, abZLM_apply] at hh
  have h3 : LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom φ
      = LinearMap.lcomp R R ((cokernel.π (smallToSing A B)).f n).hom ψ := by
    rw [LinearMap.lcomp_apply', LinearMap.lcomp_apply']
    exact (cochCoeffEquiv R M n).injective h2
  exact LinearMap.lcomp_injective_of_surjective (S := R) (N := R)
    ((cokernel.π (smallToSing A B)).f n).hom (cokerSmall_surjective A B n) h3

set_option maxHeartbeats 4000000 in
lemma abZLM_surjective (R : Type) [CommRing R] (n : ℕ) :
    Function.Surjective (abZLM (A := A) (B := B) (R := R) n) := by
  intro Θ
  have hΘA : ((restr R M A).f n).hom Θ.1 = 0 := by
    have := (Submodule.mem_inf.mp Θ.2).1
    rwa [relKern, LinearMap.mem_ker] at this
  have hΘB : ((restr R M B).f n).hom Θ.1 = 0 := by
    have := (Submodule.mem_inf.mp Θ.2).2
    rwa [relKern, LinearMap.mem_ker] at this
  set ψ : (singularChains ℤ M).X n →ₗ[ℤ] R := (cochCoeffEquiv R M n).symm Θ.1 with hψ
  have hΦψ : cochCoeffEquiv R M n ψ = Θ.1 := (cochCoeffEquiv R M n).apply_symm_apply Θ.1
  have hA : ψ.comp ((inclChains M A).f n).hom = 0 := by
    apply (cochCoeffEquiv R (TopCat.of A) n).injective
    rw [map_zero, cochCoeffEquiv_natural R (subtypeIncl M A) n ψ, hΦψ]
    rw [← restr_f_apply R M A n]
    exact hΘA
  have hB : ψ.comp ((inclChains M B).f n).hom = 0 := by
    apply (cochCoeffEquiv R (TopCat.of B) n).injective
    rw [map_zero, cochCoeffEquiv_natural R (subtypeIncl M B) n ψ, hΦψ]
    rw [← restr_f_apply R M B n]
    exact hΘB
  have hker : LinearMap.range ((smallToSing A B).f n).hom ≤ LinearMap.ker ψ := by
    change smallChainSubmodule A B n ≤ LinearMap.ker ψ
    rw [smallChainSubmodule_eq_sup A B n]
    exact sup_le ((LinearMap.range_le_ker_iff).2 hA) ((LinearMap.range_le_ker_iff).2 hB)
  have hzero : ψ.comp ((smallToSing A B).f n).hom = 0 :=
    (LinearMap.range_le_ker_iff).1 hker
  have hexact : Function.Exact ⇑((smallToSing A B).f n).hom
      ⇑((cokernel.π (smallToSing A B)).f n).hom :=
    (LinearMap.exact_iff).mpr (cokerSmall_ker A B n)
  have hmem : ψ ∈ Set.range (⇑(LinearMap.lcomp ℤ R ((cokernel.π (smallToSing A B)).f n).hom)) :=
    (LinearMap.exact_lcomp_of_exact_of_surjective (N := R) hexact
      (cokerSmall_surjective A B n) ψ).1 (by
        rw [LinearMap.lcomp_apply']
        exact hzero)
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨φ, ?_⟩
  apply Subtype.ext
  rw [abZLM_apply, ← LinearMap.lcomp_apply' (S := ℤ) (N := R)
    ((cokernel.π (smallToSing A B)).f n).hom φ, hφ, hΦψ]

end E2
end
end Work.Whitney
