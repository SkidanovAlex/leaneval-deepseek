import Mathlib
import Submission.Work.Whitney.RelRelCupNat
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Serre

open CategoryTheory

noncomputable section

variable {R : Type} [CommRing R]

/-! ## The projection of the `A+B` complex onto its `B`-part -/

/-- The degreewise projection `C^n(X,A) ∩ C^n(X,B) → C^n(X,B)` (the second projection of the
intersection). -/
def pdABProjBLM (X : TopCat) (A B : Set X) (n : ℕ) :
    (Work.Whitney.pdABKernR (R := R) X A B n) →ₗ[R] Work.Cohomology.relKern R X B n where
  toFun x := ⟨x.1, (Submodule.mem_inf.mp (by
    rw [show Work.Cohomology.relKern R X A n ⊓ Work.Cohomology.relKern R X B n
        = Work.Whitney.pdABKernR (R := R) X A B n from rfl]
    exact x.2)).2⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

/-- The underlying cochain of the projection is the cochain itself. -/
@[simp] lemma pdABProjBLM_coe (X : TopCat) (A B : Set X) (n : ℕ)
    (x : (Work.Whitney.pdABKernR (R := R) X A B n)) :
    (pdABProjBLM (R := R) X A B n x).1 = x.1 := rfl

/-- **The projection of the `A+B` cochain complex onto the relative cochain complex of `B`**: a
cochain vanishing on `A` and on `B` is sent to itself, viewed as a cochain vanishing on `B`. -/
def pdABProjB (X : TopCat) (A B : Set X) :
    Work.Whitney.pdABCohR (R := R) X A B ⟶ Work.Cohomology.relComplex R X B :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (pdABProjBLM (R := R) X A B n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro _x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        Work.Whitney.pdABCohR_d, Work.Cohomology.relComplex_d]
      rfl)

@[simp] lemma pdABProjB_f (X : TopCat) (A B : Set X) (n : ℕ) :
    (pdABProjB (R := R) X A B).f n = ModuleCat.ofHom (pdABProjBLM (R := R) X A B n) := rfl

@[simp] lemma pdABProjB_f_apply (X : TopCat) (A B : Set X) (n : ℕ)
    (x : (Work.Whitney.pdABCohR (R := R) X A B).X n) :
    (pdABProjB (R := R) X A B).f n x = pdABProjBLM (R := R) X A B n x := rfl

/-- The pair map `C^*(X,B) → C^*(X,A∪B)` induced by the identity leaves the underlying cochain
unchanged. -/
lemma relComplexMap_id_coeB (X : TopCat) (A B : Set X)
    (hh : ∀ x ∈ B, (TopCat.ofHom (ContinuousMap.id X)) x ∈ A ∪ B) (n : ℕ)
    (x : (Work.Cohomology.relComplex R X (A ∪ B)).X n) :
    ((ModuleCat.Hom.hom
      ((Work.Cohomology.relComplexMap (X₁ := X) (X₂ := X) R B (A ∪ B)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n)) x).1 = x.1 := by
  have key : (Work.Cohomology.relComplexMap (X₁ := X) (X₂ := X) R B (A ∪ B)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n
      = ModuleCat.ofHom (Work.Cohomology.relMapLM R B (A ∪ B)
          (TopCat.ofHom (ContinuousMap.id X)) hh n) :=
    Work.Cohomology.relComplexMap_f ..
  have h1 : ModuleCat.Hom.hom ((Work.Cohomology.relComplexMap (X₁ := X) (X₂ := X) R B (A ∪ B)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n)
      = Work.Cohomology.relMapLM R B (A ∪ B) (TopCat.ofHom (ContinuousMap.id X)) hh n :=
    (congrArg ModuleCat.Hom.hom key).trans (ModuleCat.hom_ofHom _)
  rw [h1]
  exact (Work.Cohomology.relMapLM_coe R B (A ∪ B) (TopCat.ofHom (ContinuousMap.id X)) hh n x).trans
    (by rw [TopCat.ofHom_id, Work.Cohomology.dualChainMap_id, HomologicalComplex.id_f,
      ModuleCat.hom_id, LinearMap.id_apply])

/-- **The pair map `C^*(X,B) → C^*(X,A∪B)` is the composite of the inclusion of `C^*(X,A∪B)` into
the `A+B` complex and the projection of the `A+B` complex onto `C^*(X,B)`.** -/
theorem pdABInclRelR_comp_pdABProjB (X : TopCat) (A B : Set X) :
    Work.Whitney.pdABInclRelR (R := R) X A B ≫ pdABProjB (R := R) X A B
      = Work.Cohomology.relComplexMap (X₁ := X) (X₂ := X) R B (A ∪ B)
          (TopCat.ofHom (ContinuousMap.id X)) (fun x hx => Or.inr hx) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (relComplexMap_id_coeB (R := R) X A B (fun x hx => Or.inr hx) n x).symm

/-- **A morphism of cochain complexes sends the homology class of the cycle associated with a
cocycle to the homology class of the cycle associated with the image cocycle.** -/
lemma homologyMap_homologypi_cocycleOfK {K L : CochainComplex (ModuleCat R) ℕ} (φ : K ⟶ L)
    {n : ℕ} (γ : (K.X n)) (hγ : ((K.d n (n + 1)).hom) γ = 0)
    (hγ' : ((L.d n (n + 1)).hom) ((φ.f n).hom γ) = 0) :
    (HomologicalComplex.homologyMap φ n).hom
        ((K.homologyπ n).hom (Work.Cohomology.cocycleOfK K γ hγ))
      = (L.homologyπ n).hom (Work.Cohomology.cocycleOfK L ((φ.f n).hom γ) hγ') := by
  rw [Work.Cohomology.homologyMap_homologyπ (R := R) φ n (Work.Cohomology.cocycleOfK K γ hγ)]
  refine congrArg (fun z => (L.homologyπ n).hom z) ?_
  apply Work.Cohomology.iCycles_injective_K L n
  rw [Work.Whitney.cyclesMap_i_apply_gen φ n (Work.Cohomology.cocycleOfK K γ hγ),
    Work.Cohomology.iCycles_cocycleOfK K γ hγ,
    Work.Cohomology.iCycles_cocycleOfK L ((φ.f n).hom γ) hγ']

/-- **The two-relative cup product forgets to the mixed cup product.** -/
theorem relRelCupOpen_mixedCup {R : Type} [CommRing R] {X : Type} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (x : Work.Thom.RelCoh R m X A) (y : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relCohMap (ContinuousMap.id X) B (A ∪ B) (fun z hz => Or.inr hz) R (m + n)).hom
        (Work.Whitney.relRelCupOpen A B hA hB m n x y)
      = Work.Thom.mixedCupC R B m n ((Work.Thom.relToAbs R A m).hom x) y := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_relClassOf R (TopCat.of X) A m x
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_relClassOf R (TopCat.of X) B n y
  have hα' : ((Work.Cohomology.relComplex R (TopCat.of X) A).d m (m + 1)).hom α = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]; exact hα
  have hβ' : ((Work.Cohomology.relComplex R (TopCat.of X) B).d n (n + 1)).hom β = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]; exact hβ
  have hstar : ((Work.Whitney.pdABCohR (R := R) (TopCat.of X) A B).d (m + n) (m + n + 1)).hom
      (Work.Whitney.starAB (R := R) (TopCat.of X) A B m n α β) = 0 :=
    Work.Whitney.ThreeCup.star3_cocycle_cochain (Work.Whitney.Leibniz3_starAB (TopCat.of X) A B)
      m n α β hα' hβ'
  -- the value of the relative-relative cup, through the canonical transport
  have hcup : Work.Whitney.relRelCupOpen A B hA hB m n
        (Work.Cohomology.relClassOf R (TopCat.of X) A α hα)
        (Work.Cohomology.relClassOf R (TopCat.of X) B β hβ)
      = Work.Whitney.pdABInvTransport A B hA hB (m + n)
          (((Work.Whitney.pdABCohR (R := R) (TopCat.of X) A B).homologyπ (m + n)).hom
            (Work.Cohomology.cocycleOfK (Work.Whitney.pdABCohR (R := R) (TopCat.of X) A B)
              (Work.Whitney.starAB (R := R) (TopCat.of X) A B m n α β) hstar)) := by
    rw [Work.Whitney.relRelCupOpen_apply, Work.Whitney.relRelCupG_apply,
      Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) A α hα hα',
      Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) B β hβ hβ',
      Work.Whitney.relRelCupHMap_apply (TopCat.of X) A B m n α β hα' hβ' hstar]
  rw [hcup]
  -- the pair map `(X,B) → (X,A∪B)` factors through the `A+B` complex
  have hcomp : (Work.Thom.relCohMap (ContinuousMap.id X) B (A ∪ B) (fun z hz => Or.inr hz)
        R (m + n))
      = HomologicalComplex.homologyMap (Work.Whitney.pdABInclRelR (R := R) (TopCat.of X) A B)
          (m + n)
        ≫ HomologicalComplex.homologyMap (pdABProjB (R := R) (TopCat.of X) A B) (m + n) := by
    rw [show Work.Thom.relCohMap (ContinuousMap.id X) B (A ∪ B) (fun z hz => Or.inr hz)
          R (m + n)
        = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
            (X₂ := TopCat.of X) R B (A ∪ B) (TopCat.ofHom (ContinuousMap.id X))
            (fun z hz => Or.inr hz)) (m + n) from rfl,
      ← pdABInclRelR_comp_pdABProjB (R := R) (TopCat.of X) A B,
      HomologicalComplex.homologyMap_comp]
  rw [hcomp, ModuleCat.hom_comp, LinearMap.comp_apply,
    Work.Whitney.pdABInvTransport_gauge A B hA hB (m + n)]
  -- the projection of the Alexander–Whitney product, and the mixed cup
  have hprojcoc : ((Work.Cohomology.relComplex R (TopCat.of X) B).d (m + n) (m + n + 1)).hom
      ((pdABProjB (R := R) (TopCat.of X) A B).f (m + n)
        (Work.Whitney.starAB (R := R) (TopCat.of X) A B m n α β)) = 0 := by
    have hcomm := HomologicalComplex.Hom.comm (pdABProjB (R := R) (TopCat.of X) A B)
      (m + n) (m + n + 1)
    have h2 := congrArg (fun (g : (Work.Whitney.pdABCohR (R := R) (TopCat.of X) A B).X (m + n) ⟶
        (Work.Cohomology.relComplex R (TopCat.of X) B).X (m + n + 1)) =>
          g.hom (Work.Whitney.starAB (R := R) (TopCat.of X) A B m n α β)) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [hstar, map_zero] at h2
    exact h2
  rw [homologyMap_homologypi_cocycleOfK (R := R)
    (φ := pdABProjB (R := R) (TopCat.of X) A B)
    (γ := Work.Whitney.starAB (R := R) (TopCat.of X) A B m n α β) hstar hprojcoc]
  -- the right-hand side
  have hrel : (Work.Thom.relToAbs R A m).hom (Work.Cohomology.relClassOf R (TopCat.of X) A α hα)
      = Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of X)) α.1
          (Work.Cohomology.relClassOf_cochainDiff R (TopCat.of X) A α hα) :=
    Work.Cohomology.relIncl_homologyMap_relClassOf R (TopCat.of X) A α hα
  rw [hrel]
  obtain ⟨hmem, hdif, hmixeq⟩ := Classical.choose_spec
    (Work.Cohomology.mixedRelCupH R (TopCat.of X) B) m n α.1 β
    (Work.Cohomology.relClassOf_cochainDiff R (TopCat.of X) A α hα) hβ
  rw [hmixeq]
  have hdif' : ((Work.Cohomology.relComplex R (TopCat.of X) B).d (m + n) (m + n + 1)).hom
      (⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X)) α.1 β.1, hmem⟩ :
        Work.Cohomology.relKern R (TopCat.of X) B (m + n)) = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]; exact hdif
  rw [Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) B
    ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X)) α.1 β.1, hmem⟩ hdif hdif']
  refine Work.Whitney.homologyπ_cocycleOfK_congr (Work.Cohomology.relComplex R (TopCat.of X) B)
    ?_ hprojcoc hdif'
  apply Subtype.ext
  rw [pdABProjB_f_apply, pdABProjBLM_coe, Work.Whitney.starAB_coe]

end

end Work.Serre
