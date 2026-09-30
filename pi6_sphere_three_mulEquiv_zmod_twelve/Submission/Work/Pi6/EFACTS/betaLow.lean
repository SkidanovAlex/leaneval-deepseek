import Mathlib
import Submission.Work.Pi6.EFACTS.Z.WangThetaLow
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.EFACTS

/-- Transport of `homologyMap` along an equality of degrees: the degree cast is natural. -/
lemma homologyMap_cast_comm {R : Type} [CommRing R] {C D : CochainComplex (ModuleCat R) ℕ}
    (φ : C ⟶ D) {i j : ℕ} (h : i = j) :
    HomologicalComplex.homologyMap φ i ≫ (eqToIso (congrArg (fun t => D.homology t) h)).hom
      = (eqToIso (congrArg (fun t => C.homology t) h)).hom ≫ HomologicalComplex.homologyMap φ j := by
  subst h
  simp [eqToIso_refl]

theorem betaLow (b : ℕ) (hb : 2 ≤ b) (X : TopCat) (A : Set X) (Fsp : TopCat)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp)
    (τS : (Work.Cohomology.relComplex ℤ X A).homology ((b - 1) + 1) ≅
      Work.Cohomology.singularCohomology ℤ 0 Fsp) :
    ∃ β : Work.Cohomology.singularCohomology ℤ 0 Fsp ⟶ Work.Cohomology.singularCohomology ℤ b X,
      Function.Exact (Work.StemsB.wangCohThetaLowR ℤ X A Fsp b γ τS) β ∧
      Function.Exact β (Work.StemsB.wangCohShiftα X A Fsp b γ b) := by
  have hb1 : 1 ≤ b := by omega
  have h : (b - 1) + 1 = b := Nat.sub_add_cancel hb1
  let eX : (Work.Cohomology.singularCochainComplex ℤ X).homology ((b - 1) + 1) ≅
      (Work.Cohomology.singularCochainComplex ℤ X).homology b :=
    eqToIso (congrArg (fun t => (Work.Cohomology.singularCochainComplex ℤ X).homology t) h)
  let eA : (Work.Cohomology.relComplex ℤ X A).homology b ≅
      Work.Cohomology.singularCohomology ℤ 0 Fsp :=
    (eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℤ X A).homology t) h)).symm ≪≫ τS
  have heAinv : eA.inv = τS.inv ≫
      (eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℤ X A).homology t) h)).hom := by
    simp only [eA, Iso.trans_inv, Iso.symm_inv]
  have hβ : (τS.inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) ((b - 1) + 1)
        ≫ eX.hom)
      = (eA.inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) b) := by
    have hnat := homologyMap_cast_comm (R := ℤ) (C := Work.Cohomology.relComplex ℤ X A)
      (D := Work.Cohomology.singularCochainComplex ℤ X) (Work.Cohomology.relIncl ℤ X A) h
    rw [heAinv, hnat, Category.assoc]
  refine ⟨τS.inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) ((b - 1) + 1)
    ≫ eX.hom, ?_, ?_⟩
  · have hE1 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.Cohomology.pair_exact₁ ℤ X A (b - 1))
    have hconj := Work.StemsB.functionExact_conj_R ℤ (Work.Cohomology.pairδ ℤ X A (b - 1))
      (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) ((b - 1) + 1))
      (γ (b - 1)) τS eX hE1
    exact hconj
  · have hE2 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Work.Cohomology.pair_exact₂ ℤ X A b)
    have hconj := Work.StemsB.functionExact_conj_R ℤ
      (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) b)
      (HomologicalComplex.homologyMap (Work.Cohomology.restr ℤ X A) b)
      eA (Iso.refl ((Work.Cohomology.singularCochainComplex ℤ X).homology b)) (γ b) hE2
    have hc1 : (eA.inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) b
        ≫ (Iso.refl ((Work.Cohomology.singularCochainComplex ℤ X).homology b)).hom)
        = (eA.inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) b) := by
      rw [Iso.refl_hom, Category.comp_id]
    have hc2 : ((Iso.refl ((Work.Cohomology.singularCochainComplex ℤ X).homology b)).inv
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.restr ℤ X A) b ≫ (γ b).hom)
        = Work.StemsB.wangCohShiftα X A Fsp b γ b := by
      rw [Iso.refl_inv, Category.id_comp]
      rfl
    rw [hc1, hc2] at hconj
    rw [hβ]
    exact hconj

end Work.Pi6.EFACTS
