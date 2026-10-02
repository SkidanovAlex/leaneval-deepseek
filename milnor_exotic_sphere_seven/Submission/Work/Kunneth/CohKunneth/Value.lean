import Mathlib
import Submission.Work.Kunneth.CohKunneth.UCTStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology (dualComplex dualComplexMap Cochain cochainDiff cohomologyClassOf
  cohomologyClassOf_congr uctDual_evaluation)

/-- **The Künneth isomorphism in cohomology, with its value rule on the cross product.** -/
theorem kunnethCoh_value_aux (X Y : SSet) (n : ℕ)
    (hYproj : ∀ q, Module.Projective ℤ ↥((sChain Y).X q))
    (hYfree : ∀ q, Module.Free ℤ ↥((sChain Y).homology q))
    (hYfin : ∀ q, Module.Finite ℤ ↥((sChain Y).homology q)) :
    ∃ e : ((Work.Cohomology.dualComplex ℤ
          (Work.Kunneth.sChain (Work.Kunneth.sProd X Y))).homology n)
        ≅ Work.Kunneth.kunnethTarget X Y n,
      ∀ (p q : ℕ) (hpq : p + q = n)
        (a : ↥((Work.Cohomology.cochainC ℤ X).homology p))
        (b : ↥((Work.Cohomology.cochainC ℤ Y).homology q)),
        e.hom.hom (CategoryTheory.eqToHom (congrArg (fun k => (Work.Cohomology.dualComplex ℤ
            (Work.Kunneth.sChain (Work.Kunneth.sProd X Y))).homology k) hpq)
          (Work.Kunneth.crossH X Y p q a b))
          ⟨(p, q), hpq⟩ = a ⊗ₜ[ℤ] b := by
  classical
  haveI hYfreeI : ∀ q, Module.Free ℤ ↥((sChain Y).homology q) := hYfree
  haveI hYfinI : ∀ q, Module.Finite ℤ ↥((sChain Y).homology q) := hYfin
  -- the transparent splitting of the second factor onto its homology
  have hYp : ∀ q, Module.Projective ℤ ↥((sChain Y).homology q) := fun q => by
    haveI := hYfree q
    exact Module.Projective.of_free
  obtain ⟨π, ι, hιπ, hHne, hπval⟩ := exists_splitting_transparent (sChain Y) hYproj hYp
  have hH : Homotopy (π ≫ ι) (𝟙 (sChain Y)) := hHne.some
  -- the flat computation of `H^*(ctens · T)`
  have hT : ∀ q, Module.Flat ℤ ↥(homDual (fun q => (sChain Y).homology q) q) := fun q => by
    haveI : Module.Free ℤ ↥(homDual (fun q => (sChain Y).homology q) q) :=
      Module.Free.of_basis (Module.finBasis ℤ ↥((sChain Y).homology q)).dualBasis
    exact Module.Flat.of_free
  obtain ⟨eC, heC⟩ := ctensHomologyValue (dualComplex ℤ (sChain X))
    (homDual (fun q => (sChain Y).homology q)) hT n
  -- the dual universal coefficient isomorphisms
  let uctIso : (q : ℕ) → ((dualComplex ℤ (sChain Y)).homology q ≅
      ModuleCat.of ℤ (↥((sChain Y).homology q) →ₗ[ℤ] ℤ)) :=
    fun q => Classical.choose (uctDual_evaluation (sChain Y) hYproj hYfree q)
  have uctIso_spec : ∀ (q : ℕ) (z : ↥((dualComplex ℤ (sChain Y)).cycles q))
      (c : ↥((sChain Y).cycles q)),
      (uctIso q).hom.hom (((dualComplex ℤ (sChain Y)).homologyπ q).hom z)
        (((sChain Y).homologyπ q).hom c)
        = Work.Cohomology.dval (sChain Y) q
            (((dualComplex ℤ (sChain Y)).iCycles q).hom z) (((sChain Y).iCycles q).hom c) :=
    fun q z c => Classical.choose_spec (uctDual_evaluation (sChain Y) hYproj hYfree q) z c
  -- the pieces of the isomorphism
  let eEZ := ezDualIso X Y n
  let eHS := homSumIso (C := sChain X) (D := sChain Y)
    (M := fun q => (sChain Y).homology q) π ι hιπ hH n
  let eCT := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
    (ctensComplexIso (C := sChain X) (M := fun q => (sChain Y).homology q))
  let eUCT : ctensH (dualComplex ℤ (sChain X))
      (homDual (fun q => (sChain Y).homology q)) n ≅ kunnethTarget X Y n :=
    (LinearEquiv.piCongrRight (fun pq : tpIdx n => TensorProduct.congr
      (Iso.toLinearEquiv (Iso.refl ((dualComplex ℤ (sChain X)).homology pq.1.1)))
      (Iso.toLinearEquiv (uctIso pq.1.2).symm))).toModuleIso
  refine ⟨eEZ ≪≫ eHS ≪≫ eCT ≪≫ eC ≪≫ eUCT, ?_⟩
  intro p q hpq a b
  subst hpq
  -- representatives of the classes and their cocycles
  obtain ⟨za, hza⟩ := (ModuleCat.epi_iff_surjective
    ((dualComplex ℤ (sChain X)).homologyπ p)).mp inferInstance a
  obtain ⟨zb, hzb⟩ := (ModuleCat.epi_iff_surjective
    ((dualComplex ℤ (sChain Y)).homologyπ q)).mp inferInstance b
  set α : Cochain ℤ X p := ((dualComplex ℤ (sChain X)).iCycles p).hom za with hαdef
  set β : Cochain ℤ Y q := ((dualComplex ℤ (sChain Y)).iCycles q).hom zb with hβdef
  have hαd : ((dualComplex ℤ (sChain X)).d p (p + 1)).hom α = 0 := by
    have hmem := ((kcCycIso (dualComplex ℤ (sChain X)) p).hom za).2
    have h0 := LinearMap.mem_ker.mp hmem
    rwa [kcCycIso_hom_val] at h0
  have hβd : ((dualComplex ℤ (sChain Y)).d q (q + 1)).hom β = 0 := by
    have hmem := ((kcCycIso (dualComplex ℤ (sChain Y)) q).hom zb).2
    have h0 := LinearMap.mem_ker.mp hmem
    rwa [kcCycIso_hom_val] at h0
  have hα : cochainDiff ℤ X α = 0 := by
    rw [cochainDiff_eq_dualComplex_d]; exact hαd
  have hβ : cochainDiff ℤ Y β = 0 := by
    rw [cochainDiff_eq_dualComplex_d]; exact hβd
  have hα'' : cochainDiff ℤ X ((dualComplex ℤ (sChain X)).iCycles p za) = 0 := by
    rw [← hαdef]; exact hα
  have hβ'' : cochainDiff ℤ Y ((dualComplex ℤ (sChain Y)).iCycles q zb) = 0 := by
    rw [← hβdef]; exact hβ
  have hclassA : cohomologyClassOf ℤ X α hα = a :=
    (cohomologyClassOf_congr ℤ X hαdef hα hα'').trans
      ((cohomologyClassOf_eq_homologyπ_dual X p za hα'').trans hza)
  have hclassB : cohomologyClassOf ℤ Y β hβ = b :=
    (cohomologyClassOf_congr ℤ Y hβdef hβ hβ'').trans
      ((cohomologyClassOf_eq_homologyπ_dual Y q zb hβ'').trans hzb)
  have hclassA'' : ((dualComplex ℤ (sChain X)).homologyπ p).hom za
      = cohomologyClassOf ℤ X α hα :=
    (cohomologyClassOf_eq_homologyπ_dual X p za hα'').symm.trans
      (cohomologyClassOf_congr ℤ X hαdef hα hα'').symm
  have hclassB'' : ((dualComplex ℤ (sChain Y)).homologyπ q).hom zb
      = cohomologyClassOf ℤ Y β hβ :=
    (cohomologyClassOf_eq_homologyπ_dual Y q zb hβ'').symm.trans
      (cohomologyClassOf_congr ℤ Y hβdef hβ hβ'').symm
  rw [← hclassA, ← hclassB]
  -- the first step: Eilenberg–Zilber
  set TC : ↥((dualComplex ℤ (tChain X Y)).X (p + q)) :=
    tensorCochain (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β with hTC
  set zT : ↥((dualComplex ℤ (tChain X Y)).cycles (p + q)) :=
    cocycleCyc (dualComplex ℤ (tChain X Y)) (p + q) TC
      (tensorCochain_isCocycle (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β hαd hβd)
    with hzT
  have hstep1 : eEZ.hom.hom (crossH X Y p q (cohomologyClassOf ℤ X α hα)
        (cohomologyClassOf ℤ Y β hβ))
      = ((dualComplex ℤ (tChain X Y)).homologyπ (p + q)).hom zT :=
    ezDualIso_crossH X Y p q α β hα hβ
  -- the second step: replacing the second factor by its homology
  set z2 : ↥((dualComplex ℤ (tpC (sChain X)
      (sumShift (fun q => (sChain Y).homology q)))).cycles (p + q)) :=
    (HomologicalComplex.cyclesMap (homSumDualMap (C := sChain X) (D := sChain Y) ι)
      (p + q)).hom zT with hz2
  have hstep2 : eHS.hom.hom (eEZ.hom.hom (crossH X Y p q (cohomologyClassOf ℤ X α hα)
        (cohomologyClassOf ℤ Y β hβ)))
      = ((dualComplex ℤ (tpC (sChain X)
          (sumShift (fun q => (sChain Y).homology q)))).homologyπ (p + q)).hom z2 := by
    rw [hstep1]
    exact cochHomologyMap_apply_homologyπ (dualComplex ℤ (tpC (sChain X) (sChain Y)))
      (dualComplex ℤ (tpC (sChain X) (sumShift (fun q => (sChain Y).homology q))))
      (homSumDualMap (C := sChain X) (D := sChain Y) ι) (p + q) zT
  -- the third step: the hom–tensor adjunction
  set z3 : ↥((ctens (dualComplex ℤ (sChain X))
      (homDual (fun q => (sChain Y).homology q))).cycles (p + q)) :=
    (HomologicalComplex.cyclesMap (ctensComplexIso (C := sChain X)
      (M := fun q => (sChain Y).homology q)).hom (p + q)).hom z2 with hz3
  have hstep3 : eCT.hom.hom (eHS.hom.hom (eEZ.hom.hom (crossH X Y p q
        (cohomologyClassOf ℤ X α hα) (cohomologyClassOf ℤ Y β hβ))))
      = ((ctens (dualComplex ℤ (sChain X))
          (homDual (fun q => (sChain Y).homology q))).homologyπ (p + q)).hom z3 := by
    rw [hstep2]
    exact cochHomologyMap_apply_homologyπ _ _ _ (p + q) z2
  -- the value of the adjunction step on the `(p,q)`-component
  set φ : ↥((sChain Y).homology q) →ₗ[ℤ] ℤ :=
    (show ↥((sChain Y).X q) →ₗ[ℤ] ℤ from
      ((dualComplex ℤ (sChain Y)).iCycles q).hom zb).comp (ι.f q).hom with hφdef
  have hγ' : ∀ (u : ↥((sChain X).X p)) (h : ↥((sChain Y).homology q)),
      (show tpX (sChain X) (sumShift (fun q => (sChain Y).homology q)) (p + q) →ₗ[ℤ] ℤ
        from ((homSumDualMap (C := sChain X) (D := sChain Y) ι).f (p + q)).hom TC)
        (tpLof (sChain X) (sumShift (fun q => (sChain Y).homology q)) (p + q)
          ⟨(p, q), rfl⟩ (u ⊗ₜ[ℤ] h)) = α u * φ h := by
    intro u h
    rw [hφdef]
    exact homSumDualMap_value (C := sChain X) (D := sChain Y) ι p q α
      (((dualComplex ℤ (sChain Y)).iCycles q).hom zb) u h
  have hctensVal : (tpDualEquiv (sChain X) (fun q => (sChain Y).homology q) (p + q)
        (show tpX (sChain X) (sumShift (fun q => (sChain Y).homology q)) (p + q) →ₗ[ℤ] ℤ
          from ((homSumDualMap (C := sChain X) (D := sChain Y) ι).f (p + q)).hom TC))
        ⟨(p, q), rfl⟩ = α ⊗ₜ[ℤ] φ :=
    tpDualEquiv_component_value (C := sChain X) (M := fun q => (sChain Y).homology q)
      (p + q) ⟨(p, q), rfl⟩ α φ _ hγ'
  have hcomp : (show ctensX (dualComplex ℤ (sChain X))
        (homDual (fun q => (sChain Y).homology q)) (p + q) from
      ((ctens (dualComplex ℤ (sChain X))
        (homDual (fun q => (sChain Y).homology q))).iCycles (p + q)).hom z3) ⟨(p, q), rfl⟩
      = α ⊗ₜ[ℤ] φ := by
    rw [hz3, coch_iCycles_cyclesMap, hz2, coch_iCycles_cyclesMap, hzT, iCycles_cocycleCyc,
      hTC, ctensComplexIso_f_apply]
    exact hctensVal
  -- the fourth step: the flat computation of `H^*(ctens · T)`
  have hstep4 : (eC.hom.hom (eCT.hom.hom (eHS.hom.hom (eEZ.hom.hom (crossH X Y p q
        (cohomologyClassOf ℤ X α hα) (cohomologyClassOf ℤ Y β hβ)))))) ⟨(p, q), rfl⟩
      = ((dualComplex ℤ (sChain X)).homologyπ p).hom za ⊗ₜ[ℤ] φ := by
    rw [hstep3]
    exact heC z3 ⟨(p, q), rfl⟩ za φ hcomp
  -- the fifth step: the dual universal coefficient theorem
  have huct : (uctIso q).symm.toLinearEquiv φ = cohomologyClassOf ℤ Y β hβ := by
    rw [← hclassB'']
    exact uctSymm_apply (sChain Y) π ι hιπ hπval q zb (uctIso q) (uctIso_spec q)
  have hfinal : (eUCT.hom.hom (eC.hom.hom (eCT.hom.hom (eHS.hom.hom
        (eEZ.hom.hom (crossH X Y p q (cohomologyClassOf ℤ X α hα)
          (cohomologyClassOf ℤ Y β hβ))))))) ⟨(p, q), rfl⟩
      = cohomologyClassOf ℤ X α hα ⊗ₜ[ℤ] cohomologyClassOf ℤ Y β hβ := by
    rw [show (eUCT.hom.hom (eC.hom.hom (eCT.hom.hom (eHS.hom.hom
            (eEZ.hom.hom (crossH X Y p q (cohomologyClassOf ℤ X α hα)
              (cohomologyClassOf ℤ Y β hβ))))))) ⟨(p, q), rfl⟩
          = (TensorProduct.congr
              (Iso.toLinearEquiv (Iso.refl ((dualComplex ℤ (sChain X)).homology p)))
              (Iso.toLinearEquiv (uctIso q).symm))
              ((eC.hom.hom (eCT.hom.hom (eHS.hom.hom (eEZ.hom.hom (crossH X Y p q
                (cohomologyClassOf ℤ X α hα) (cohomologyClassOf ℤ Y β hβ))))))
                ⟨(p, q), rfl⟩) from rfl]
    rw [hstep4, TensorProduct.congr_tmul]
    have hrefl : Iso.toLinearEquiv (Iso.refl ((dualComplex ℤ (sChain X)).homology p))
        = LinearEquiv.refl ℤ ↥((dualComplex ℤ (sChain X)).homology p) := rfl
    rw [hrefl, LinearEquiv.refl_apply, huct, hclassA'']
  have hcomp_unfold : ∀ (x : ↥((Work.Cohomology.dualComplex ℤ
      (Work.Kunneth.sChain (Work.Kunneth.sProd X Y))).homology (p + q))),
      (eEZ ≪≫ eHS ≪≫ eCT ≪≫ eC ≪≫ eUCT).hom.hom x
        = eUCT.hom.hom (eC.hom.hom (eCT.hom.hom (eHS.hom.hom (eEZ.hom.hom x)))) := by
    intro x
    simp only [CategoryTheory.Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  rw [hcomp_unfold]
  rw [show (CategoryTheory.eqToHom (congrArg (fun k => ((Work.Cohomology.dualComplex ℤ
      (Work.Kunneth.sChain (Work.Kunneth.sProd X Y))).homology) k) rfl)
        (crossH X Y p q (cohomologyClassOf ℤ X α hα) (cohomologyClassOf ℤ Y β hβ)))
      = crossH X Y p q (cohomologyClassOf ℤ X α hα) (cohomologyClassOf ℤ Y β hβ) from rfl]
  exact hfinal

end

end Work.Kunneth
