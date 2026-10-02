import Mathlib
import Submission.Work.Cohomology.Endgame.transgressionIso
import Submission.Work.Cohomology.Endgame.overlapCap
import Submission.Work.Cohomology.Endgame.capCompare
import Submission.Work.Cohomology.Endgame.dshDelta
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.relMV_quasiIso
import Submission.Work.Cohomology.Endgame.relMVUVQuasiIso
import Submission.Work.Cohomology.Crux.cruxDelta7_isIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

namespace InternalTransgression

variable {X : TopCat}

/-! ## Elementary API -/

/-- Naturality of `homologyπ`. -/
theorem homologyMap_homologyπ_apply' {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat ℤ) cs} (φ : K ⟶ L) (i : ι)
    (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) := by
  have h := HomologicalComplex.homologyπ_naturality φ i
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- Elementwise form of `cyclesMap_i`. -/
theorem cyclesMap_i_apply' {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat ℤ) cs} (φ : K ⟶ L) (i : ι)
    (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) := by
  have h := congrArg (fun (m : K.cycles i ⟶ L.X i) => (ModuleCat.Hom.hom m) z)
    (HomologicalComplex.cyclesMap_i φ i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The two halves of an isomorphism are inverse. -/
theorem iso_hom_inv_apply {A B : ModuleCat ℤ} (e : A ≅ B) (x : B) :
    (ConcreteCategory.hom e.hom) ((ConcreteCategory.hom e.inv) x) = x := by
  have h : e.inv ≫ e.hom = 𝟙 B := Iso.inv_hom_id e
  have h2 := congrArg (fun (g : B ⟶ B) => (ModuleCat.Hom.hom g) x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h2

theorem iso_inv_hom_apply {A B : ModuleCat ℤ} (e : A ≅ B) (x : A) :
    (ConcreteCategory.hom e.inv) ((ConcreteCategory.hom e.hom) x) = x := by
  have h : e.hom ≫ e.inv = 𝟙 A := Iso.hom_inv_id e
  have h2 := congrArg (fun (g : A ⟶ A) => (ModuleCat.Hom.hom g) x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h2

/-- The forward direction of the `dsh` isomorphism on homology classes. -/
theorem dshHomologyIso_hom_homologyπ (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n)
    (c : (dsh C).cycles n) :
    (ConcreteCategory.hom (dshHomologyIso_mulFour C n hn).hom) (((dsh C).homologyπ n).hom c) =
      (C.homologyπ (4 + n)).hom ((ConcreteCategory.hom (dshCyclesIso' C n hn).hom) c) := by
  have h := congrArg (fun (g : (dsh C).cycles n ⟶ C.homology (4 + n)) => (ModuleCat.Hom.hom g) c)
    (dshHomology_π C n hn)
  simp only [dsh, ModuleCat.hom_comp] at h
  exact h

/-- The inverse direction of the `dsh` isomorphism on homology classes. -/
theorem dshHomologyIso_inv_homologyπ (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n)
    (c : C.cycles (4 + n)) :
    (ConcreteCategory.hom (dshHomologyIso_mulFour C n hn).inv) ((C.homologyπ (4 + n)).hom c) =
      ((dsh C).homologyπ n).hom ((ConcreteCategory.hom (dshCyclesIso' C n hn).inv) c) := by
  have hinj : Function.Injective
      (ConcreteCategory.hom (dshHomologyIso_mulFour C n hn).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinj
  rw [iso_hom_inv_apply]
  rw [dshHomologyIso_hom_homologyπ C n hn ((ConcreteCategory.hom (dshCyclesIso' C n hn).inv) c)]
  rw [iso_hom_inv_apply]

/-- The `iCycles` of the reindexed cycle. -/
theorem dshCyclesIso_hom_iCycles (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n)
    (c : (dsh C).cycles n) :
    C.iCycles (4 + n) ((ConcreteCategory.hom (dshCyclesIso' C n hn).hom) c) =
      (dsh C).iCycles n c := by
  have h : (dshCyclesIso' C n hn).hom ≫ C.iCycles (shiftEmb.f n) = (dsh C).iCycles n := by
    rw [show (dshCyclesIso' C n hn) = C.restrictionCyclesIso shiftEmb n (n-1)
      (downNext n hn) rfl rfl (downNextS n hn) from rfl]
    rw [HomologicalComplex.restrictionCyclesIso_hom_iCycles]
    congr 1
  exact congrArg (fun (g : (dsh C).cycles n ⟶ C.X (shiftEmb.f n)) => (ModuleCat.Hom.hom g) c) h

/-! ## The chosen top quasi-isomorphism and its cap comparison -/

/-- The quasi-isomorphism of the top term of the relative Mayer--Vietoris sequence used by
`ovlT`. -/
noncomputable def topPhi (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) : relMVTopC X A U V ⟶ relChains X A :=
  Classical.choose (relMV_quasiIso X A U V hU hV hcov)

/-- **The cap comparison for the chosen top quasi-isomorphism** (the proof of
`exists_capTopCanon_relCapHalf` for the specific choice `topPhi`). -/
theorem topPhi_cap (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (α : relKern ℤ X A 4) (m : ℕ) :
    (topPhi X A U V hU hV hcov).f (4 + m) ≫
        (cokernelComponentIso (inclChains X A) (4 + m)).hom ≫ relCapHalf ℤ X A α m
      = capTopCanon A U V α m ≫ (smallToSing U V).f m := by
  have h2 : cokernel.π (smallInToSmall U V A) ≫ topPhi X A U V hU hV hcov
      = smallToSing U V ≫ cokernel.π (inclChains X A) :=
    (Classical.choose_spec (relMV_quasiIso X A U V hU hV hcov)).2
  haveI : Epi ((cokernel.π (smallInToSmall U V A)).f (4 + m)) := epi_cokernel_π_f _ (4 + m)
  have hlevel : (cokernel.π (smallInToSmall U V A)).f (4 + m)
        ≫ (topPhi X A U V hU hV hcov).f (4 + m)
      = (smallToSing U V).f (4 + m) ≫ (cokernel.π (inclChains X A)).f (4 + m) := by
    rw [← HomologicalComplex.comp_f, h2, HomologicalComplex.comp_f]
  rw [← cancel_epi ((cokernel.π (smallInToSmall U V A)).f (4 + m))]
  simp only [← Category.assoc]
  rw [hlevel]
  ext y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hcast : relChainsModule ℤ X A (4 + m) = cokernel ((inclChains X A).f (4 + m)) := rfl
  show (ModuleCat.Hom.hom (relCapHalf ℤ X A α m))
      ((eqToHom hcast.symm).hom
        ((ModuleCat.Hom.hom (cokernelComponentIso (inclChains X A) (4 + m)).hom)
          ((ModuleCat.Hom.hom ((cokernel.π (inclChains X A)).f (4 + m)))
            ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y))))
      = (ModuleCat.Hom.hom ((smallToSing U V).f m))
          ((ModuleCat.Hom.hom (capTopCanon A U V α m))
            ((ModuleCat.Hom.hom ((cokernel.π (smallInToSmall U V A)).f (4 + m))) y))
  simp only [CategoryTheory.eqToHom_refl, cokernelComponentIso_canon_apply,
    relCapHalf_apply', capTopCanon_spec_apply, capSub_comp_incl_apply]
  show (ModuleCat.Hom.hom (relCapHalf ℤ X A α m))
      ((ModuleCat.Hom.hom (cokernel.π ((inclChains X A).f (4 + m))))
        ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y))
      = (ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj X) α.1 m))
          ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y)
  exact relCapHalf_apply' X A α m ((ModuleCat.Hom.hom ((smallToSing U V).f (4 + m))) y)

/-- The two canonical comparisons of `(relChains X A).X n` with the degreewise cokernel agree. -/
theorem relChains_cokernelIso_eq_cokernelComponentIso (X : TopCat) (A : Set X) (n : ℕ) :
    (relChains_cokernelIso X A n).hom = (cokernelComponentIso (inclChains X A) n).hom := by
  haveI : Epi ((cokernel.π (inclChains X A)).f n) := epi_cokernel_π_f _ n
  rw [← cancel_epi ((cokernel.π (inclChains X A)).f n)]
  rw [relChains_cokernelIso_canon]
  exact (cokernelComponentIso_canon (inclChains X A) n).symm

/-! ## The top cap comparison at the homology level -/

theorem capTopComparison (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (z : (relComplex ℤ X A).cycles 4)
    (y : (dsh (relMVTopC X A U V)).homology 4) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (smallToSing U V) 4))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (capTopChain A U V (((relComplex ℤ X A).iCycles 4).hom z)
            (relDiffLM_iCycles X A 4 z)) 4)) y)
      = relCapPair X A 4 4 (((relComplex ℤ X A).homologyπ 4).hom z)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (topPhi X A U V hU hV hcov) 8))
            ((ConcreteCategory.hom
              (dshHomologyIso_mulFour (relMVTopC X A U V) 4 (by norm_num)).hom) y)) := by
  classical
  obtain ⟨ŷ, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((dsh (relMVTopC X A U V)).homologyπ 4)).mp inferInstance y
  set α : relKern ℤ X A 4 := ((relComplex ℤ X A).iCycles 4).hom z with hαdef
  have hα : relDiffLM ℤ X A 4 α = 0 := relDiffLM_iCycles X A 4 z
  set x : (dsh (relMVTopC X A U V)).X 4 := (dsh (relMVTopC X A U V)).iCycles 4 ŷ with hxdef
  set ζ : (singularChains ℤ X).cycles 4 := (HomologicalComplex.cyclesMap
    (capTopChain A U V α hα ≫ smallToSing U V) 4).hom ŷ with hζdef
  set cc : (relChains X A).cycles 8 := (HomologicalComplex.cyclesMap
      (topPhi X A U V hU hV hcov) 8).hom
        ((ConcreteCategory.hom (dshCyclesIso' (relMVTopC X A U V) 4 (by norm_num)).hom) ŷ) with hccdef
  have hL : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (smallToSing U V) 4))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (capTopChain A U V α hα) 4))
          ((HomologicalComplex.homologyπ (dsh (relMVTopC X A U V)) 4).hom ŷ))
      = ((singularChains ℤ X).homologyπ 4).hom ζ := by
    rw [homologyMap_homologyπ_apply' (capTopChain A U V α hα) 4 ŷ]
    rw [homologyMap_homologyπ_apply' (smallToSing U V) 4]
    congr 1
    exact congrArg (fun (g : (dsh (relMVTopC X A U V)).cycles 4
        ⟶ (singularChains ℤ X).cycles 4) => (ModuleCat.Hom.hom g) ŷ)
      (HomologicalComplex.cyclesMap_comp (capTopChain A U V α hα) (smallToSing U V) 4).symm
  have hR : relCapPair X A 4 4 (((relComplex ℤ X A).homologyπ 4).hom z)
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (topPhi X A U V hU hV hcov) 8))
          ((ConcreteCategory.hom
            (dshHomologyIso_mulFour (relMVTopC X A U V) 4 (by norm_num)).hom)
            ((HomologicalComplex.homologyπ (dsh (relMVTopC X A U V)) 4).hom ŷ)))
      = ((singularChains ℤ X).homologyπ 4).hom (relCapPairZ X A 4 4 z cc) := by
    rw [dshHomologyIso_hom_homologyπ]
    rw [homologyMap_homologyπ_apply' (topPhi X A U V hU hV hcov) 8]
    rw [relCapPair_apply]
  have hcyc : ζ = relCapPairZ X A 4 4 z cc := by
    apply iCycles_injective_C ℤ (singularChains ℤ X) 4
    have h1 : (singularChains ℤ X).iCycles 4 ζ
        = (smallToSing U V).f 4 ((capTopChain A U V α hα).f 4 x) := by
      rw [hζdef]
      rw [cyclesMap_i_apply' (capTopChain A U V α hα ≫ smallToSing U V) 4 ŷ]
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    have h2 : (singularChains ℤ X).iCycles 4 (relCapPairZ X A 4 4 z cc)
        = relCapHalf ℤ X A α 4 ((relChains_cokernelIso X A 8).hom
            ((relChains X A).iCycles 8 cc)) := by
      rw [relCapPairZ_iCycles X A 4 4 z cc]
    have h3 : (relChains X A).iCycles 8 cc = (topPhi X A U V hU hV hcov).f 8 x := by
      rw [hccdef]
      rw [cyclesMap_i_apply' (topPhi X A U V hU hV hcov) 8]
      exact congrArg (fun w => (topPhi X A U V hU hV hcov).f 8 w)
        (dshCyclesIso_hom_iCycles (relMVTopC X A U V) 4 (by norm_num) ŷ)
    rw [h1, h2, h3, relChains_cokernelIso_eq_cokernelComponentIso]
    have hcmp := congrArg (fun (g : (dsh (relMVTopC X A U V)).X 4
        ⟶ (singularChains ℤ X).X 4) => (ModuleCat.Hom.hom g) x)
      (topPhi_cap X A U V hU hV hcov α 4)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcmp
    exact hcmp.symm
  rw [hL, hR, hcyc]

/-! ## The cap comparison on the overlap at the homology level -/

theorem capUvComparison (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (z : (relComplex ℤ X A).cycles 4)
    (h : ∀ x ∈ ovlA X A U V, (subtypeIncl X (U ∩ V)) x ∈ A)
    (w : (dsh (relMVUV X A U V)).homology 3) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (smallInToSingA U V (U ∩ V)) 3))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (capUvChain A U V (((relComplex ℤ X A).iCycles 4).hom z)
            (relDiffLM_iCycles X A 4 z)) 3)) w)
      = relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (relComplexMap ℤ (ovlA X A U V) A (subtypeIncl X (U ∩ V)) h) 4))
            (((relComplex ℤ X A).homologyπ 4).hom z))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7))
            ((ConcreteCategory.hom
              (dshHomologyIso_mulFour (relMVUV X A U V) 3 (by norm_num)).hom) w)) := by
  classical
  obtain ⟨what, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((dsh (relMVUV X A U V)).homologyπ 3)).mp inferInstance w
  set α : relKern ℤ X A 4 := ((relComplex ℤ X A).iCycles 4).hom z with hαdef
  have hα : relDiffLM ℤ X A 4 α = 0 := relDiffLM_iCycles X A 4 z
  set x : (dsh (relMVUV X A U V)).X 3 := (dsh (relMVUV X A U V)).iCycles 3 what with hxdef
  set ζ : (singularChains ℤ (TopCat.of ↥(U ∩ V))).cycles 3 := (HomologicalComplex.cyclesMap
    (capUvChain A U V α hα ≫ smallInToSingA U V (U ∩ V)) 3).hom what with hζdef
  set cc : (relChains (TopCat.of ↥(U ∩ V)) (ovlA X A U V)).cycles 7 := (HomologicalComplex.cyclesMap
      (relMVUVPhi X A U V) 7).hom
        ((ConcreteCategory.hom (dshCyclesIso' (relMVUV X A U V) 3 (by norm_num)).hom) what) with hccdef
  have hL : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (smallInToSingA U V (U ∩ V)) 3))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (capUvChain A U V α hα) 3))
          ((HomologicalComplex.homologyπ (dsh (relMVUV X A U V)) 3).hom what))
      = ((singularChains ℤ (TopCat.of ↥(U ∩ V))).homologyπ 3).hom ζ := by
    rw [homologyMap_homologyπ_apply' (capUvChain A U V α hα) 3 what]
    rw [homologyMap_homologyπ_apply' (smallInToSingA U V (U ∩ V)) 3]
    congr 1
    exact congrArg (fun (g : (dsh (relMVUV X A U V)).cycles 3
        ⟶ (singularChains ℤ (TopCat.of ↥(U ∩ V))).cycles 3) => (ModuleCat.Hom.hom g) what)
      (HomologicalComplex.cyclesMap_comp (capUvChain A U V α hα)
        (smallInToSingA U V (U ∩ V)) 3).symm
  have hR : relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA X A U V) A
            (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4)) (((relComplex ℤ X A).homologyπ 4).hom z))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7))
          ((ConcreteCategory.hom
            (dshHomologyIso_mulFour (relMVUV X A U V) 3 (by norm_num)).hom)
            ((HomologicalComplex.homologyπ (dsh (relMVUV X A U V)) 3).hom what)))
      = ((singularChains ℤ (TopCat.of ↥(U ∩ V))).homologyπ 3).hom
          (relCapPairZ (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
            ((HomologicalComplex.cyclesMap (relComplexMap ℤ (ovlA X A U V) A
              (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4).hom z) cc) := by
    rw [homologyMap_homologyπ_apply' (relComplexMap ℤ (ovlA X A U V) A
      (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4 z]
    rw [dshHomologyIso_hom_homologyπ]
    rw [homologyMap_homologyπ_apply' (relMVUVPhi X A U V) 7]
    rw [relCapPair_apply]
  have hcyc : ζ = relCapPairZ (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
      ((HomologicalComplex.cyclesMap (relComplexMap ℤ (ovlA X A U V) A
        (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4).hom z) cc := by
    apply iCycles_injective_C ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V))) 3
    have h1 : (singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles 3 ζ
        = (smallInToSingA U V (U ∩ V)).f 3 ((capUvChain A U V α hα).f 3 x) := by
      rw [hζdef]
      rw [cyclesMap_i_apply' (capUvChain A U V α hα ≫ smallInToSingA U V (U ∩ V)) 3 what]
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    have h2 : (singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles 3
          (relCapPairZ (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
            ((HomologicalComplex.cyclesMap (relComplexMap ℤ (ovlA X A U V) A
              (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4).hom z) cc)
        = relCapHalf ℤ (TopCat.of ↥(U ∩ V)) (ovlA X A U V) (ovl X A U V α) 3
            ((relChains_cokernelIso (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 7).hom
              ((relChains (TopCat.of ↥(U ∩ V)) (ovlA X A U V)).iCycles 7 cc)) := by
      rw [relCapPairZ_iCycles]
      have hcoc : ((relComplex ℤ (TopCat.of ↥(U ∩ V)) (ovlA X A U V)).iCycles 4).hom
          ((HomologicalComplex.cyclesMap (relComplexMap ℤ (ovlA X A U V) A
            (subtypeIncl X (U ∩ V)) (fun _ hx => hx)) 4).hom z) = ovl X A U V α := by
        rw [cyclesMap_i_apply', relComplexMap_f]
        rfl
      rw [hcoc]
    have h3 : (relChains (TopCat.of ↥(U ∩ V)) (ovlA X A U V)).iCycles 7 cc
        = (relMVUVPhi X A U V).f 7 x := by
      rw [hccdef]
      rw [cyclesMap_i_apply' (relMVUVPhi X A U V) 7]
      exact congrArg (fun w => (relMVUVPhi X A U V).f 7 w)
        (dshCyclesIso_hom_iCycles (relMVUV X A U V) 3 (by norm_num) what)
    rw [h1, h2, h3,
      relChains_cokernelIso_eq_cokernelComponentIso (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 7]
    have hcmp := congrArg (fun (g : (dsh (relMVUV X A U V)).X 3
        ⟶ (singularChains ℤ (TopCat.of ↥(U ∩ V))).X 3) => (ModuleCat.Hom.hom g) x)
      (exists_capUvCanon_relCapHalf X A U V α 3)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcmp
    exact hcmp.symm
  rw [hL, hR, hcyc]

/-! ## The transgression identity in the `cruxδ` form -/

/-- **The transgression identity in the `cruxδ` form**: `transgression_capUvCanon` with the
reindexed connecting map replaced by `cruxδ X A U V (4 + m)`. -/
theorem transgression_cruxδ' (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (α : relKern ℤ X A 4) (hα : relDiffLM ℤ X A 4 α = 0)
    (m : ℕ) (hm : 1 ≤ m) :
    CategoryTheory.CategoryStruct.comp
        (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) (by omega)).hom
        (CategoryTheory.CategoryStruct.comp (cruxδ X A U V (4 + m))
          (dshHomologyIso_mulFour (relMVUV X A U V) m hm).inv)
      ≫ HomologicalComplex.homologyMap (capUvChain A U V α hα) m
    = HomologicalComplex.homologyMap (capTopChain A U V α hα) (m + 1)
      ≫ (mvSmall_shortExact U V).δ (m + 1) m (by simp only [ComplexShape.down_Rel]) := by
  rw [← dshShort_cruxShort_delta X A U V m hm]
  exact transgression_capUvCanon A U V α hα m

/-- The elementwise form of `transgression_cruxδ'`: the two sides of the transgression identity
agree on a homology class of the top term. -/
theorem cruxDelta_transgression (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (α : relKern ℤ X A 4) (hα : relDiffLM ℤ X A 4 α = 0)
    (y : (relMVTopC X A U V).homology 8) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (capUvChain A U V α hα) 3))
        ((ConcreteCategory.hom (dshHomologyIso_mulFour (relMVUV X A U V) 3 (by norm_num)).inv)
          ((cruxδ X A U V 7).hom y))
      = (ModuleCat.Hom.hom ((mvSmall_shortExact U V).δ 4 3
            (by simp [ComplexShape.down_Rel])))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (capTopChain A U V α hα) 4))
            ((ConcreteCategory.hom
              (dshHomologyIso_mulFour (relMVTopC X A U V) 4 (by norm_num)).inv) y)) := by
  have h := transgression_cruxδ' X A U V hU hV hcov α hα 3 (by norm_num)
  have h2 := congrArg (fun (g : (dsh (relMVTopC X A U V)).homology 4
      ⟶ (smallInChains U V (U ∩ V)).homology 3) =>
      (ModuleCat.Hom.hom g)
        ((ConcreteCategory.hom
          (dshHomologyIso_mulFour (relMVTopC X A U V) 4 (by norm_num)).inv) y)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [show (ConcreteCategory.hom
        (dshHomologyIso_mulFour (relMVTopC X A U V) 4 (by norm_num)).hom)
      ((ConcreteCategory.hom
        (dshHomologyIso_mulFour (relMVTopC X A U V) 4 (by norm_num)).inv) y) = y from
    iso_hom_inv_apply _ y] at h2
  exact h2

/-! ## The transgression identity -/

/-- **The transgression identity** for the pair `(X,A)` and the cover `U ∪ V = X`: the cap product
with a relative `4`-cocycle commutes, up to sign, with the Mayer--Vietoris connecting maps
`T₀ = ovlT` (relative) and `U₀ = ovlU` (absolute). -/
theorem transgression_identity (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hδT : IsIso (cruxδ X A U V 7))
    (h : ∀ x ∈ ovlA X A U V, (subtypeIncl X (U ∩ V)) x ∈ A)
    (δmv : (smallChains U V).homology 4 ≃ₗ[ℤ] (smallInChains U V (U ∩ V)).homology 3)
    (hδmv : ∀ x, δmv x = (ModuleCat.Hom.hom ((mvSmall_shortExact U V).δ 4 3
      (by simp [ComplexShape.down_Rel]))) x)
    (a : relCohomology ℤ X A 4) (c : (relChains X A).homology 8) :
    (ovlU X U V hU hV hcov δmv) (relCapPair X A 4 4 a c)
        = relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA X A U V) A
              (subtypeIncl X (U ∩ V)) h) 4)) a)
            ((ovlT X A U V hU hV hcov hδT) c)
      ∨ (ovlU X U V hU hV hcov δmv) (relCapPair X A 4 4 a c)
        = - relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA X A U V) A
              (subtypeIncl X (U ∩ V)) h) 4)) a)
            ((ovlT X A U V hU hV hcov hδT) c) := by
  classical
  -- the chosen quasi-isomorphism of the top term, and its two properties
  have hφiso : ∀ n, IsIso (HomologicalComplex.homologyMap (topPhi X A U V hU hV hcov) n) :=
    (Classical.choose_spec (relMV_quasiIso X A U V hU hV hcov)).1
  have hφ8 : IsIso (HomologicalComplex.homologyMap
      (Classical.choose (relMV_quasiIso X A U V hU hV hcov)) 8) := hφiso 8
  haveI := hφ8
  -- representatives of `a` and `c`
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((relComplex ℤ X A).homologyπ 4)).mp
    inferInstance a
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap (topPhi X A U V hU hV hcov) 8)).mp inferInstance c
  have hy' : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Classical.choose (relMV_quasiIso X A U V hU hV hcov)) 8)) y = c := hy
  have hα : relDiffLM ℤ X A 4 (((relComplex ℤ X A).iCycles 4).hom z) = 0 :=
    relDiffLM_iCycles X A 4 z
  -- the two elements fed into the two cap comparisons
  set y₀ : (dsh (relMVTopC X A U V)).homology 4 :=
    (ConcreteCategory.hom (dshHomologyIso_mulFour (relMVTopC X A U V) 4 (by norm_num)).inv) y
    with hy₀
  set w : (dsh (relMVUV X A U V)).homology 3 :=
    (ConcreteCategory.hom (dshHomologyIso_mulFour (relMVUV X A U V) 3 (by norm_num)).inv)
      ((cruxδ X A U V 7).hom y) with hw
  -- (1) the top cap comparison
  have hβ : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (smallToSing U V) 4))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (capTopChain A U V (((relComplex ℤ X A).iCycles 4).hom z) hα) 4)) y₀)
      = relCapPair X A 4 4 a c := by
    have hh := capTopComparison X A U V hU hV hcov z y₀
    rw [hz] at hh
    rw [show (ConcreteCategory.hom (dshHomologyIso_mulFour (relMVTopC X A U V) 4
        (by norm_num)).hom) y₀ = y from iso_hom_inv_apply _ y] at hh
    rw [hy] at hh
    exact hh
  -- (2) the transgression identity relates the connecting map to the relative cap product
  have hδ : δmv ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (capTopChain A U V (((relComplex ℤ X A).iCycles 4).hom z) hα) 4)) y₀)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (capUvChain A U V (((relComplex ℤ X A).iCycles 4).hom z) hα) 3)) w := by
    have hh := cruxDelta_transgression X A U V hU hV hcov
      (((relComplex ℤ X A).iCycles 4).hom z) hα y
    rw [show (ConcreteCategory.hom (dshHomologyIso_mulFour (relMVUV X A U V) 3
        (by norm_num)).inv) ((cruxδ X A U V 7).hom y) = w from rfl] at hh
    rw [show (ConcreteCategory.hom (dshHomologyIso_mulFour (relMVTopC X A U V) 4
        (by norm_num)).inv) y = y₀ from rfl] at hh
    rw [hδmv]
    exact hh.symm
  -- (3) the overlap cap comparison
  haveI := isIso_smallInToSingA U V (U ∩ V) hU hV hcov 3
  have hγ : (asIso (HomologicalComplex.homologyMap (smallInToSingA U V (U ∩ V)) 3)).toLinearEquiv
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (capUvChain A U V (((relComplex ℤ X A).iCycles 4).hom z) hα) 3)) w)
      = relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA X A U V) A
            (subtypeIncl X (U ∩ V)) h) 4)) a)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7))
            ((cruxδ X A U V 7).hom y)) := by
    have hh := capUvComparison X A U V hU hV hcov z h w
    rw [hz] at hh
    rw [show (ConcreteCategory.hom (dshHomologyIso_mulFour (relMVUV X A U V) 3
        (by norm_num)).hom) w = (cruxδ X A U V 7).hom y from
      iso_hom_inv_apply _ ((cruxδ X A U V 7).hom y)] at hh
    exact hh
  -- (4) the value of `ovlT` at `c`
  have hT : (ovlT X A U V hU hV hcov hδT) c
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relMVUVPhi X A U V) 7))
          ((cruxδ X A U V 7).hom y) := by
    rw [ovlT_eq X A U V hU hV hcov hδT hφ8
      (relMVUV_quasiIso X A U V hU hV hcov 7) c]
    have hkey : ((asIso (HomologicalComplex.homologyMap
        (Classical.choose (relMV_quasiIso X A U V hU hV hcov)) 8)).toLinearEquiv).symm c = y := by
      rw [← hy']
      exact LinearEquiv.symm_apply_apply _ _
    rw [hkey]
    rfl
  -- (5) the value of `ovlU` at `relCapPair X A 4 4 a c`
  have hU₀ : (ovlU X U V hU hV hcov δmv) (relCapPair X A 4 4 a c)
      = relCapPair (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 3
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relComplexMap ℤ (ovlA X A U V) A
            (subtypeIncl X (U ∩ V)) h) 4)) a)
          ((ovlT X A U V hU hV hcov hδT) c) := by
    rw [ovlU_eq X U V hU hV hcov δmv
      (smallChains_homology_iso U V hU hV hcov 4)
      (isIso_smallInToSingA U V (U ∩ V) hU hV hcov 3)]
    haveI := smallChains_homology_iso U V hU hV hcov 4
    have hsy : ((asIso (HomologicalComplex.homologyMap (smallToSing U V) 4)).toLinearEquiv).symm
        (relCapPair X A 4 4 a c) = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (capTopChain A U V (((relComplex ℤ X A).iCycles 4).hom z) hα) 4)) y₀ := by
      rw [← hβ]
      exact LinearEquiv.symm_apply_apply _ _
    rw [hsy, hδ, hγ, hT]
  exact Or.inl hU₀

/-- The absolute Mayer--Vietoris connecting isomorphism of the cover `vkU ∪ vkV = Vk (-2)`. -/
abbrev vkDeltaIso :
    (smallChains vkU vkV).homology 4 ≅ (smallInChains vkU vkV (vkU ∩ vkV)).homology 3 := by
  haveI := vkδabs_isIso
  exact asIso ((mvSmall_shortExact vkU vkV).δ 4 3 rfl)

/-- The transgression identity specialised to the two-chart cover of `Vk (-2)`. -/
theorem vkInternalTransgression_aux (hδT : IsIso (cruxδ vkPairX vkPairA vkU vkV 7)) :
    ∃ (T₀ : (relChains vkPairX vkPairA).homology 8
            →ₗ[ℤ] (relChains (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV)).homology 7)
      (U₀ : (singularChains ℤ vkPairX).homology 4
            →ₗ[ℤ] (singularChains ℤ (TopCat.of ↥(vkU ∩ vkV))).homology 3),
      Function.Surjective T₀ ∧ Function.Injective U₀ ∧
      ∀ (a : relCohomology ℤ vkPairX vkPairA 4)
        (c : (relChains vkPairX vkPairA).homology 8),
        U₀ (relCapPair vkPairX vkPairA 4 4 a c)
            = relCapPair (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV) 4 3
                ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
                  (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV) vkPairA
                    (subtypeIncl vkPairX (vkU ∩ vkV)) (fun x hx => hx)) 4)) a) (T₀ c) ∨
        U₀ (relCapPair vkPairX vkPairA 4 4 a c)
            = - relCapPair (TopCat.of ↥(vkU ∩ vkV)) (ovlA vkPairX vkPairA vkU vkV) 4 3
                ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
                  (relComplexMap ℤ (ovlA vkPairX vkPairA vkU vkV) vkPairA
                    (subtypeIncl vkPairX (vkU ∩ vkV)) (fun x hx => hx)) 4)) a) (T₀ c) := by
  refine ⟨(ovlT vkPairX vkPairA vkU vkV vkU_isOpen vkV_isOpen vkU_union_vkV hδT).toLinearMap,
    (ovlU vkPairX vkU vkV vkU_isOpen vkV_isOpen vkU_union_vkV vkDeltaIso.toLinearEquiv).toLinearMap,
    (ovlT vkPairX vkPairA vkU vkV vkU_isOpen vkV_isOpen vkU_union_vkV hδT).surjective,
    (ovlU vkPairX vkU vkV vkU_isOpen vkV_isOpen vkU_union_vkV vkDeltaIso.toLinearEquiv).injective,
    ?_⟩
  intro a c
  refine transgression_identity vkPairX vkPairA vkU vkV vkU_isOpen vkV_isOpen vkU_union_vkV hδT
    (fun x hx => hx) vkDeltaIso.toLinearEquiv ?_ a c
  intro x
  rfl

end InternalTransgression

/-- **The internal transgression identity of the two-chart cover of `Vk (-2)`.** -/
theorem vkInternalTransgression :
    ∃ (T₀ : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8
            →ₗ[ℤ] (Work.Cohomology.relChains Work.Cohomology.Crux.vkOvl
              Work.Cohomology.Crux.vkOvlA).homology 7)
      (U₀ : (Work.Cohomology.singularChains ℤ Work.Cohomology.vkPairX).homology 4
            →ₗ[ℤ] (Work.Cohomology.singularChains ℤ Work.Cohomology.Crux.vkOvl).homology 3),
      Function.Surjective T₀ ∧ Function.Injective U₀ ∧
      ∀ (a : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4)
        (c : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8),
        U₀ (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 a c)
            = Work.Cohomology.relCapPair Work.Cohomology.Crux.vkOvl Work.Cohomology.Crux.vkOvlA 4 3
                ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
                  (Work.Cohomology.relComplexMap ℤ Work.Cohomology.Crux.vkOvlA
                    Work.Cohomology.vkPairA
                    (Work.Cohomology.subtypeIncl Work.Cohomology.vkPairX
                      (Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
                    (fun x hx => hx)) 4)) a) (T₀ c) ∨
        U₀ (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 a c)
            = - Work.Cohomology.relCapPair Work.Cohomology.Crux.vkOvl Work.Cohomology.Crux.vkOvlA 4 3
                ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
                  (Work.Cohomology.relComplexMap ℤ Work.Cohomology.Crux.vkOvlA
                    Work.Cohomology.vkPairA
                    (Work.Cohomology.subtypeIncl Work.Cohomology.vkPairX
                      (Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
                    (fun x hx => hx)) 4)) a) (T₀ c) := by
  exact InternalTransgression.vkInternalTransgression_aux cruxDelta7_isIso

end

end Work.Cohomology.Crux
