import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.singularCohomology_zero_Hom
import Submission.Work.Cohomology.sphereBandHomotopyEquiv
import Submission.Work.Cohomology.sphereHomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Limits Simplicial
open scoped Simplicial Topology unitInterval
open Classical

namespace Work.Cohomology

noncomputable section

namespace Sph1

/-! ## A. Cocycles on `0`-chains are constant on path components -/

/-- A linear functional on the `0`-chains of `X` which kills the differential `d₁` takes the same
value on all `0`-simplices representing the same connected component. -/
theorem sgen_congr_of_pi0 {X : TopCat}
    (f : (singularChains ℤ X).X 0 →ₗ[ℤ] ℤ)
    (hf : f.comp ((singularChains ℤ X).d 1 0).hom = 0)
    {s s' : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)}
    (h : SSet.π₀.mk s = SSet.π₀.mk s') :
    f (sgen ℤ X s) = f (sgen ℤ X s') := by
  have hmem : (singularChains ℤ X).d 1 0 ≫ ModuleCat.ofHom f = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
    exact hf
  have hmem' : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0
      ≫ ModuleCat.ofHom f = 0 := by
    rw [show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 =
      (singularChains ℤ X).d 1 0 from rfl]
    exact hmem
  obtain ⟨hh, hfac⟩ := CokernelCofork.IsColimit.desc'
    (SSet.isColimitCokernelCoforkChainComplexDOneZero (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ))
    (ModuleCat.ofHom f) hmem'
  have key : ∀ s, f (sgen ℤ X s) =
      ModuleCat.Hom.hom hh
        (ModuleCat.Hom.hom (Sigma.ι
          (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s)) 1) := by
    intro s
    rw [show f (sgen ℤ X s) = ModuleCat.Hom.hom
        (SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) s
          ≫ ModuleCat.ofHom f) 1 from by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      rfl]
    rw [← hfac, CokernelCofork.π_ofπ]
    rw [← Category.assoc, SSet.π₀.comp_fromChainComplexXZero]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  rw [key s, key s', h]

/-- A linear functional on the `0`-chains of `X` which kills the differential `d₁` takes the same
value at two points joined by a path. -/
theorem sgen_congr_of_joined {X : TopCat}
    (f : (singularChains ℤ X).X 0 →ₗ[ℤ] ℤ)
    (hf : f.comp ((singularChains ℤ X).d 1 0).hom = 0)
    {x y : X} (h : Joined x y) :
    f (sgen ℤ X ((TopCat.toSSetObj₀Equiv (X := X)).symm x))
      = f (sgen ℤ X ((TopCat.toSSetObj₀Equiv (X := X)).symm y)) := by
  refine sgen_congr_of_pi0 f hf ?_
  rw [← TopCat.zerothHomotopyEquiv_mk x, ← TopCat.zerothHomotopyEquiv_mk y,
    TopCat.zerothHomotopyEquiv, Equiv.coe_fn_mk]
  exact congrArg _ (ZerothHomotopy.sound h.somePath)

/-- Two `0`-simplices whose underlying points can be joined by a path represent the same
component. -/
lemma pi0_mk_eq_of_joined {X : TopCat}
    {s s' : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)}
    (h : Joined (TopCat.toSSetObj₀Equiv s) (TopCat.toSSetObj₀Equiv s')) :
    SSet.π₀.mk s = SSet.π₀.mk s' := by
  refine TopCat.zerothHomotopyEquiv.symm.injective ?_
  rw [TopCat.zerothHomotopyEquiv_symm_mk, TopCat.zerothHomotopyEquiv_symm_mk]
  exact ZerothHomotopy.sound h.somePath

/-- Conversely, `0`-simplices representing the same component have joinable underlying points. -/
lemma joined_of_pi0_mk_eq {X : TopCat}
    {s s' : (TopCat.toSSet.obj X).obj (Opposite.op ⦋0⦌)}
    (h : SSet.π₀.mk s = SSet.π₀.mk s') :
    Joined (TopCat.toSSetObj₀Equiv s) (TopCat.toSSetObj₀Equiv s') := by
  have h1 : ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv s)
      = ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv s') := by
    have := congrArg (TopCat.zerothHomotopyEquiv (X := X)).symm h
    rwa [TopCat.zerothHomotopyEquiv_symm_mk, TopCat.zerothHomotopyEquiv_symm_mk] at this
  exact Quotient.exact h1

/-! ## B. The equatorial band `band 1` -/

/-- The band `band 1 ⊆ S¹` (`= capA 1 ∩ capB 1`), as a topological space. -/
abbrev bandW : TopCat := TopCat.of ↥(capA 1 ∩ capB 1)

/-- The homeomorphism between `↥(band 1)` (the band inside `S¹`) and `Band 1`. -/
def bandHomeo : ↥(capA 1 ∩ capB 1) ≃ₜ Band 1 where
  toFun x := ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2.1, z.2.2.2⟩
  left_inv x := by ext <;> rfl
  right_inv z := by ext <;> rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun x => ⟨x.1.2, x.2.1, x.2.2⟩)
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun z => z.2.1))
      (fun z => ⟨z.2.2.1, z.2.2.2⟩)

/-- The "north pole" `(1, 0)` of the band. -/
def bP : ↥(capA 1 ∩ capB 1) := bandHomeo.symm (gMap 1 sphOnePointN)

/-- The "south pole" `(-1, 0)` of the band. -/
def bQ : ↥(capA 1 ∩ capB 1) := bandHomeo.symm (gMap 1 sphOnePointS)

lemma bandHomeo_bP : bandHomeo bP = gMap 1 sphOnePointN := bandHomeo.apply_symm_apply _

lemma bandHomeo_bQ : bandHomeo bQ = gMap 1 sphOnePointS := bandHomeo.apply_symm_apply _

lemma fMap_one_cases (x : Band 1) : fMap 1 x = sphOnePointN ∨ fMap 1 x = sphOnePointS :=
  sphOne_cases (fMap 1 x)

/-- **Every point of the band is joined to the north or the south pole.** -/
theorem bandJoined (x : ↥(capA 1 ∩ capB 1)) : Joined x bP ∨ Joined x bQ := by
  have hpath : Path (bandHomeo x)
      (((gMap 1).comp (fMap 1)) (bandHomeo x)) := (HambHomotopy 1).evalAt (bandHomeo x)
  rcases fMap_one_cases (bandHomeo x) with hf | hf
  · left
    refine ⟨Path.cast (hpath.map bandHomeo.symm.continuous) ?_ ?_⟩
    · simp
    · rw [ContinuousMap.comp_apply, hf]; rfl
  · right
    refine ⟨Path.cast (hpath.map bandHomeo.symm.continuous) ?_ ?_⟩
    · simp
    · rw [ContinuousMap.comp_apply, hf]; rfl

/-- The two poles of the band are not joined. -/
theorem bP_not_joined_bQ : ¬ Joined bP bQ := by
  intro h
  obtain ⟨γ⟩ := h
  haveI hd : DiscreteTopology ↥(sphSet 1) := discreteTopology_sphSet_one
  have hcont : Continuous (fun t : I => fMap 1 (bandHomeo (γ t))) :=
    (fMap 1).continuous.comp (bandHomeo.continuous.comp γ.continuous)
  have hconst := PreconnectedSpace.constant (α := I) (Y := ↥(sphSet 1)) inferInstance
    (f := fun t : I => fMap 1 (bandHomeo (γ t))) hcont (x := (0 : I)) (y := (1 : I))
  have h0 : fMap 1 (bandHomeo (γ 0)) = sphOnePointN := by
    rw [γ.source, bandHomeo_bP, fMap_gMap]
  have h1 : fMap 1 (bandHomeo (γ 1)) = sphOnePointS := by
    rw [γ.target, bandHomeo_bQ, fMap_gMap]
  rw [h0, h1] at hconst
  exact sphOnePointS_ne_N hconst.symm


/-! ## C. The "indicator" `0`-cochain on the band -/

/-- The `0`-th homotopy class of the north pole in the band. -/
noncomputable def bandPi0 : SSet.π₀ (TopCat.toSSet.obj bandW) :=
  SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := bandW)).symm bP)

/-- The indicator cochain, as a morphism: `1` on the northern island of the band, `0` elsewhere. -/
noncomputable def indicMor :
    ((TopCat.toSSet.obj bandW).chainComplex (ModuleCat.of ℤ ℤ)).X 0 ⟶ ModuleCat.of ℤ ℤ :=
  SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW) (ModuleCat.of ℤ ℤ) ≫
    Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
      if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ) else 0)

/-- The linear functional underlying `indicMor`. -/
noncomputable def indic : Cochain ℤ (TopCat.toSSet.obj bandW) 0 := indicMor.hom

theorem indicMor_comp_d :
    ((TopCat.toSSet.obj bandW).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫ indicMor = 0 := by
  rw [show indicMor = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW)
      (ModuleCat.of ℤ ℤ) ≫
      Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
        if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl]
  rw [← Category.assoc, SSet.π₀.d_fromChainComplexXZero, zero_comp]

/-- The indicator is a `0`-cocycle. -/
theorem indic_cocycle : cochainDiff ℤ (TopCat.toSSet.obj bandW) indic = 0 := by
  have h := congrArg ModuleCat.Hom.hom indicMor_comp_d
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  show indic.comp (((TopCat.toSSet.obj bandW).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom = 0
  exact h

theorem indic_gen_of_mem (s : (TopCat.toSSet.obj bandW).obj (Opposite.op ⦋0⦌))
    (hc : SSet.π₀.mk s = bandPi0) :
    genEval ℤ (TopCat.toSSet.obj bandW) indic s = 1 := by
  have h1 : ModuleCat.Hom.hom indicMor =
      (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
        if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ) else 0))).comp
      (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW)
        (ModuleCat.of ℤ ℤ))) := by
    rw [show indicMor = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW)
        (ModuleCat.of ℤ ℤ) ≫
        Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
          if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl, ModuleCat.hom_comp]
  have h2 : (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW)
        (ModuleCat.of ℤ ℤ)))
        ((ModuleCat.Hom.hom ((TopCat.toSSet.obj bandW).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s)) 1)
      = (ModuleCat.Hom.hom (Sigma.ι
          (fun _ : SSet.π₀ (TopCat.toSSet.obj bandW) => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := TopCat.toSSet.obj bandW)
        (R := ModuleCat.of ℤ ℤ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  change ModuleCat.Hom.hom indicMor
      (((TopCat.toSSet.obj bandW).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) = 1
  rw [h1]
  simp only [LinearMap.comp_apply]
  rw [h2]
  have h3 : (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
        if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))))
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj bandW) =>
          ModuleCat.of ℤ ℤ) (SSet.π₀.mk s))) 1)
      = (ModuleCat.Hom.hom (if SSet.π₀.mk s = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ)
          else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
        if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) (SSet.π₀.mk s))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  rw [h3]
  simp [hc]

theorem indic_gen_of_not_mem (s : (TopCat.toSSet.obj bandW).obj (Opposite.op ⦋0⦌))
    (hc : SSet.π₀.mk s ≠ bandPi0) :
    genEval ℤ (TopCat.toSSet.obj bandW) indic s = 0 := by
  have h1 : ModuleCat.Hom.hom indicMor =
      (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
        if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ) else 0))).comp
      (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW)
        (ModuleCat.of ℤ ℤ))) := by
    rw [show indicMor = SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW)
        (ModuleCat.of ℤ ℤ) ≫
        Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
          if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ) else 0) from rfl, ModuleCat.hom_comp]
  have h2 : (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj bandW)
        (ModuleCat.of ℤ ℤ)))
        ((ModuleCat.Hom.hom ((TopCat.toSSet.obj bandW).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s)) 1)
      = (ModuleCat.Hom.hom (Sigma.ι
          (fun _ : SSet.π₀ (TopCat.toSSet.obj bandW) => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := TopCat.toSSet.obj bandW)
        (R := ModuleCat.of ℤ ℤ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  change ModuleCat.Hom.hom indicMor
      (((TopCat.toSSet.obj bandW).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) = 0
  rw [h1]
  simp only [LinearMap.comp_apply]
  rw [h2]
  have h3 : (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
        if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))))
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj bandW) =>
          ModuleCat.of ℤ ℤ) (SSet.π₀.mk s))) 1)
      = (ModuleCat.Hom.hom (if SSet.π₀.mk s = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ)
          else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ (TopCat.toSSet.obj bandW) =>
        if c = bandPi0 then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) (SSet.π₀.mk s))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  rw [h3]
  simp [hc]

/-- The two poles of the band lie in different components. -/
theorem pi0_bQ_ne_bP :
    SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := bandW)).symm bQ) ≠ bandPi0 := by
  intro h
  have h2 := joined_of_pi0_mk_eq h
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  exact bP_not_joined_bQ h2.symm

theorem indic_bP : genEval ℤ (TopCat.toSSet.obj bandW) indic
    ((TopCat.toSSetObj₀Equiv (X := bandW)).symm bP) = 1 :=
  indic_gen_of_mem _ (by simp only [bandPi0])

theorem indic_bQ : genEval ℤ (TopCat.toSSet.obj bandW) indic
    ((TopCat.toSSetObj₀Equiv (X := bandW)).symm bQ) = 0 :=
  indic_gen_of_not_mem _ pi0_bQ_ne_bP

/-! ## D. Pullback of the unit cochain -/

/-- The pullback of the unit `0`-cochain along a map of simplicial sets is the unit `0`-cochain. -/
theorem unitCochain_dualMap {X Y : SSet} (g : X ⟶ Y) :
    ((SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap (unitCochain ℤ Y)
      = unitCochain ℤ X := by
  apply dual_ext_of_iota
  intro s
  have hnat : ((SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f 0).hom
      ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
      = (Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) (g.app (Opposite.op ⦋0⦌) s)).hom 1 :=
    congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.ι_chainComplexMap_f _ _ g (ModuleCat.of ℤ ℤ) s)
  show (((SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap (unitCochain ℤ Y))
      ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
    = (unitCochain ℤ X) ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
  rw [LinearMap.dualMap_apply, hnat]
  exact (genEval_unitCochain ℤ Y (g.app (Opposite.op ⦋0⦌) s)).trans
    (genEval_unitCochain ℤ X s).symm

/-! ## E. Linearity of the class map in the cochain -/

theorem cohomologyClassOf_smul {R : Type} [CommRing R] {X : SSet} {n : ℕ} (a : R)
    (α : Cochain R X n) (h : cochainDiff R X (a • α) = 0) (hα : cochainDiff R X α = 0) :
    cohomologyClassOf R X (a • α) h = a • cohomologyClassOf R X α hα := by
  rw [cohomologyClassOf, cohomologyClassOf, cocycleOf_smul R X a α h hα, map_smul]

/-- The `ℤ`-scalar form of `cohomologyClassOf_smul`, with the canonical `ℤ`-scalar structure. -/
theorem cohomologyClassOf_smul_int {X : SSet} {n : ℕ} (a : ℤ) (α : Cochain ℤ X n)
    (h : cochainDiff ℤ X (a • α) = 0) (hα : cochainDiff ℤ X α = 0) :
    cohomologyClassOf ℤ X (a • α) h = a • cohomologyClassOf ℤ X α hα := by
  rw [← int_smul_eq_zsmul (M := ↑(HomologicalComplex.homology (SSetCochainComplex ℤ X) n))]
  exact cohomologyClassOf_smul a α h hα

/-! ## E2. The `chainComplex`-level constancy lemmas and the Mayer–Vietoris maps -/

/-- A linear functional on the `0`-cochains of a simplicial set which is a `0`-cocycle takes the
same value on `0`-simplices representing the same component. -/
theorem genEval_congr_of_pi0 {X : SSet} {f : Cochain ℤ X 0}
    (hf : cochainDiff ℤ X f = 0) {s s' : X _⦋0⦌} (h : SSet.π₀.mk s = SSet.π₀.mk s') :
    genEval ℤ X f s = genEval ℤ X f s' := by
  have hmem : (X.chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫ ModuleCat.ofHom f = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
    exact hf
  obtain ⟨hh, hfac⟩ := CokernelCofork.IsColimit.desc'
    (SSet.isColimitCokernelCoforkChainComplexDOneZero X (ModuleCat.of ℤ ℤ))
    (ModuleCat.ofHom f) hmem
  have key : ∀ s, genEval ℤ X f s = ModuleCat.Hom.hom hh
      (ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ X => ModuleCat.of ℤ ℤ) (SSet.π₀.mk s)) 1) := by
    intro s
    rw [show genEval ℤ X f s = ModuleCat.Hom.hom
        (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫ ModuleCat.ofHom f) 1 from by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      rfl]
    rw [← hfac, CokernelCofork.π_ofπ]
    rw [← Category.assoc, SSet.π₀.comp_fromChainComplexXZero]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  rw [key s, key s', h]

/-- The `chainComplex`-level form of `sgen_congr_of_joined`. -/
theorem genEval_congr_of_joined {X : TopCat} {f : Cochain ℤ (TopCat.toSSet.obj X) 0}
    (hf : cochainDiff ℤ (TopCat.toSSet.obj X) f = 0) {x y : X} (h : Joined x y) :
    genEval ℤ (TopCat.toSSet.obj X) f ((TopCat.toSSetObj₀Equiv (X := X)).symm x)
      = genEval ℤ (TopCat.toSSet.obj X) f ((TopCat.toSSetObj₀Equiv (X := X)).symm y) := by
  refine genEval_congr_of_pi0 hf ?_
  rw [← TopCat.zerothHomotopyEquiv_mk x, ← TopCat.zerothHomotopyEquiv_mk y,
    TopCat.zerothHomotopyEquiv, Equiv.coe_fn_mk]
  exact congrArg _ (ZerothHomotopy.sound h.somePath)

/-- The inclusion `C_*(U ∩ V) ⟶ C_*(U)` is the chain map induced by the inclusion. -/
lemma chainInclU_eq_chainMap {X : TopCat} (U V : Set X) :
    chainInclU U V = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) := rfl

/-- The inclusion `C_*(U ∩ V) ⟶ C_*(V)` is the chain map induced by the inclusion. -/
lemma chainInclV_eq_chainMap {X : TopCat} (U V : Set X) :
    chainInclV U V = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (inclUVV U V) := rfl

/-- The dual of `chainInclU` is the cochain pullback induced by the inclusion. -/
lemma dualComplexMap_chainInclU {X : TopCat} (U V : Set X) :
    dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V))) (singularChains ℤ (TopCat.of U))
      (chainInclU U V)
      = dualChainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of U) (inclUVU U V) := by
  rw [chainInclU_eq_chainMap]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  rfl

/-- The dual of `chainInclV` is the cochain pullback induced by the inclusion. -/
lemma dualComplexMap_chainInclV {X : TopCat} (U V : Set X) :
    dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V))) (singularChains ℤ (TopCat.of V))
      (chainInclV U V)
      = dualChainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of V) (inclUVV U V) := by
  rw [chainInclV_eq_chainMap]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  rfl

/-- The first component of `mvCochainG` is the dual of `chainInclU`. -/
lemma biprod_inl_mvCochainG {X : TopCat} (U V : Set X) :
    (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V) ≫ mvCochainG U V
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of U)) (chainInclU U V) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, mvCochainG_inl]

/-- The second component of `mvCochainG` is the dual of `chainInclV`. -/
lemma biprod_inr_mvCochainG {X : TopCat} (U V : Set X) :
    (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V) ≫ mvCochainG U V
      = dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of V)) (chainInclV U V) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, mvCochainG_inr]

abbrev bandSSet : SSet := TopCat.toSSet.obj bandW

/-- The `0`-simplex of the band corresponding to the north pole. -/
noncomputable abbrev sP0 : bandSSet _⦋0⦌ :=
  (TopCat.toSSetObj₀Equiv (X := bandW)).symm bP

/-- The `0`-simplex of the band corresponding to the south pole. -/
noncomputable abbrev sQ0 : bandSSet _⦋0⦌ :=
  (TopCat.toSSetObj₀Equiv (X := bandW)).symm bQ

abbrev WU : TopCat := TopCat.of ↥(capA 1)
abbrev WV : TopCat := TopCat.of ↥(capB 1)
abbrev WUV : TopCat := bandW

/-! ### The Mayer–Vietoris degree zero maps, concretely -/

abbrev WcoU : CochainComplex (ModuleCat ℤ) ℕ := cochainU (capA 1) (capB 1)
abbrev WcoV : CochainComplex (ModuleCat ℤ) ℕ := cochainV (capA 1) (capB 1)
abbrev WcoD : CochainComplex (ModuleCat ℤ) ℕ := cochainUV (capA 1) (capB 1)

abbrev WcoD2 := SSetCochainComplex ℤ bandSSet

abbrev WG0 : (WcoU ⊞ WcoV).homology 0 ⟶ WcoD2.homology 0 :=
  HomologicalComplex.homologyMap (mvCochainG (capA 1) (capB 1)) 0

theorem homologyMap_biprod_total (k : ℕ) :
    HomologicalComplex.homologyMap (biprod.fst : WcoU ⊞ WcoV ⟶ WcoU) k
        ≫ HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) k
      + HomologicalComplex.homologyMap (biprod.snd : WcoU ⊞ WcoV ⟶ WcoV) k
        ≫ HomologicalComplex.homologyMap (biprod.inr : WcoV ⟶ WcoU ⊞ WcoV) k
    = 𝟙 ((WcoU ⊞ WcoV).homology k) := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]

theorem WG0_inl (z : ↥(WcoU.homology 0)) :
    WG0.hom ((HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom z)
      = (HomologicalComplex.homologyMap
          (dualChainMap ℤ WUV WU (inclUVU (capA 1) (capB 1))) 0).hom z := by
  have hc : (HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0) ≫ WG0
      = HomologicalComplex.homologyMap
          (dualChainMap ℤ WUV WU (inclUVU (capA 1) (capB 1))) 0 := by
    rw [show WG0 = HomologicalComplex.homologyMap (mvCochainG (capA 1) (capB 1)) 0 from rfl,
      ← HomologicalComplex.homologyMap_comp, biprod_inl_mvCochainG, dualComplexMap_chainInclU]
  rw [show WG0.hom ((HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom z)
      = (ModuleCat.Hom.hom ((HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0)
          ≫ WG0)) z from rfl]
  rw [hc]
  rfl

theorem WG0_inr (z : ↥(WcoV.homology 0)) :
    WG0.hom ((HomologicalComplex.homologyMap (biprod.inr : WcoV ⟶ WcoU ⊞ WcoV) 0).hom z)
      = (HomologicalComplex.homologyMap
          (dualChainMap ℤ WUV WV (inclUVV (capA 1) (capB 1))) 0).hom z := by
  have hc : (HomologicalComplex.homologyMap (biprod.inr : WcoV ⟶ WcoU ⊞ WcoV) 0) ≫ WG0
      = HomologicalComplex.homologyMap
          (dualChainMap ℤ WUV WV (inclUVV (capA 1) (capB 1))) 0 := by
    rw [show WG0 = HomologicalComplex.homologyMap (mvCochainG (capA 1) (capB 1)) 0 from rfl,
      ← HomologicalComplex.homologyMap_comp, biprod_inr_mvCochainG, dualComplexMap_chainInclV]
  rw [show WG0.hom ((HomologicalComplex.homologyMap (biprod.inr : WcoV ⟶ WcoU ⊞ WcoV) 0).hom z)
      = (ModuleCat.Hom.hom ((HomologicalComplex.homologyMap (biprod.inr : WcoV ⟶ WcoU ⊞ WcoV) 0)
          ≫ WG0)) z from rfl]
  rw [hc]
  rfl


/-! ## F. The difference functional on `H⁰` of the band -/

/-- Both poles of the band are in the same component of the cap `capA 1`. -/
lemma pi0_g_UV :
    SSet.π₀.mk ((TopCat.toSSet.map (inclUVU (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sP0)
      = SSet.π₀.mk ((TopCat.toSSet.map (inclUVU (capA 1) (capB 1))).app
          (Opposite.op ⦋0⦌) sQ0) := by
  haveI : ContractibleSpace ↥(capA 1) := contractibleSpace_capA 1
  refine (TopCat.zerothHomotopyEquiv (X := WU)).symm.injective ?_
  exact Subsingleton.elim _ _

/-- Both poles of the band are in the same component of the cap `capB 1`. -/
lemma pi0_g_VV :
    SSet.π₀.mk ((TopCat.toSSet.map (inclUVV (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sP0)
      = SSet.π₀.mk ((TopCat.toSSet.map (inclUVV (capA 1) (capB 1))).app
          (Opposite.op ⦋0⦌) sQ0) := by
  haveI : ContractibleSpace ↥(capB 1) := contractibleSpace_capB 1
  refine (TopCat.zerothHomotopyEquiv (X := WV)).symm.injective ?_
  exact Subsingleton.elim _ _

/-- The module of `0`-cochains of the band. -/
abbrev BandCochain : Type := (bandSSet.chainComplex (ModuleCat.of ℤ ℤ)).X 0 →ₗ[ℤ] ℤ

/-- Evaluation at the north pole, as a functional on `0`-cochains of the band. -/
noncomputable def evP : BandCochain →ₗ[ℤ] ℤ where
  toFun f := f ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1)
  map_add' f g := rfl
  map_smul' a f := rfl

/-- Evaluation at the south pole, as a functional on `0`-cochains of the band. -/
noncomputable def evQ : BandCochain →ₗ[ℤ] ℤ where
  toFun f := f ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1)
  map_add' f g := rfl
  map_smul' a f := rfl

/-- The difference of the evaluations at the two poles. -/
noncomputable def PhiCochain : BandCochain →ₗ[ℤ] ℤ := evP - evQ

theorem PhiCochain_apply (f : BandCochain) :
    PhiCochain f = f ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1)
      - f ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1) := by
  rw [PhiCochain, LinearMap.sub_apply]
  rfl

/-- The composition `C⁰ ⟶ ℤ` used to define `Φ`. -/
noncomputable def PhiK : (SSetCochainComplex ℤ bandSSet).cycles 0 ⟶ ModuleCat.of ℤ ℤ :=
  (SSetCochainComplex ℤ bandSSet).iCycles 0 ≫ ModuleCat.ofHom PhiCochain

theorem PhiK_apply (z : (SSetCochainComplex ℤ bandSSet).cycles 0) :
    PhiK.hom z = PhiCochain (((SSetCochainComplex ℤ bandSSet).iCycles 0).hom z) := by
  rw [PhiK, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rfl

theorem PhiK_toCycles : (SSetCochainComplex ℤ bandSSet).toCycles
    ((ComplexShape.up ℕ).prev 0) 0 ≫ PhiK = 0 := by
  have hz : (SSetCochainComplex ℤ bandSSet).toCycles ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
    HomologicalComplex.toCycles_eq_zero (K := SSetCochainComplex ℤ bandSSet)
      (i := (ComplexShape.up ℕ).prev 0) (j := 0) (by simp [ComplexShape.up_Rel])
  rw [hz, zero_comp]

/-- The map `H⁰(band) → ℤ` induced by the difference of the two evaluations. -/
noncomputable def Phi : WcoD2.homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  descH ℤ bandSSet 0 PhiK PhiK_toCycles

/-- The value of `Φ` on the class of a cocycle. -/
theorem Phi_classOf (α : Cochain ℤ bandSSet 0) (h : cochainDiff ℤ bandSSet α = 0) :
    Phi.hom (cohomologyClassOf ℤ bandSSet α h) = PhiCochain α := by
  have hkey : (SSetCochainComplex ℤ bandSSet).homologyπ 0 ≫ Phi = PhiK := by
    unfold Phi
    exact homologyπ_descH ℤ bandSSet 0 _ _
  have h2 := congrArg (fun (k : (SSetCochainComplex ℤ bandSSet).cycles 0 ⟶ ModuleCat.of ℤ ℤ) =>
    k.hom (cocycleOf ℤ bandSSet α h)) hkey
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [PhiK_apply, iCycles_cocycleOf] at h2
  exact h2

theorem PhiCochain_unit : PhiCochain (unitCochain ℤ bandSSet) = 0 := by
  rw [PhiCochain_apply,
    show (unitCochain ℤ bandSSet) ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1)
      = 1 from genEval_unitCochain ℤ bandSSet sP0,
    show (unitCochain ℤ bandSSet) ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1)
      = 1 from genEval_unitCochain ℤ bandSSet sQ0,
    sub_self]

/-- `Φ` kills the class of the augmentation. -/
theorem Phi_one : Phi.hom (oneH ℤ bandSSet) = 0 := by
  rw [oneH, Phi_classOf, PhiCochain_unit]

theorem PhiCochain_indic : PhiCochain indic = 1 := by
  rw [PhiCochain_apply,
    show indic ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1) = 1 from indic_bP,
    show indic ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1) = 0 from indic_bQ,
    sub_zero]

/-- `Φ` is surjective. -/
theorem Phi_indic : Phi.hom (cohomologyClassOf ℤ bandSSet indic indic_cocycle) = 1 := by
  rw [Phi_classOf, PhiCochain_indic]

theorem Phi_smul_indic (y : ℤ) :
    Phi.hom (y • (cohomologyClassOf ℤ bandSSet indic indic_cocycle)) = y := by
  have h1 : Phi.hom (y • (cohomologyClassOf ℤ bandSSet indic indic_cocycle))
      = y • Phi.hom (cohomologyClassOf ℤ bandSSet indic indic_cocycle) :=
    Phi.hom.toAddMonoidHom.map_zsmul y _
  rw [h1, Phi_indic, smul_eq_mul, mul_one]

theorem Phi_surjective : Function.Surjective Phi.hom := fun y =>
  ⟨y • (cohomologyClassOf ℤ bandSSet indic indic_cocycle), Phi_smul_indic y⟩

/-! ## G. The difference functional kills the Mayer–Vietoris image -/

/-- Evaluation of a scalar multiple of a cochain at a simplex. -/
theorem genEval_zsmul {X : SSet} {n : ℕ} (c : ℤ) (f : Cochain ℤ X n) (s : X _⦋n⦌) :
    genEval ℤ X (c • f) s = c • genEval ℤ X f s := by
  rw [genEval, genEval, LinearMap.smul_apply]

/-- Evaluation of the pullback of a cochain of `U` at the north pole of the band. -/
theorem dualMap_apply_SP (α : Cochain ℤ (TopCat.toSSet.obj WU) 0) :
    (((SSet.chainComplexMap (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α)
      ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1)
    = genEval ℤ (TopCat.toSSet.obj WU) α
        ((TopCat.toSSet.map (inclUVU (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sP0) := by
  rw [LinearMap.dualMap_apply]
  have hnat : ((SSet.chainComplexMap (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ)).f 0).hom
      ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1)
      = ((TopCat.toSSet.obj WU).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map (inclUVU (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sP0)).hom 1 :=
    congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ) sP0)
  rw [hnat]
  rfl

/-- Evaluation of the pullback of a cochain of `U` at the south pole of the band. -/
theorem dualMap_apply_SQ (α : Cochain ℤ (TopCat.toSSet.obj WU) 0) :
    (((SSet.chainComplexMap (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α)
      ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1)
    = genEval ℤ (TopCat.toSSet.obj WU) α
        ((TopCat.toSSet.map (inclUVU (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sQ0) := by
  rw [LinearMap.dualMap_apply]
  have hnat : ((SSet.chainComplexMap (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ)).f 0).hom
      ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1)
      = ((TopCat.toSSet.obj WU).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map (inclUVU (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sQ0)).hom 1 :=
    congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ) sQ0)
  rw [hnat]
  rfl

/-- The pullback to the band of a class coming from `U` pairs to zero with the difference
functional. -/
theorem Phi_pullback_U (z : ↥(WcoU.homology 0)) :
    Phi.hom (WG0.hom ((HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom z))
      = 0 := by
  rw [WG0_inl]
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj WU) 0 z
  rw [singularCohomologyMap_classOf ℤ (inclUVU (capA 1) (capB 1)) α hα]
  rw [Phi_classOf, PhiCochain_apply, sub_eq_zero]
  rw [dualMap_apply_SP, dualMap_apply_SQ]
  exact genEval_congr_of_pi0 hα pi0_g_UV

/-- The pullback to the band of a class coming from `V` pairs to zero with the difference
functional. -/
theorem Phi_pullback_V (z : ↥(WcoV.homology 0)) :
    Phi.hom (WG0.hom ((HomologicalComplex.homologyMap (biprod.inr : WcoV ⟶ WcoU ⊞ WcoV) 0).hom z))
      = 0 := by
  rw [WG0_inr]
  obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj WV) 0 z
  rw [singularCohomologyMap_classOf ℤ (inclUVV (capA 1) (capB 1)) α hα]
  rw [Phi_classOf, PhiCochain_apply, sub_eq_zero]
  rw [show (((SSet.chainComplexMap (TopCat.toSSet.map (inclUVV (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α)
      ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1)
      = genEval ℤ (TopCat.toSSet.obj WV) α
          ((TopCat.toSSet.map (inclUVV (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sP0) from by
    rw [LinearMap.dualMap_apply]
    have hnat : ((SSet.chainComplexMap (TopCat.toSSet.map (inclUVV (capA 1) (capB 1)))
          (ModuleCat.of ℤ ℤ)).f 0).hom
        ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sP0).hom 1)
        = ((TopCat.toSSet.obj WV).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.map (inclUVV (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sP0)).hom 1 :=
      congrArg (fun k => (ModuleCat.Hom.hom k) 1)
        (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVV (capA 1) (capB 1)))
          (ModuleCat.of ℤ ℤ) sP0)
    rw [hnat]
    rfl]
  rw [show (((SSet.chainComplexMap (TopCat.toSSet.map (inclUVV (capA 1) (capB 1)))
        (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap α)
      ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1)
      = genEval ℤ (TopCat.toSSet.obj WV) α
          ((TopCat.toSSet.map (inclUVV (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sQ0) from by
    rw [LinearMap.dualMap_apply]
    have hnat : ((SSet.chainComplexMap (TopCat.toSSet.map (inclUVV (capA 1) (capB 1)))
          (ModuleCat.of ℤ ℤ)).f 0).hom
        ((bandSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) sQ0).hom 1)
        = ((TopCat.toSSet.obj WV).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.map (inclUVV (capA 1) (capB 1))).app (Opposite.op ⦋0⦌) sQ0)).hom 1 :=
      congrArg (fun k => (ModuleCat.Hom.hom k) 1)
        (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVV (capA 1) (capB 1)))
          (ModuleCat.of ℤ ℤ) sQ0)
    rw [hnat]
    rfl]
  exact genEval_congr_of_pi0 hα pi0_g_VV

/-- **`Φ` kills the image of the Mayer–Vietoris map `G`.** -/
theorem Phi_G0 (x : ↥((WcoU ⊞ WcoV).homology 0)) : Phi.hom (WG0.hom x) = 0 := by
  have hx := congrArg (fun (k : (WcoU ⊞ WcoV).homology 0 ⟶ (WcoU ⊞ WcoV).homology 0) => k.hom x)
    (homologyMap_biprod_total 0)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at hx
  rw [show x = (HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom
        ((HomologicalComplex.homologyMap (biprod.fst : WcoU ⊞ WcoV ⟶ WcoU) 0).hom x)
      + (HomologicalComplex.homologyMap (biprod.inr : WcoV ⟶ WcoU ⊞ WcoV) 0).hom
        ((HomologicalComplex.homologyMap (biprod.snd : WcoU ⊞ WcoV ⟶ WcoV) 0).hom x)
      from hx.symm]
  rw [map_add, map_add, Phi_pullback_U, Phi_pullback_V, add_zero]

/-- The class of the augmentation on `U`. -/
noncomputable abbrev cU : ↥(WcoU.homology 0) :=
  cohomologyClassOf ℤ (TopCat.toSSet.obj WU) (unitCochain ℤ (TopCat.toSSet.obj WU))
    (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj WU))

/-- The class of the augmentation on the band is in the image of `G`. -/
theorem WG0_inl_cU : WG0.hom ((HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom cU)
    = oneH ℤ bandSSet := by
  have h1 : WG0.hom ((HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom cU)
      = (HomologicalComplex.homologyMap
          (dualChainMap ℤ WUV WU (inclUVU (capA 1) (capB 1))) 0).hom cU := WG0_inl cU
  have h2 : (HomologicalComplex.homologyMap
        (dualChainMap ℤ WUV WU (inclUVU (capA 1) (capB 1))) 0).hom cU
      = (HomologicalComplex.homologyMap
          (dualChainMap ℤ WUV WU (inclUVU (capA 1) (capB 1))) 0).hom
          (cohomologyClassOf ℤ (TopCat.toSSet.obj WU) (unitCochain ℤ (TopCat.toSSet.obj WU))
            (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj WU))) := by
    congr 1
  have h3 : (HomologicalComplex.homologyMap
        (dualChainMap ℤ WUV WU (inclUVU (capA 1) (capB 1))) 0).hom
        (cohomologyClassOf ℤ (TopCat.toSSet.obj WU) (unitCochain ℤ (TopCat.toSSet.obj WU))
          (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj WU)))
      = cohomologyClassOf ℤ (TopCat.toSSet.obj WUV)
          (((SSet.chainComplexMap (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
            (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap (unitCochain ℤ (TopCat.toSSet.obj WU)))
          (cochainDiff_dualMap_chainComplexMap ℤ (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
            (unitCochain ℤ (TopCat.toSSet.obj WU)) (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj WU))) :=
    singularCohomologyMap_classOf ℤ (inclUVU (capA 1) (capB 1))
      (unitCochain ℤ (TopCat.toSSet.obj WU)) (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj WU))
  have h4 : cohomologyClassOf ℤ (TopCat.toSSet.obj WUV)
        (((SSet.chainComplexMap (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
          (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap (unitCochain ℤ (TopCat.toSSet.obj WU)))
        (cochainDiff_dualMap_chainComplexMap ℤ (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))
          (unitCochain ℤ (TopCat.toSSet.obj WU)) (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj WU)))
      = cohomologyClassOf ℤ (TopCat.toSSet.obj WUV) (unitCochain ℤ (TopCat.toSSet.obj WUV))
          (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj WUV)) :=
    cohomologyClassOf_congr ℤ (TopCat.toSSet.obj WUV)
      (unitCochain_dualMap (TopCat.toSSet.map (inclUVU (capA 1) (capB 1)))) _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans rfl)))

theorem bandJoined_gen (s : bandSSet _⦋0⦌) :
    SSet.π₀.mk s = SSet.π₀.mk sP0 ∨ SSet.π₀.mk s = SSet.π₀.mk sQ0 := by
  rcases bandJoined (TopCat.toSSetObj₀Equiv (X := bandW) s) with hj | hj
  · left
    refine pi0_mk_eq_of_joined ?_
    simpa using hj
  · right
    refine pi0_mk_eq_of_joined ?_
    simpa using hj

/-- Any `0`-cocycle on the band which takes the same value at the two poles is a multiple of the
augmentation. -/
theorem eq_smul_unitCochain (α : Cochain ℤ bandSSet 0) (hα : cochainDiff ℤ bandSSet α = 0)
    (h : genEval ℤ bandSSet α sP0 = genEval ℤ bandSSet α sQ0) :
    α = (genEval ℤ bandSSet α sP0) • unitCochain ℤ bandSSet := by
  apply genEval_ext
  intro s
  have hs : genEval ℤ bandSSet α s = genEval ℤ bandSSet α sP0 := by
    rcases bandJoined_gen s with hp | hp
    · rw [genEval_congr_of_pi0 hα hp]
    · rw [genEval_congr_of_pi0 hα hp, ← h]
  rw [hs, genEval_zsmul, genEval_unitCochain, smul_eq_mul, mul_one]

/-- **The kernel of `Φ` is exactly the image of the Mayer–Vietoris map `G`.** -/
theorem ker_Phi : (WG0.hom).range = Phi.hom.ker := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    exact Phi_G0 y
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf ℤ bandSSet 0 x
    rw [Phi_classOf, PhiCochain_apply, sub_eq_zero] at hx
    have hconst : α = (genEval ℤ bandSSet α sP0) • unitCochain ℤ bandSSet := eq_smul_unitCochain α hα hx
    have h'' : cochainDiff ℤ bandSSet ((genEval ℤ bandSSet α sP0) • unitCochain ℤ bandSSet) = 0 := by
      rw [← hconst]; exact hα
    have hcong : cohomologyClassOf ℤ bandSSet α hα
        = cohomologyClassOf ℤ bandSSet ((genEval ℤ bandSSet α sP0) • unitCochain ℤ bandSSet) h'' :=
      cohomologyClassOf_congr ℤ bandSSet hconst hα h''
    have hgoal : (cohomologyClassOf ℤ bandSSet α hα : ↥(WcoD2.homology 0))
        = (genEval ℤ bandSSet α sP0) • oneH ℤ bandSSet := by
      rw [show (cohomologyClassOf ℤ bandSSet α hα : ↥(WcoD2.homology 0))
          = (cohomologyClassOf ℤ bandSSet ((genEval ℤ bandSSet α sP0) • unitCochain ℤ bandSSet) h''
            : ↥(WcoD2.homology 0)) from by rw [hcong]]
      rw [cohomologyClassOf_smul_int]
      rfl
    refine ⟨(genEval ℤ bandSSet α sP0) •
        (HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom cU, ?_⟩
    have h1 : WG0.hom ((genEval ℤ bandSSet α sP0) •
        (HomologicalComplex.homologyMap (biprod.inl : WcoU ⟶ WcoU ⊞ WcoV) 0).hom cU)
        = (genEval ℤ bandSSet α sP0) • oneH ℤ bandSSet :=
      (WG0.hom.toAddMonoidHom.map_zsmul _ _).trans
        (congrArg (fun y => (genEval ℤ bandSSet α sP0) • y) WG0_inl_cU)
    exact h1.trans hgoal.symm

/-! ## H. The Mayer–Vietoris reduction -/

theorem H1_iso_coker : Nonempty (singularCohomology ℤ 1 (sphTop 2) ≅ cokernel WG0) := by
  haveI hA : ContractibleSpace ↥(capA 1) := contractibleSpace_capA 1
  haveI hB : ContractibleSpace ↥(capB 1) := contractibleSpace_capB 1
  haveI hb : IsZero ((WcoU ⊞ WcoV).homology 1) :=
    isZero_coh_homology_biprod WcoU WcoV 1 (contractible ℤ WU 0) (contractible ℤ WV 0)
  have hF : HomologicalComplex.homologyMap (mvCochainF (capA 1) (capB 1)) 1 = 0 :=
    IsZero.eq_zero_of_tgt hb _
  haveI hEpi : Epi (mvCohδ (capA 1) (capB 1) 0) := by
    have h := mvCoh_H_exact₁ (capA 1) (capB 1) 0
    have hg : (ShortComplex.mk (mvCohδ (capA 1) (capB 1) 0)
        (HomologicalComplex.homologyMap (mvCochainF (capA 1) (capB 1)) (0 + 1))
        (by
          show mvCohδ (capA 1) (capB 1) 0
            ≫ HomologicalComplex.homologyMap (mvCochainF (capA 1) (capB 1)) (0 + 1) = 0
          exact (mvCochainSES (capA 1) (capB 1)).δ_comp 0 1 (by simp [ComplexShape.up]))).g = 0 := hF
    exact (ShortComplex.exact_iff_epi _ hg).1 h
  have hrange : (WG0.hom).range = (mvCohδ (capA 1) (capB 1) 0).hom.ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker
      (ShortComplex.mk (HomologicalComplex.homologyMap (mvCochainG (capA 1) (capB 1)) 0)
        (mvCohδ (capA 1) (capB 1) 0)
        (by
          show HomologicalComplex.homologyMap (mvCochainG (capA 1) (capB 1)) 0
            ≫ mvCohδ (capA 1) (capB 1) 0 = 0
          exact (mvCochainSES (capA 1) (capB 1)).comp_δ 0 1 (by simp [ComplexShape.up])))).1
      (mvCoh_H_exact₃ (capA 1) (capB 1) 0)
  have hsurj : Function.Surjective (mvCohδ (capA 1) (capB 1) 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp hEpi
  obtain ⟨e⟩ := cohSmallIso (X := sphTop 2) (capA 1) (capB 1) (isOpen_capA 1) (isOpen_capB 1)
    (capA_union_capB 1) 1
  refine ⟨e ≪≫ ?_⟩
  exact (LinearEquiv.toModuleIso
      (LinearMap.quotKerEquivOfSurjective (mvCohδ (capA 1) (capB 1) 0).hom hsurj)).symm
    ≪≫ LinearEquiv.toModuleIso (Submodule.quotEquivOfEq _ _ hrange.symm)
    ≪≫ (ModuleCat.cokernelIsoRangeQuotient WG0).symm

theorem coker_G0_iso : Nonempty (cokernel WG0 ≅ ModuleCat.of ℤ ℤ) :=
  ⟨(ModuleCat.cokernelIsoRangeQuotient WG0)
    ≪≫ LinearEquiv.toModuleIso (Submodule.quotEquivOfEq _ _ ker_Phi)
    ≪≫ LinearEquiv.toModuleIso (LinearMap.quotKerEquivOfSurjective Phi.hom Phi_surjective)⟩

end Sph1

/-- **`H¹(S¹; ℤ) ≅ ℤ`** — the base case of the computation of the cohomology of the spheres. -/
theorem sphereCohomologyOne :
    Nonempty (Work.Cohomology.singularCohomology ℤ 1 (Work.Cohomology.sphTop 2)
      ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e1⟩ := Sph1.H1_iso_coker
  obtain ⟨e2⟩ := Sph1.coker_G0_iso
  exact ⟨e1 ≪≫ e2⟩

end

end Work.Cohomology
