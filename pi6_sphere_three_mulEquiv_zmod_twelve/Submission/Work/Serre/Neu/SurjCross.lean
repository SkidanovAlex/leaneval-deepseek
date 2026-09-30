-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/CrossProduct.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.SurjSetup2
import Submission.Work.Serre.Surj.tpMapDzCokerTorsion
import Submission.Work.Serre.Surj.homologyMapBaseChangeSurjective
import Submission.Work.Serre.Neu.SurjDZ
import Submission.Work.Serre.Surj.ratCycleExists
import Submission.Work.Serre.Neu.RelEZMap
import Submission.Work.Serre.crossProduct_coker_rat

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology

/-- The value of `dzMap` on the generator cycle of the coefficient complex. -/
theorem dzMap_iCycles_dzGenCycle (r : ℕ) (D : ChainComplex (ModuleCat ℤ) ℕ)
    (z : ↥(D.cycles (r + 1))) :
    (ModuleCat.Hom.hom ((Work.Serre.dzMap r D z).f (r + 1)))
        ((ModuleCat.Hom.hom ((Work.Serre.dzComplex r).iCycles (r + 1))) (dzGenCycle r))
      = (ModuleCat.Hom.hom (D.iCycles (r + 1))) z := by
  rw [iCycles_dzGenCycle, Work.Serre.dzMap_f_self_apply, Work.Kunneth.homIso_hom_apply,
    LinearMap.toSpanSingleton_apply_one]

/-- **The value of `tpMap` on the cross product with the generator cycle.** -/
theorem tpMap_iCycles_crossCycTensElem (W : Type) [TopologicalSpace W] (P : Type)
    [TopologicalSpace P] (Q : Set P) (r m : ℕ)
    (w : ↥((singularChains ℤ (TopCat.of W)).cycles m))
    (z : ↥((relChains (TopCat.of P) Q).cycles (r + 1))) :
    (ModuleCat.Hom.hom ((Work.Kunneth.tpMap (singularChains ℤ (TopCat.of W))
        (singularChains ℤ (TopCat.of W)) (Work.Serre.dzComplex r)
        (relChains (TopCat.of P) Q) (CategoryTheory.CategoryStruct.id _)
        (Work.Serre.dzMap r (relChains (TopCat.of P) Q) z)).f (m + r + 1)))
      ((ModuleCat.Hom.hom ((Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
          (Work.Serre.dzComplex r)).iCycles (m + r + 1)))
        (Work.Kunneth.crossCycTens (singularChains ℤ (TopCat.of W)) (Work.Serre.dzComplex r)
          (m + r + 1) m (r + 1) rfl (TensorProduct.tmul ℤ w (dzGenCycle r))))
    = (ModuleCat.Hom.hom ((Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
        (relChains (TopCat.of P) Q)).iCycles (m + r + 1)))
      (Work.Serre.crossCycTensElem W P Q m (r + 1) w z) := by
  rw [Work.Kunneth.iCycles_crossCycTens_tmul, Work.Kunneth.tpMap_tmul, dzMap_iCycles_dzGenCycle]
  simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rw [show Work.Serre.crossCycTensElem W P Q m (r + 1) w z
      = Work.Kunneth.crossCycTens (singularChains ℤ (TopCat.of W))
          (relChains (TopCat.of P) Q) (m + r + 1) m (r + 1) rfl
          (TensorProduct.tmul ℤ w z) from rfl]
  rw [Work.Kunneth.iCycles_crossCycTens_tmul]

/-- **The rational cross product with the generating cycle is surjective, with its values on cycle
classes.** -/
theorem crossProductQ (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (Q : Set P) (r N : ℕ)
    (z : ↥((relChains (TopCat.of P) Q).cycles (r + 1)))
    (vtz : ↥((singularChains ℤ (TopCat.of P)).X (r + 1)))
    (hvtz : (ModuleCat.Hom.hom ((relChainsProj (TopCat.of P) Q).f (r + 1))) vtz
      = (ModuleCat.Hom.hom ((relChains (TopCat.of P) Q).iCycles (r + 1))) z)
    (hzt : TensorProduct.tmul ℤ ((ModuleCat.Hom.hom
      ((relChains (TopCat.of P) Q).homologyπ (r + 1))) z) (1 : ℚ) ≠ 0)
    (hvanZ : ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 → Subsingleton
      (TensorProduct ℤ ↥((relChains (TopCat.of P) Q).homology j) ℚ))
    (hgenZ : ∀ w : ↥((relChains (TopCat.of P) Q).homology (r + 1)),
      ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
        TensorProduct.tmul ℤ (n • w) (1 : ℚ)
          = TensorProduct.tmul ℤ (m • ((ModuleCat.Hom.hom
              ((relChains (TopCat.of P) Q).homologyπ (r + 1))) z)) (1 : ℚ))
    (m : ℕ) (hm : m + r + 1 ≤ N + 1) :
    ∃ T : (singularChains ℚ (TopCat.of W)).homology m ⟶
        (relBBA_rat W P Q).homology (m + r + 1),
      Function.Surjective T.hom ∧
      (∀ u : ↥((singularChains ℚ (TopCat.of W)).cycles m),
        ∃ c : ↥((relBBA_rat W P Q).cycles (m + r + 1)),
          (Work.StemsB.rdRProj ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
              (Work.Serre.shufRat W P m (r + 1)
                ((ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).iCycles m)) u)
                (vt0Of P r vtz))
            = (ModuleCat.Hom.hom ((relBBA_rat W P Q).iCycles (m + r + 1))) c
          ∧ T.hom ((ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).homologyπ m)) u)
              = (ModuleCat.Hom.hom ((relBBA_rat W P Q).homologyπ (m + r + 1))) c) := by
  have hznt := Work.Serre.z_chain_not_torsion (relChains (TopCat.of P) Q) r z hzt
  have hfree : ∀ i, Module.Free ℤ
      ↥((singularChains ℤ (TopCat.of W)).X i) := fun i => singularChains_free _ i
  have hcoker := Work.Serre.Surj.tpMapDzCokerTorsion (singularChains ℤ (TopCat.of W))
    (relChains (TopCat.of P) Q) hfree r N z hznt hvanZ hgenZ
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.StemsB.IntRatCM.map (Work.Kunneth.tpMap (singularChains ℤ (TopCat.of W))
        (singularChains ℤ (TopCat.of W)) (dzComplex r) (relChains (TopCat.of P) Q)
        (CategoryTheory.CategoryStruct.id _) (dzMap r (relChains (TopCat.of P) Q) z)))
      (m + r + 1)).hom :=
    Work.Serre.Surj.homologyMapBaseChangeSurjective _ _ _ _ (hcoker (m + r + 1) hm)
  obtain ⟨e, heprop⟩ := Work.Serre.Surj.dzTpShiftQ (singularChains ℤ (TopCat.of W)) r m
  obtain ⟨EZ, hEZiso, hEZrule⟩ := Work.Serre.relEZMap W P Q
  haveI hEZn : IsIso (HomologicalComplex.homologyMap EZ (m + r + 1)) := hEZiso (m + r + 1)
  have hsurjEZ : Function.Surjective (HomologicalComplex.homologyMap
      (Work.StemsB.IntRatCM.map EZ) (m + r + 1)).hom :=
    Work.Serre.Surj.homologyMapBaseChangeSurjective _ _ EZ (m + r + 1)
      (Work.Serre.Surj.subsingleton_coker_tensor_of_isIso
        (HomologicalComplex.homologyMap EZ (m + r + 1)))
  haveI hrelIso : IsIso (HomologicalComplex.homologyMap
      (bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).hom (m + r + 1)) := by
    rw [← HomologicalComplex.homologyMapIso_hom
      (bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}) (m + r + 1)]
    infer_instance
  have hsurjLast : Function.Surjective (HomologicalComplex.homologyMap
      (Work.StemsB.IntRatCM.map EZ ≫
        (bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).hom) (m + r + 1)).hom := by
    rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
    exact ((ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (bcRel (TopCat.of (W × P))
        {x : W × P | x.2 ∈ Q}).hom (m + r + 1))).mp inferInstance).comp hsurjEZ
  let a : (singularChains ℚ (TopCat.of W)).homology m ⟶
      (Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).homology m :=
    ((asIso (HomologicalComplex.homologyMap (bcAbs W).hom m)).symm).hom
  let c : (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
      (dzComplex r))).homology (m + r + 1) ⟶
      (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
        (relChains (TopCat.of P) Q))).homology (m + r + 1) :=
    HomologicalComplex.homologyMap (Work.StemsB.IntRatCM.map (Work.Kunneth.tpMap
      (singularChains ℤ (TopCat.of W)) (singularChains ℤ (TopCat.of W)) (dzComplex r)
      (relChains (TopCat.of P) Q) (CategoryTheory.CategoryStruct.id _)
      (dzMap r (relChains (TopCat.of P) Q) z))) (m + r + 1)
  let d : (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
      (relChains (TopCat.of P) Q))).homology (m + r + 1) ⟶
      (relBBA_rat W P Q).homology (m + r + 1) :=
    HomologicalComplex.homologyMap (Work.StemsB.IntRatCM.map EZ ≫
      (bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).hom) (m + r + 1)
  have hsurjc : Function.Surjective c.hom := hsurj
  have hsurjd : Function.Surjective d.hom := hsurjLast
  have ha : Function.Surjective a.hom :=
    (ModuleCat.epi_iff_surjective a).mp inferInstance
  have he : Function.Surjective (e.hom).hom :=
    (ModuleCat.epi_iff_surjective e.hom).mp inferInstance
  refine ⟨a ≫ e.hom ≫ c ≫ d, ?_, ?_⟩
  · intro y
    obtain ⟨z1, hz1⟩ := hsurjd y
    obtain ⟨z2, hz2⟩ := hsurjc z1
    obtain ⟨z3, hz3⟩ := he z2
    obtain ⟨x, hx⟩ := ha z3
    refine ⟨x, ?_⟩
    rw [show (a ≫ e.hom ≫ c ≫ d).hom
        = d.hom.comp (c.hom.comp ((e.hom).hom.comp a.hom)) from by
      simp only [ModuleCat.hom_comp, LinearMap.comp_assoc]]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hx, hz3, hz2, hz1]
  · intro u
    set u' : ↥((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).cycles m) :=
      (HomologicalComplex.cyclesMap (bcAbs W).inv m).hom u with hu'def
    have hcyc_u' : (ModuleCat.Hom.hom
        ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).iCycles m)) u'
        = (ModuleCat.Hom.hom ((bcAbs W).inv.f m))
            ((ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).iCycles m)) u) := by
      rw [hu'def]
      exact Work.Serre.Surj.iCycles_cyclesMap_q _ _ (bcAbs W).inv m u
    have hbck : (ModuleCat.Hom.hom ((bcAbs W).hom.f m))
        ((ModuleCat.Hom.hom
          ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).iCycles m)) u')
        = (ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).iCycles m)) u := by
      have h2 : (ModuleCat.Hom.hom ((bcAbs W).hom.f m)).comp
          (ModuleCat.Hom.hom ((bcAbs W).inv.f m)) = LinearMap.id := by
        have h := congrArg (fun (g : singularChains ℚ (TopCat.of W) ⟶
            singularChains ℚ (TopCat.of W)) => (ModuleCat.Hom.hom (g.f m)))
          (Iso.inv_hom_id (bcAbs W))
        simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_id,
          HomologicalComplex.id_f] using h
      rw [hcyc_u']
      exact congrArg (fun (g : ↥((singularChains ℚ (TopCat.of W)).X m) →ₗ[ℚ]
          ↥((singularChains ℚ (TopCat.of W)).X m)) =>
            g ((ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).iCycles m)) u)) h2
    obtain ⟨q, w, hw⟩ := Work.Serre.Surj.ratCycleExists (singularChains ℤ (TopCat.of W)) m u'
    have hu_shuf : (ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).iCycles m)) u
        = q • (ModuleCat.Hom.hom ((bcAbs W).hom.f m))
            (TensorProduct.tmul ℤ (1 : ℚ)
              ((ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of W)).iCycles m)) w)) := by
      rw [← hbck, hw, map_smul]
    have hL := Work.Serre.Surj.shuffleProjection W P Q r m z vtz hvtz w q u hu_shuf
    obtain ⟨x, y, hx, hy, hexy⟩ := heprop w
    have hy' := hy
    have hexy' : (ModuleCat.Hom.hom e.hom)
        ((ModuleCat.Hom.hom
          ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).homologyπ m)) x)
        = (ModuleCat.Hom.hom
          ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
            (dzComplex r))).homologyπ (m + r + 1))) y := hexy
    have hu'x : u' = q • x := by
      apply Work.Serre.Surj.cycle_eq_of_iCycles_eq (K := Work.StemsB.IntRatCM.obj
        (singularChains ℤ (TopCat.of W))) (n := m)
      rw [map_smul, hw, hx]
    have hfu' : (HomologicalComplex.cyclesMap (bcAbs W).hom m).hom u' = u := by
      have hcomp : (HomologicalComplex.cyclesMap (bcAbs W).inv m) ≫
          (HomologicalComplex.cyclesMap (bcAbs W).hom m) = 𝟙 _ := by
        rw [← HomologicalComplex.cyclesMap_comp, Iso.inv_hom_id, HomologicalComplex.cyclesMap_id]
      have h := congrArg (fun (g : ((singularChains ℚ (TopCat.of W)).cycles m) ⟶
          ((singularChains ℚ (TopCat.of W)).cycles m)) => (ModuleCat.Hom.hom g) u) hcomp
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] at h
      rwa [← hu'def] at h
    have ha_id' : HomologicalComplex.homologyMap (bcAbs W).hom m ≫ a = 𝟙 _ := by
      show HomologicalComplex.homologyMap (bcAbs W).hom m ≫
        ((asIso (HomologicalComplex.homologyMap (bcAbs W).hom m)).symm).hom = 𝟙 _
      exact Iso.hom_inv_id (asIso (HomologicalComplex.homologyMap (bcAbs W).hom m))
    have hA : (ModuleCat.Hom.hom a)
        ((ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).homologyπ m)) u)
        = q • (ModuleCat.Hom.hom
            ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).homologyπ m)) x := by
      have h1 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (bcAbs W).hom m))
          (q • (ModuleCat.Hom.hom
            ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).homologyπ m)) x)
          = (ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).homologyπ m)) u := by
        have hq : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (bcAbs W).hom m))
            (q • (ModuleCat.Hom.hom
              ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).homologyπ m)) x)
            = q • (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (bcAbs W).hom m))
              ((ModuleCat.Hom.hom
                ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).homologyπ m)) x) := by
          rw [map_smul]
        rw [hq]
        rw [Work.Serre.Surj.homologyMap_homologyπ_q]
        have hq2 : q • (ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).homologyπ m))
              ((HomologicalComplex.cyclesMap (bcAbs W).hom m).hom x)
            = (ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).homologyπ m))
              (q • (HomologicalComplex.cyclesMap (bcAbs W).hom m).hom x) := by
          rw [map_smul]
        rw [hq2]
        have hq3 : q • (HomologicalComplex.cyclesMap (bcAbs W).hom m).hom x
            = (HomologicalComplex.cyclesMap (bcAbs W).hom m).hom (q • x) := by
          rw [map_smul]
        rw [hq3, ← hu'x, hfu']
      rw [← h1]
      have h3 := congrArg (fun (g : (Work.StemsB.IntRatCM.obj
            (singularChains ℤ (TopCat.of W))).homology m ⟶ (Work.StemsB.IntRatCM.obj
            (singularChains ℤ (TopCat.of W))).homology m) =>
          (ModuleCat.Hom.hom g) (q • (ModuleCat.Hom.hom
            ((Work.StemsB.IntRatCM.obj (singularChains ℤ (TopCat.of W))).homologyπ m)) x))
        ha_id'
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using h3
    set CYC : ↥((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
        (relChains (TopCat.of P) Q))).cycles (m + r + 1)) :=
      (HomologicalComplex.cyclesMap (Work.StemsB.IntRatCM.map (Work.Kunneth.tpMap
        (singularChains ℤ (TopCat.of W)) (singularChains ℤ (TopCat.of W)) (dzComplex r)
        (relChains (TopCat.of P) Q) (CategoryTheory.CategoryStruct.id _)
        (dzMap r (relChains (TopCat.of P) Q) z))) (m + r + 1)).hom y with hCYCdef
    set CYC2 : ↥((relBBA_rat W P Q).cycles (m + r + 1)) :=
      (HomologicalComplex.cyclesMap (Work.StemsB.IntRatCM.map EZ ≫
        (bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).hom) (m + r + 1)).hom CYC
      with hCYC2def
    have hc1 : (ModuleCat.Hom.hom c)
        (q • (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC
          (singularChains ℤ (TopCat.of W)) (dzComplex r))).homologyπ (m + r + 1))) y)
        = q • (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC
          (singularChains ℤ (TopCat.of W)) (relChains (TopCat.of P) Q))).homologyπ
            (m + r + 1))) CYC := by
      rw [map_smul, Work.Serre.Surj.homologyMap_homologyπ_q, ← hCYCdef]
    have hd1 : (ModuleCat.Hom.hom d)
        (q • (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC
          (singularChains ℤ (TopCat.of W)) (relChains (TopCat.of P) Q))).homologyπ
            (m + r + 1))) CYC)
        = q • (ModuleCat.Hom.hom ((relBBA_rat W P Q).homologyπ (m + r + 1))) CYC2 := by
      rw [map_smul, Work.Serre.Surj.homologyMap_homologyπ_q, ← hCYC2def]
    have hTval : (ModuleCat.Hom.hom (a ≫ e.hom ≫ c ≫ d))
        ((ModuleCat.Hom.hom ((singularChains ℚ (TopCat.of W)).homologyπ m)) u)
        = q • (ModuleCat.Hom.hom ((relBBA_rat W P Q).homologyπ (m + r + 1))) CYC2 := by
      rw [show (ModuleCat.Hom.hom (a ≫ e.hom ≫ c ≫ d))
          = (d.hom.comp (c.hom.comp ((e.hom).hom.comp a.hom))) from by
        simp only [ModuleCat.hom_comp, LinearMap.comp_assoc]]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      rw [hA]
      rw [show (ModuleCat.Hom.hom e.hom) (q • (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj
            (singularChains ℤ (TopCat.of W))).homologyπ m)) x)
          = q • (ModuleCat.Hom.hom e.hom) ((ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj
            (singularChains ℤ (TopCat.of W))).homologyπ m)) x) from by rw [map_smul]]
      rw [hexy', hc1, hd1]
    have hCYC2 : (ModuleCat.Hom.hom ((relBBA_rat W P Q).iCycles (m + r + 1))) CYC2
        = (ModuleCat.Hom.hom
            ((bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).hom.f (m + r + 1)))
          (TensorProduct.tmul ℤ (1 : ℚ)
            ((ModuleCat.Hom.hom ((relChainsProj (TopCat.of (W × P))
              {x : W × P | x.2 ∈ Q}).f (m + r + 1)))
              (Work.Serre.ezShufChain W P m (r + 1)
                ((ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of W)).iCycles m)) w) vtz))) := by
      have hEZ'' : (ModuleCat.Hom.hom (EZ.f (m + r + 1)))
          ((ModuleCat.Hom.hom ((Work.Kunneth.tpMap (singularChains ℤ (TopCat.of W))
            (singularChains ℤ (TopCat.of W)) (dzComplex r) (relChains (TopCat.of P) Q)
            (CategoryTheory.CategoryStruct.id _)
            (dzMap r (relChains (TopCat.of P) Q) z)).f (m + r + 1)))
            ((ModuleCat.Hom.hom ((Work.Kunneth.tpC (singularChains ℤ (TopCat.of W))
              (dzComplex r)).iCycles (m + r + 1)))
              (Work.Kunneth.crossCycTens (singularChains ℤ (TopCat.of W)) (dzComplex r)
                (m + r + 1) m (r + 1) rfl
                (TensorProduct.tmul ℤ w (dzGenCycle r)))))
          = (ModuleCat.Hom.hom ((relChainsProj (TopCat.of (W × P))
              {x : W × P | x.2 ∈ Q}).f (m + r + 1)))
            (Work.Serre.ezShufChain W P m (r + 1)
              ((ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of W)).iCycles m)) w) vtz) := by
        rw [Work.Serre.Surj.tpMap_iCycles_crossCycTensElem]
        exact hEZrule m (r + 1) w z vtz hvtz
      rw [hCYC2def, hCYCdef]
      simp only [Work.Serre.Surj.iCycles_cyclesMap_q, HomologicalComplex.comp_f,
        ModuleCat.hom_comp, LinearMap.comp_apply, hy', Work.Serre.Surj.IntRatCM_map_tmul]
      refine congrArg (fun (x : ↥((Work.StemsB.IntRatCM.obj (relBBA W P Q)).X (m + r + 1))) =>
        (ModuleCat.Hom.hom ((bcRel (TopCat.of (W × P))
          {x : W × P | x.2 ∈ Q}).hom.f (m + r + 1))) x) ?_
      refine congrArg (fun (x : ↥((relBBA W P Q).X (m + r + 1))) =>
        (TensorProduct.tmul ℤ (1 : ℚ)) x) ?_
      exact hEZ''
    refine ⟨q • CYC2, ?_, ?_⟩
    · rw [hL, map_smul, hCYC2]
    · rw [hTval, map_smul]

end

end Work.Serre.Surj
