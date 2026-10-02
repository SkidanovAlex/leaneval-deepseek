import Mathlib
import Submission.Work.Serre.coneBotSetup
import Submission.Work.Serre.coneBotVal
import Submission.Work.Thom.CohMap_oneH
import Submission.Work.Thom.oneH_generates_rat
import Submission.Work.StemsB.RelCohMapPairHomotopyR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

variable {X B : Type} [TopologicalSpace X] [TopologicalSpace B]

/-- **Pullback fixes the unit class `1 ∈ H⁰(−;ℚ)`** (the `ℚ`-version of `Work.Thom.CohMap_oneH`). -/
theorem CohMap_oneH_rat {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (Work.Thom.CohMap f ℚ 0).hom (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of Y)))
      = Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X)) := by
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) 0))
      (Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of Y))
        (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y)))
        (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y))))
    = Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj (TopCat.of X)))
        (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj (TopCat.of X)))
  rw [Work.Cohomology.singularCohomologyMap_classOf (X := TopCat.of X) (Y := TopCat.of Y) ℚ
      (TopCat.ofHom f) (n := 0) (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y)))
      (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj (TopCat.of Y)))]
  exact Work.Cohomology.cohomologyClassOf_congr ℚ (TopCat.toSSet.obj (TopCat.of X))
    (Work.Thom.chainComplexMap_unitCochain (R := ℚ) (TopCat.toSSet.map (TopCat.ofHom f))) _ _

/-- **The bottom homeomorphism of the two cone-fibres is the restriction of `pathPsiFibre`.** -/
theorem apart_pathPsiFibre {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    Work.RatHurewicz.apart (pathPsiFibre q p t)
        (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
        (pathPsiFibre_mapsTo_bot q p t)
      = (coneBotHomeo q p t : C(↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t),
          ↥(coneFibreBot q (p t)))) := by
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  apply Subtype.ext
  exact (coneBotVal q p t a).symm

/-- **Any two maps into a contractible space are homotopic.** -/
theorem homotopic_of_contractible {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit Y
  have hconst : hv.invFun.comp hv.toFun = ContinuousMap.const Y (hv.invFun ()) := by
    ext y
    exact congrArg hv.invFun (Subsingleton.elim _ _)
  have h0 : (hv.invFun.comp hv.toFun).Homotopic (ContinuousMap.id Y) := hv.left_inv
  rw [hconst] at h0
  have h1 : (ContinuousMap.id Y).Homotopic (ContinuousMap.const Y (hv.invFun ())) := h0.symm
  have hf : f.Homotopic (ContinuousMap.const X (hv.invFun ())) := by
    have h := h1.comp (ContinuousMap.Homotopic.refl f)
    simpa using h
  have hg : g.Homotopic (ContinuousMap.const X (hv.invFun ())) := by
    have h := h1.comp (ContinuousMap.Homotopic.refl g)
    simpa using h
  exact hf.trans hg.symm

/-- **The comparison is injective in degrees `≥ 2`.** -/
theorem coneFibreComparison_ge_two (q : C(X, B)) (p : C(unitInterval, B))
    (m : ℕ) (hm : 1 ≤ m) (t : unitInterval) :
    Function.Injective ((Work.Thom.relCohMap (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t)
      (coneFibreBot q (p t)) (pathPsiFibre_mapsTo_bot q p t) ℚ (m + 1)).hom) := by
  haveI hZc : ContractibleSpace ↥(coneFibre (Work.StemsB.pullbackSnd q p) t) :=
    Work.Serre.DiscPair.cylRetractPreimageContractible (Work.StemsB.pullbackSnd q p) t
  haveI hZc' : ContractibleSpace ↥(coneFibre q (p t)) :=
    Work.Serre.DiscPair.cylRetractPreimageContractible q (p t)
  have hZa : Work.Serre.RatAcyclic ↥(coneFibre (Work.StemsB.pullbackSnd q p) t) :=
    Work.Serre.ratAcyclic_of_contractible _
  have hZa' : Work.Serre.RatAcyclic ↥(coneFibre q (p t)) :=
    Work.Serre.ratAcyclic_of_contractible _
  have h1 : IsZero (Work.Thom.Coh ℚ m ↥(coneFibre (Work.StemsB.pullbackSnd q p) t)) :=
    Work.Serre.isZero_coh_of_ratAcyclic hZa (by omega)
  have h2 : IsZero (Work.Thom.Coh ℚ (m + 1) ↥(coneFibre (Work.StemsB.pullbackSnd q p) t)) :=
    Work.Serre.isZero_coh_of_ratAcyclic hZa (by omega)
  have h1' : IsZero (Work.Thom.Coh ℚ m ↥(coneFibre q (p t))) :=
    Work.Serre.isZero_coh_of_ratAcyclic hZa' (by omega)
  have h2' : IsZero (Work.Thom.Coh ℚ (m + 1) ↥(coneFibre q (p t))) :=
    Work.Serre.isZero_coh_of_ratAcyclic hZa' (by omega)
  have hA : IsIso (Work.Thom.CohMap (Work.RatHurewicz.apart (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
      (pathPsiFibre_mapsTo_bot q p t)) ℚ m) := by
    rw [apart_pathPsiFibre q p t]
    exact Work.RatHurewicz.isIso_cohMap_homeo (coneBotHomeo q p t) m
  haveI : IsIso (Work.Thom.relCohMap (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t)
      (coneFibreBot q (p t)) (pathPsiFibre_mapsTo_bot q p t) ℚ (m + 1)) :=
    Work.RatHurewicz.isIso_relCohMap_of_pairDelta
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
      (pathPsiFibre q p t) (pathPsiFibre_mapsTo_bot q p t) m h1 h2 h1' h2' hA
  exact ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1

/-- **The comparison is injective in degree one.** -/
theorem coneFibreComparison_one (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    Function.Injective ((Work.Thom.relCohMap (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t)
      (coneFibreBot q (p t)) (pathPsiFibre_mapsTo_bot q p t) ℚ 1).hom) := by
  haveI hZc : ContractibleSpace ↥(coneFibre (Work.StemsB.pullbackSnd q p) t) :=
    Work.Serre.DiscPair.cylRetractPreimageContractible (Work.StemsB.pullbackSnd q p) t
  haveI hZc' : ContractibleSpace ↥(coneFibre q (p t)) :=
    Work.Serre.DiscPair.cylRetractPreimageContractible q (p t)
  have hZ'1 : IsZero (Work.Thom.Coh ℚ 1 ↥(coneFibre q (p t))) :=
    Work.Serre.isZero_coh_of_ratAcyclic (Work.Serre.ratAcyclic_of_contractible _) (by norm_num)
  have hδ'surj : Function.Surjective
      (Work.Cohomology.pairδ ℚ (TopCat.of ↥(coneFibre q (p t)))
        (coneFibreBot q (p t)) 0).hom := by
    have hepi : Epi (Work.Cohomology.pairδ ℚ (TopCat.of ↥(coneFibre q (p t)))
        (coneFibreBot q (p t)) 0) := by
      have hg : (ShortComplex.mk
          (Work.Cohomology.pairδ ℚ (TopCat.of ↥(coneFibre q (p t))) (coneFibreBot q (p t)) 0)
          (HomologicalComplex.homologyMap
            (Work.Cohomology.relIncl ℚ (TopCat.of ↥(coneFibre q (p t)))
              (coneFibreBot q (p t))) 1)
          (Work.Cohomology.pairδ_comp ℚ (TopCat.of ↥(coneFibre q (p t)))
            (coneFibreBot q (p t)) 0)).g = 0 :=
        hZ'1.eq_of_tgt _ 0
      exact (ShortComplex.exact_iff_epi _ hg).mp
        (Work.Cohomology.pair_exact₁ ℚ (TopCat.of ↥(coneFibre q (p t)))
          (coneFibreBot q (p t)) 0)
    exact (ModuleCat.epi_iff_surjective _).mp hepi
  -- exactness: the kernel of the connecting map is the range of the restriction
  have hkerZ : (Work.Thom.CohMap_subtype ℚ
        (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0).hom.range
      = (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ
          (TopCat.of ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))
          (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0)).ker := by
    change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℚ (TopCat.of ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))
        (coneFibreBot (Work.StemsB.pullbackSnd q p) t)) 0)).range = _
    exact ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.pair_exact₃ ℚ (TopCat.of ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))
        (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0)
  have hkerZ' : (Work.Thom.CohMap_subtype ℚ (coneFibreBot q (p t)) 0).hom.range
      = (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ (TopCat.of ↥(coneFibre q (p t)))
          (coneFibreBot q (p t)) 0)).ker := by
    change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℚ (TopCat.of ↥(coneFibre q (p t))) (coneFibreBot q (p t))) 0)).range = _
    exact ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.pair_exact₃ ℚ (TopCat.of ↥(coneFibre q (p t))) (coneFibreBot q (p t)) 0)
  -- the restriction sends the unit class to the unit class
  have honeZ : (Work.Thom.CohMap_subtype ℚ
        (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0).hom
      (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
        ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))) : Work.Thom.Coh ℚ 0
          ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))
      = (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
          ↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t))) : Work.Thom.Coh ℚ 0
            ↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t)) :=
    CohMap_oneH_rat _
  have honeZ' : (Work.Thom.CohMap_subtype ℚ (coneFibreBot q (p t)) 0).hom
      (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of ↥(coneFibre q (p t))))
        : Work.Thom.Coh ℚ 0 ↥(coneFibre q (p t)))
      = (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of ↥(coneFibreBot q (p t))))
        : Work.Thom.Coh ℚ 0 ↥(coneFibreBot q (p t))) :=
    CohMap_oneH_rat _
  -- the restriction to the bottom is injective
  have hψinj : Function.Injective ((Work.Thom.CohMap (Work.RatHurewicz.apart (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
      (pathPsiFibre_mapsTo_bot q p t)) ℚ 0).hom) := by
    rw [apart_pathPsiFibre q p t]
    exact ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (Work.RatHurewicz.isIso_cohMap_homeo (coneBotHomeo q p t) 0)).1
  have hψone : (Work.Thom.CohMap (Work.RatHurewicz.apart (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
      (pathPsiFibre_mapsTo_bot q p t)) ℚ 0).hom
      (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of ↥(coneFibreBot q (p t))))
        : Work.Thom.Coh ℚ 0 ↥(coneFibreBot q (p t)))
      = (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
          ↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t))) : Work.Thom.Coh ℚ 0
            ↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t)) := by
    rw [apart_pathPsiFibre q p t]
    exact CohMap_oneH_rat _
  -- naturality of the connecting map
  have hnat : ∀ y : Work.Thom.Coh ℚ 0 ↥(coneFibreBot q (p t)),
      (Work.Thom.relCohMap (pathPsiFibre q p t)
        (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
        (pathPsiFibre_mapsTo_bot q p t) ℚ 1).hom
        ((Work.Cohomology.pairδ ℚ (TopCat.of ↥(coneFibre q (p t)))
          (coneFibreBot q (p t)) 0).hom y)
      = (Work.Cohomology.pairδ ℚ (TopCat.of ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))
          (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0).hom
        ((Work.Thom.CohMap (Work.RatHurewicz.apart (pathPsiFibre q p t)
          (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
          (pathPsiFibre_mapsTo_bot q p t)) ℚ 0).hom y) :=
    fun y => Work.StemsB.pairDeltaNaturalR ℚ (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
      (pathPsiFibre_mapsTo_bot q p t) 0 y
  intro x y hxy
  obtain ⟨u, rfl⟩ := hδ'surj x
  obtain ⟨v, rfl⟩ := hδ'surj y
  have hker_eq : (Work.Cohomology.pairδ ℚ
      (TopCat.of ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0).hom
      ((Work.Thom.CohMap (Work.RatHurewicz.apart (pathPsiFibre q p t)
        (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
        (pathPsiFibre_mapsTo_bot q p t)) ℚ 0).hom (u - v)) = 0 := by
    rw [map_sub, map_sub, ← hnat u, ← hnat v, hxy, sub_self]
  have hrange_mem : (Work.Thom.CohMap (Work.RatHurewicz.apart (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
      (pathPsiFibre_mapsTo_bot q p t)) ℚ 0).hom (u - v)
      ∈ (Work.Thom.CohMap_subtype ℚ (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0).hom.range := by
    rw [hkerZ]
    exact hker_eq
  obtain ⟨w, hw⟩ := hrange_mem
  obtain ⟨c, hc⟩ := Work.Thom.oneH_generates_rat w
  -- hence `u - v` is a multiple of the unit class of the target
  have huv : u - v = c • (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
      ↥(coneFibreBot q (p t)))) : Work.Thom.Coh ℚ 0 ↥(coneFibreBot q (p t))) := by
    refine hψinj ?_
    rw [← hw]
    calc (Work.Thom.CohMap_subtype ℚ
            (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0).hom w
        = (Work.Thom.CohMap_subtype ℚ
            (coneFibreBot (Work.StemsB.pullbackSnd q p) t) 0).hom
            (c • (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
              ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))) : Work.Thom.Coh ℚ 0
                ↥(coneFibre (Work.StemsB.pullbackSnd q p) t))) := by rw [hc]
      _ = c • (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
              ↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t))) : Work.Thom.Coh ℚ 0
                ↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t)) := by
            rw [map_smul, honeZ]
      _ = (Work.Thom.CohMap (Work.RatHurewicz.apart (pathPsiFibre q p t)
            (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
            (pathPsiFibre_mapsTo_bot q p t)) ℚ 0).hom
            (c • (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
              ↥(coneFibreBot q (p t)))) : Work.Thom.Coh ℚ 0 ↥(coneFibreBot q (p t)))) := by
            rw [map_smul, hψone]
  -- so `δ'(u - v) = 0`
  have hmem' : c • (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
      ↥(coneFibreBot q (p t)))) : Work.Thom.Coh ℚ 0 ↥(coneFibreBot q (p t)))
      ∈ (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ
        (TopCat.of ↥(coneFibre q (p t))) (coneFibreBot q (p t)) 0)).ker := by
    rw [← hkerZ']
    exact ⟨c • (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of
      ↥(coneFibre q (p t)))) : Work.Thom.Coh ℚ 0 ↥(coneFibre q (p t))), by
        rw [map_smul, honeZ']⟩
  have hz : (Work.Cohomology.pairδ ℚ (TopCat.of ↥(coneFibre q (p t)))
      (coneFibreBot q (p t)) 0).hom (u - v) = 0 := by
    rw [huv]
    exact hmem'
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- **The comparison is injective in degree zero**: either the relative set is non-empty, in which
case the source of the comparison is zero, or it is empty on both sides, in which case the two cone
fibres are contractible and any map between them is a homotopy equivalence (indeed, homotopic to
the identity), so that `Work.StemsB.relCohMap_pairHomotopyR` applies with vacuous pair
conditions. -/
theorem coneFibreComparison_zero (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    Function.Injective ((Work.Thom.relCohMap (pathPsiFibre q p t)
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t)
      (coneFibreBot q (p t)) (pathPsiFibre_mapsTo_bot q p t) ℚ 0).hom) := by
  by_cases hB : (coneFibreBot q (p t)).Nonempty
  · haveI hZc' : ContractibleSpace ↥(coneFibre q (p t)) :=
      Work.Serre.DiscPair.cylRetractPreimageContractible q (p t)
    have h0 : IsZero (Work.Thom.RelCoh ℚ 0 ↥(coneFibre q (p t))
        (coneFibreBot q (p t))) :=
      isZeroRelCohomologyZero_rat (TopCat.of ↥(coneFibre q (p t)))
        (coneFibreBot q (p t)) hB
    haveI : Subsingleton (Work.Thom.RelCoh ℚ 0 ↥(coneFibre q (p t))
        (coneFibreBot q (p t))) := ModuleCat.subsingleton_of_isZero h0
    exact fun x y _ => Subsingleton.elim x y
  · have hA : ¬ (coneFibreBot (Work.StemsB.pullbackSnd q p) t).Nonempty := by
      rintro ⟨a, ha⟩
      exact hB ⟨(coneBotHomeo q p t) ⟨a, ha⟩, ((coneBotHomeo q p t) ⟨a, ha⟩).2⟩
    haveI hZc : ContractibleSpace ↥(coneFibre (Work.StemsB.pullbackSnd q p) t) :=
      Work.Serre.DiscPair.cylRetractPreimageContractible (Work.StemsB.pullbackSnd q p) t
    haveI hZc' : ContractibleSpace ↥(coneFibre q (p t)) :=
      Work.Serre.DiscPair.cylRetractPreimageContractible q (p t)
    obtain ⟨hz⟩ := ContractibleSpace.hequiv_unit ↥(coneFibre (Work.StemsB.pullbackSnd q p) t)
    have hg : ∀ y ∈ coneFibreBot q (p t),
        (ContinuousMap.const ↥(coneFibre q (p t)) (hz.invFun ()))
          y ∈ coneFibreBot (Work.StemsB.pullbackSnd q p) t :=
      fun y hy => absurd ⟨y, hy⟩ hB
    have P : ContinuousMap.Homotopy
        ((ContinuousMap.const ↥(coneFibre q (p t)) (hz.invFun ())).comp (pathPsiFibre q p t))
        (ContinuousMap.id ↥(coneFibre (Work.StemsB.pullbackSnd q p) t)) :=
      Classical.choice (homotopic_of_contractible _ _)
    have Q : ContinuousMap.Homotopy
        ((pathPsiFibre q p t).comp (ContinuousMap.const ↥(coneFibre q (p t)) (hz.invFun ())))
        (ContinuousMap.id ↥(coneFibre q (p t))) :=
      Classical.choice (homotopic_of_contractible _ _)
    have hP : ∀ s x, x ∈ coneFibreBot (Work.StemsB.pullbackSnd q p) t →
        P (s, x) ∈ coneFibreBot (Work.StemsB.pullbackSnd q p) t :=
      fun s x hx => absurd ⟨x, hx⟩ hA
    have hQ : ∀ s y, y ∈ coneFibreBot q (p t) → Q (s, y) ∈ coneFibreBot q (p t) :=
      fun s y hy => absurd ⟨y, hy⟩ hB
    refine (Work.StemsB.relCohMap_pairHomotopyR ℚ
      (coneFibreBot (Work.StemsB.pullbackSnd q p) t) (coneFibreBot q (p t))
      (pathPsiFibre q p t) (ContinuousMap.const ↥(coneFibre q (p t)) (hz.invFun ()))
      (pathPsiFibre_mapsTo_bot q p t) hg P hP Q hQ 0).1

/-- **The fibre-pair comparison along a path.**  The map of mapping cylinders induced by the
pullback square of a path restricts, over each `t`, to a map of pairs
`(coneFibre (pullbackSnd q p) t, coneFibreBot (pullbackSnd q p) t) → (coneFibre q (p t),
coneFibreBot q (p t))` which is injective on relative cohomology in every degree.

Route: `coneFibre (pullbackSnd q p) t` is the cone on `{z : Pullback q p // pullbackSnd q p z = t}`
and `pullbackFst q p` is a homeomorphism from this set onto the fibre `q ⁻¹' {p t}` (its inverse is
`x ↦ (x, t)`, using `q x = p t`).  Hence `Work.Serre.pathPsiFibre q p t` is a **homeomorphism of
pairs**: on the cone it is the identity on the interval coordinate and `pullbackFst q p` on the
`X`-coordinate, with the apexes matched (`Work.StemsB.cylMapGen_apply_inl`,
`Work.StemsB.cylMapGen_apply_inr`), and the inverse is the cone on the inverse homeomorphism.
Conclude with `Work.Thom.bijective_relCohMap_of_homeomorphA` (a homeomorphism of pairs induces a
bijective pullback on relative cohomology), transporting a hypothetical inverse along
`Work.Thom.relCohMap_congrA` if needed.  No fibration hypothesis is used. -/
theorem coneFibreComparison {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) (n : ℕ) (t : unitInterval) :
    Function.Injective ((Work.Thom.relCohMap (Work.Serre.pathPsiFibre q p t)
      (Work.Serre.coneFibreBot (Work.StemsB.pullbackSnd q p) t)
      (Work.Serre.coneFibreBot q (p t)) (Work.Serre.pathPsiFibre_mapsTo_bot q p t) ℚ n).hom) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact coneFibreComparison_zero q p t
  · rcases eq_or_lt_of_le (show 1 ≤ n by omega) with h1 | h1
    · subst h1
      exact coneFibreComparison_one q p t
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact coneFibreComparison_ge_two q p m (by omega) t

end

end Work.Serre
