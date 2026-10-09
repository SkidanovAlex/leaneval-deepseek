import Mathlib
import Submission.Work.SSGRoute.phi0_defs
import Submission.Work.SSGRoute.phi0_muClassHom_pairing
import Submission.Work.SSGRoute.extHRestrict_comp
import Submission.Work.SSGRoute.extIdele_localisation_injective
import Submission.Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified
import Submission.Work.SSGRoute.exists_finset_unramifiedPlaces
import Submission.Work.SSGRoute.exists_zetaCoeff
import Submission.Work.SSGRoute.e6_util
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E5Route

open SSGRoute.PTExt CategoryTheory NK.GlobalCFT

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

section LevelPlace

/-- The place of `K` below a place of a level `L` (a choice; the value is unique). -/
noncomputable def e5LevelPlaceUnder (L : IntermediateField K Ω) [FiniteDimensional K ↥L]
    (w : NK.GlobalCFT.Place ↥L) : NK.GlobalCFT.Place K :=
  Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w)

theorem e5LevelPlaceUnder_liesOver (L : IntermediateField K Ω) [FiniteDimensional K ↥L]
    (w : NK.GlobalCFT.Place ↥L) :
    NK.GlobalCFT.Place.LiesOver w (e5LevelPlaceUnder (K := K) L w) :=
  Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w)

end LevelPlace

/-- The localisation at `w` of the image of a units-class under `Lˣ → 𝕀_L` is its localisation. -/
theorem e5_loc_ideleIncl_comp (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) (a : extH (unitsK k L) 2) :
    (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w)
        (a.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k L)) (add_zero 2))).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero 2)
    = (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w) a).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w)) (add_zero 2) := by
  rw [extHRestrict_comp]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  rw [NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits]

theorem zmodVal_one (p : ℕ) [Fact p.Prime] : (1 : ZMod p).val = 1 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  exact ZMod.val_one p

theorem zmodVal_zero (p : ℕ) : (0 : ZMod p).val = 0 := by
  rw [ZMod.val_zero]

/-- **Finite support of the Kummer localisation.** -/
theorem kummerLocSupport_finite (p : ℕ) [Fact p.Prime] [IsGalois k K]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ unitsK k L)
      (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      ∃ T : Finset (NK.GlobalCFT.Place L), ∀ w ∉ T,
        (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w)
            (h.comp (Abelian.Ext.mk₀ z) (add_zero 2))).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w)) (add_zero 2) = 0 := by
  intro L _instNF _instFD _instGal z hz h
  classical
  set κ : extH (unitsK k ↥L) 2 := h.comp (Abelian.Ext.mk₀ z) (add_zero 2) with hκ
  obtain ⟨R, hR⟩ := exists_transversal_of_mulAction (↥L ≃ₐ[k] ↥L) (NK.GlobalCFT.Place ↥L)
  have hfin : {w : NK.GlobalCFT.Place ↥L |
      ¬ IsUnramifiedExt (k := k) (K := ↥L) w
        (extLoc (k := k) (K := ↥L) w (extToIdeles κ))}.Finite :=
    (ext_idele_shapiro_aux (k := k) (K := ↥L) (unitRep (↥L ≃ₐ[k] ↥L))
      (by infer_instance) 2 R hR).2.1 (extToIdeles κ)
  obtain ⟨T₁, hT₁⟩ := exists_finset_unramifiedPlaces (k := k) (L := ↥L)
  refine ⟨T₁ ∪ hfin.toFinset, ?_⟩
  intro w hw
  have hw₁ : w ∉ T₁ := fun hmem => hw (Finset.mem_union_left _ hmem)
  have hwbad : IsUnramifiedExt (k := k) (K := ↥L) w
      (extLoc (k := k) (K := ↥L) w (extToIdeles κ)) := by
    by_contra hc
    exact hw (Finset.mem_union_right _
      ((Set.Finite.mem_toFinset hfin).mpr (Set.mem_ofPred.mpr hc)))
  obtain ⟨q, Q, hwq, hlies, hunr⟩ := hT₁ w hw₁
  rw [hwq] at hwbad ⊢
  have hzero : extLoc (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q) (extToIdeles κ) = 0 :=
    eq_zero_of_isUnramifiedExt_of_unramified (k := k) (L := ↥L) q Q hlies hunr
      (extLoc (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q) (extToIdeles κ)) hwbad
  rw [← e5_loc_ideleIncl_comp (k := k) (L := ↥L) (NK.GlobalCFT.Place.ofFinite q) κ]
  exact (congrArg
    (fun t => t.comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k ↥L (NK.GlobalCFT.Place.ofFinite q)))
      (add_zero 2))
    (extRes_eq_extHRestrict (D := decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q))
      (κ.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k ↥L)) (add_zero 2)))).trans hzero

/-- **The localisation `y ↦ (extHRestrict D y) ≫ (mk₀ φ)`, as an additive map.** -/
noncomputable def extLocHom {G : Type} [Group G] (D : Subgroup G) {A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff D} {n : ℕ} (φ : Rep.res D.subtype A ⟶ B) :
    extH A n →+ extH B n where
  toFun y := (extHRestrict D y).comp (Abelian.Ext.mk₀ φ) (add_zero n)
  map_zero' := by
    show (extHRestrict D (0 : extH A n)).comp _ _ = 0
    simp only [extHRestrict, extHMap, E6Util.extRes_zero, Abelian.Ext.zero_comp,
      Abelian.Ext.comp_zero]
  map_add' y y' := by
    show (extHRestrict D (y + y')).comp _ _ = _
    simp only [extHRestrict, extHMap, E6Util.extRes_add, Abelian.Ext.add_comp,
      Abelian.Ext.comp_add]

theorem pairing_formula (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (f : NK.GlobalCFT.Place k → ZMod p)
    (x : Work.SSGRoute.LevelCohLimit (k := k) (K := K) (Ω := Ω) p) :
    ∃ S : Finset (NK.GlobalCFT.Place k),
      (∀ v ∉ S, Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x = 0) ∧
      Work.SSGRoute.Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
          (Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ f) x
        = ∑ v ∈ S, (f v).val • Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x := by
  classical
  refine LevelCohLimit.induction (k := k) (K := K) (Ω := Ω) p
    (C := fun y => ∃ S : Finset (NK.GlobalCFT.Place k),
      (∀ v ∉ S, Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v y = 0) ∧
      Work.SSGRoute.Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
          (Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ f) y
        = ∑ v ∈ S, (f v).val • Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v y)
    ?_ x
  intro L h
  obtain ⟨u, hu, z, hzu⟩ := exists_zetaCoeff p k ↥L.1 ζ hζ
  have hz1 : ((Additive.toMul (z.hom (1 : ZMod p)) : (↥L.1)ˣ) : ↥L.1) = algebraMap k ↥L.1 ζ := by
    rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) by simp, hzu 1]
    simp [hu]
  haveI : FiniteDimensional K ↥L.1 :=
    NK.GlobalCFT.Inclusion.globalCFT_finiteDimensional_of_numberField
  set κ : SSGRoute.PTExt.extH (SSGRoute.PTExt.unitsK k ↥L.1) 2 :=
    h.comp (CategoryTheory.Abelian.Ext.mk₀ z) (add_zero 2) with hκdef
  obtain ⟨T, hT⟩ := kummerLocSupport_finite (k := k) (K := K) (Ω := Ω) p ζ hζ L.1 z hz1 h
  rw [← hκdef] at hT
  set s : NK.GlobalCFT.Place ↥L.1 → NK.GlobalCFT.Place k :=
    fun w => Work.SSGRoute.Phi0.placeUnder (k := k) (K := K) (e5LevelPlaceUnder (K := K) L.1 w)
    with hsdef
  have hP1 : ∀ (a : NK.GlobalCFT.Place K → ZMod p)
      (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w),
      ∃ y : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k ↥L.1) 2,
        (∀ (w' : NK.GlobalCFT.Place ↥L.1) (w : NK.GlobalCFT.Place K),
          NK.GlobalCFT.Place.LiesOver w' w →
          (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') y).comp
              (CategoryTheory.Abelian.Ext.mk₀
                (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')) (add_zero 2)
            = (a w).val • (SSGRoute.PTExt.extHRestrict
                (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') κ).comp
              (CategoryTheory.Abelian.Ext.mk₀
                (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w')) (add_zero 2)) ∧
        SSGRoute.PTExt.phiTriv (k := k) (K := K) (L := ↥L.1) (ZMod p)
            (CategoryTheory.Abelian.Ext.mk₀ (muClassHom p k K ζ hζ a ha)) h
          = y.comp (CategoryTheory.Abelian.Ext.mk₀
              (NK.HassePrinciple.classGroupMap k ↥L.1)) (add_zero 2) :=
    fun a ha => phi0_muClassHom_pairing p k K Ω ζ hζ a ha L.1 z hz1 h
  have hspec : ∀ v : NK.GlobalCFT.Place k,
      ∃ y : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k ↥L.1) 2,
        (∀ (w' : NK.GlobalCFT.Place ↥L.1) (w : NK.GlobalCFT.Place K),
          NK.GlobalCFT.Place.LiesOver w' w →
          (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') y).comp
              (CategoryTheory.Abelian.Ext.mk₀
                (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')) (add_zero 2)
            = ((fun w : NK.GlobalCFT.Place K =>
                  if Work.SSGRoute.Phi0.placeUnder (k := k) (K := K) w = v
                  then (1 : ZMod p) else 0) w).val •
              (SSGRoute.PTExt.extHRestrict
                (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') κ).comp
              (CategoryTheory.Abelian.Ext.mk₀
                (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w')) (add_zero 2)) ∧
        SSGRoute.PTExt.phiTriv (k := k) (K := K) (L := ↥L.1) (ZMod p)
            (CategoryTheory.Abelian.Ext.mk₀ (muClassHom p k K ζ hζ
              (fun w => if Work.SSGRoute.Phi0.placeUnder (k := k) (K := K) w = v then 1 else 0)
              (fun σ w => by rw [Work.SSGRoute.Phi0.placeUnder_smul]))) h
          = y.comp (CategoryTheory.Abelian.Ext.mk₀
              (NK.HassePrinciple.classGroupMap k ↥L.1)) (add_zero 2) := by
    intro v
    exact hP1 (fun w => if Work.SSGRoute.Phi0.placeUnder (k := k) (K := K) w = v then 1 else 0)
      (fun σ w => by rw [Work.SSGRoute.Phi0.placeUnder_smul])
  choose yv hyv using hspec
  have lamV_eq (v : NK.GlobalCFT.Place k) :
      Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v
          (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h)
        = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
            ((yv v).comp (CategoryTheory.Abelian.Ext.mk₀
              (NK.HassePrinciple.classGroupMap k ↥L.1)) (add_zero 2)) := by
    have h1 : Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v
        = Work.SSGRoute.Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
            (Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ
              (fun v' => if v' = v then 1 else 0)) := rfl
    rw [h1, Work.SSGRoute.Phi0.phiColim_of (k := k) (K := K) (Ω := Ω) p
      (Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ (fun v' => if v' = v then 1 else 0))
      L h]
    rw [show Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ
          (fun v' => if v' = v then 1 else 0)
        = muClassHom p k K ζ hζ
            (fun w => if Work.SSGRoute.Phi0.placeUnder (k := k) (K := K) w = v then 1 else 0)
            (fun σ w => by rw [Work.SSGRoute.Phi0.placeUnder_smul])
        from by simp only [Work.SSGRoute.Phi0.cOfFun]]
    exact congrArg (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L) (hyv v).2
  refine ⟨T.image s, ?_, ?_⟩
  · intro v hv
    have hloc0 : ∀ w' : NK.GlobalCFT.Place ↥L.1,
        (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w')
          (yv v)).comp
            (CategoryTheory.Abelian.Ext.mk₀
              (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')) (add_zero 2) = 0 := by
      intro w'
      rw [(hyv v).1 w' (e5LevelPlaceUnder (K := K) L.1 w')
        (e5LevelPlaceUnder_liesOver (K := K) L.1 w')]
      beta_reduce
      by_cases hsw : Work.SSGRoute.Phi0.placeUnder (k := k) (K := K)
          (e5LevelPlaceUnder (K := K) L.1 w') = v
      · have hw'T : w' ∉ T := fun hmem => hv (Finset.mem_image.mpr ⟨w', hmem, hsw⟩)
        rw [if_pos hsw, zmodVal_one p, one_smul, hT w' hw'T]
      · rw [if_neg hsw, zmodVal_zero, zero_smul]
    have hy0 : yv v = 0 := extIdele_localisation_injective k ↥L.1 (yv v) hloc0
    rw [lamV_eq v, hy0]
    simp only [CategoryTheory.Abelian.Ext.zero_comp, map_zero]
  · obtain ⟨yf, hyf⟩ := hP1 (fun w => f (Work.SSGRoute.Phi0.placeUnder (k := k) (K := K) w))
      (fun σ w => by rw [Work.SSGRoute.Phi0.placeUnder_smul])
    let Φ : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k ↥L.1) 2 →+
        Work.SSGRoute.ClassLevel (k := k) (K := K) (Ω := Ω) L :=
      { toFun := fun y => y.comp (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.classGroupMap k ↥L.1)) (add_zero 2)
        map_zero' := by simp only [CategoryTheory.Abelian.Ext.zero_comp]
        map_add' := fun a b => by simp only [CategoryTheory.Abelian.Ext.add_comp] }
    let Ψ : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k ↥L.1) 2 →+
        Work.SSGRoute.ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
      (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L).comp Φ
    have hLHS : Work.SSGRoute.Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
          (Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ f)
          (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h) = Ψ yf := by
      rw [Work.SSGRoute.Phi0.phiColim_of (k := k) (K := K) (Ω := Ω) p
        (Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ f) L h]
      refine congrArg (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L) ?_
      rw [show Work.SSGRoute.Phi0.cOfFun (k := k) (K := K) p ζ hζ f
          = muClassHom p k K ζ hζ
              (fun w => f (Work.SSGRoute.Phi0.placeUnder (k := k) (K := K) w))
              (fun σ w => by rw [Work.SSGRoute.Phi0.placeUnder_smul])
          from by simp only [Work.SSGRoute.Phi0.cOfFun]]
      exact hyf.2
    have hRHS : (∑ v ∈ T.image s, (f v).val •
          Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v
            (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h))
        = Ψ (∑ v ∈ T.image s, (f v).val • yv v) := by
      rw [Finset.sum_congr rfl (fun v (_ : v ∈ T.image s) =>
        congrArg (fun z => (f v).val • z) (lamV_eq v))]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [map_nsmul]
      rfl
    have hyf_sum : yf = ∑ v ∈ T.image s, (f v).val • yv v := by
      refine sub_eq_zero.mp (extIdele_localisation_injective k ↥L.1
        (yf - ∑ v ∈ T.image s, (f v).val • yv v) ?_)
      intro w'
      show extLocHom (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w')
          (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')
          (yf - ∑ v ∈ T.image s, (f v).val • yv v) = 0
      rw [map_sub]
      set X :=
        (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') κ).comp
          (CategoryTheory.Abelian.Ext.mk₀
            (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w')) (add_zero 2) with hXdef
      have hYf : extLocHom (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w')
            (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w') yf
          = (f (s w')).val • X := by
        show (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') yf).comp
            (CategoryTheory.Abelian.Ext.mk₀
              (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')) (add_zero 2) = (f (s w')).val • X
        simpa only [hXdef] using hyf.1 w' (e5LevelPlaceUnder (K := K) L.1 w')
          (e5LevelPlaceUnder_liesOver (K := K) L.1 w')
      have hYs : extLocHom (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w')
            (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')
            (∑ v ∈ T.image s, (f v).val • yv v)
          = ∑ v ∈ T.image s, (f v).val • (((if s w' = v then (1 : ZMod p) else 0)).val • X) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [map_nsmul]
        show (f v).val • (SSGRoute.PTExt.extHRestrict
              (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') (yv v)).comp
              (CategoryTheory.Abelian.Ext.mk₀
                (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')) (add_zero 2)
          = (f v).val • (((if s w' = v then (1 : ZMod p) else 0)).val • X)
        simpa only [hXdef] using congrArg (fun z => (f v).val • z)
          ((hyv v).1 w' (e5LevelPlaceUnder (K := K) L.1 w')
            (e5LevelPlaceUnder_liesOver (K := K) L.1 w'))
      rw [hYf, hYs]
      have hterm : ∀ v : NK.GlobalCFT.Place k,
          (f v).val • (((if s w' = v then (1 : ZMod p) else 0)).val • X)
            = if s w' = v then (f v).val • X else 0 := by
        intro v
        by_cases hv : s w' = v
        · rw [if_pos hv, if_pos hv, zmodVal_one p, one_smul]
        · rw [if_neg hv, if_neg hv, zmodVal_zero, zero_smul, nsmul_zero]
      rw [Finset.sum_congr rfl (fun v _ => hterm v)]
      have hsum : (∑ v ∈ T.image s, (if s w' = v then (f v).val • X else 0))
          = if s w' ∈ T.image s then (f (s w')).val • X else 0 := by
        by_cases hS : s w' ∈ T.image s
        · rw [if_pos hS, Finset.sum_eq_single (s w')]
          · rw [if_pos rfl]
          · intro b hb hbne
            rw [if_neg (fun h' => hbne h'.symm)]
          · intro hnot; exact absurd hS hnot
        · rw [if_neg hS]
          exact Finset.sum_eq_zero (fun b hb => by
            rw [if_neg (fun h' : s w' = b => hS (h' ▸ hb))])
      rw [hsum]
      by_cases hS : s w' ∈ T.image s
      · rw [if_pos hS, sub_self]
      · rw [if_neg hS]
        have hw'T : w' ∉ T := fun hmem => hS (Finset.mem_image.mpr ⟨w', hmem, rfl⟩)
        rw [hXdef, hT w' hw'T]
        simp only [nsmul_zero, sub_zero]
    rw [hLHS, hRHS, hyf_sum]



end

end Work.SSGRoute.E5Route
