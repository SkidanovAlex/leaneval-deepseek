import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.SSGRoute.PTembedding.localGlobal_compat
import Submission.Work.SSGRoute.phi0_defs
import Submission.Work.SSGRoute.phi0_family_vanish_of_local
import Submission.Work.SSGRoute.phi0_muClassHom_pairing

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-! ## Auxiliary bookkeeping -/

section LevelPlace

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- **The place of `K` under a place of a level `L`** (a choice; the value is unique). -/
noncomputable def phi0LevelPlaceUnder (L : IntermediateField K Ω) [FiniteDimensional K ↥L]
    (w : NK.GlobalCFT.Place ↥L) : NK.GlobalCFT.Place K :=
  Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w)

theorem phi0LevelPlaceUnder_liesOver (L : IntermediateField K Ω) [FiniteDimensional K ↥L]
    (w : NK.GlobalCFT.Place ↥L) :
    NK.GlobalCFT.Place.LiesOver w (phi0LevelPlaceUnder (K := K) L w) :=
  Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w)

end LevelPlace

/-! ## E8′ in `Ext` form -/

/-- **E8′ in the `Ext` core**: a class of `H²(Gal(L/k), Lˣ)` whose localisation vanishes at every
place of `L` outside one `Gal(L/k)`-orbit is zero.  (`Work.SSGRoute.brauer_single_place`
transported along the E0b bridge, exactly as in `Work.SSGRoute.hbn_ext_units`.) -/
theorem brauer_single_place_ext_aux (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (a : extH (unitsK k L) 2) (w₀ : NK.GlobalCFT.Place L)
    (h : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) →
      (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w) a).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w)) (add_zero 2) = 0) :
    a = 0 := by
  classical
  let e := E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)
  let x : groupCohomology (unitsK k L) 2 := e.symm a
  have hax : e x = a := e.apply_symm_apply a
  have hx0 : x = 0 := by
    refine brauer_single_place k L x w₀ (fun w hw => ?_)
    rw [hbnAux_locUnits_eq_map (k := k) (L := L) w]
    have hnat := hbnAux_eBridge_natural (G := L ≃ₐ[k] L)
      (H := MulAction.stabilizer (L ≃ₐ[k] L) w)
      (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype (A := unitsK k L)
      (B := NK.HassePrinciple.localUnitsRep k L w)
      (NK.HassePrinciple.unitsToLocalUnits k L w) 2 x
    suffices E0bGroupCoeff.eBridge 2 (MulAction.stabilizer (L ≃ₐ[k] L) w)
        (NK.HassePrinciple.localUnitsRep k L w)
        ((groupCohomology.map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
          (NK.HassePrinciple.unitsToLocalUnits k L w) 2).hom x) = 0 by
      exact (E0bGroupCoeff.eBridge 2 (MulAction.stabilizer (L ≃ₐ[k] L) w)
        (NK.HassePrinciple.localUnitsRep k L w)).injective (by rw [this, map_zero])
    rw [hnat, hax,
      ← extHRestrict_comp_mk0 (MulAction.stabilizer (L ≃ₐ[k] L) w) a
        (NK.HassePrinciple.unitsToLocalUnits k L w)]
    exact h w hw
  calc a = e x := hax.symm
    _ = 0 := by rw [hx0, map_zero]

/-! ## Localisation commutes with `Lˣ ↪ 𝕀_L` -/

/-- **The localisation of the image of a class under `Lˣ ↪ 𝕀_L` is its localisation.**  The
coefficient triangle `res_{D_w}(𝕀_L-incl) ≫ (𝕀_L → L_wˣ) = (Lˣ → L_wˣ)` together with the
`.`-calculus of `Ext`. -/
theorem loc_ideleIncl_comp (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
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

/-! ## Injectivity of the class-group colimit maps -/

/-- **The canonical maps `A_L → A` of the class-group colimit are injective** (inflation on
`H²(·, C_·)` is injective, `Work.SSGRoute.inflCIn_injective`). -/
theorem classLevelLimit_of_injective_aux {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsGalois k K] (L : Lvl k K Ω) :
    Function.Injective (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L) := by
  intro x y hxy
  have hsub : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨L', hLL', hzero⟩ :=
    (ClassLevelLimit.of_eq_zero_iff (k := k) (K := K) (Ω := Ω) L (x - y)).mp hsub
  have hmem : classLevelMap (k := k) L L' hLL' (x - y) = 0 := by
    rw [classLevelMap_apply (k := k) L L' hLL']
    exact hzero
  have hinj : Function.Injective (classLevelMap (k := k) L L' hLL') := by
    intro p q hpq
    rw [classLevelMap_apply (k := k) L L' hLL',
      classLevelMap_apply (k := k) L L' hLL'] at hpq
    exact inflCIn_injective (k := k) (K := K) (Ω := Ω) L.1 L'.1 hLL' hpq
  have hxy' : x - y = 0 := hinj (by simp only [hmem, map_zero])
  exact sub_eq_zero.mp hxy'

/-! ## The separation theorem -/

/-- **E4Ω separation.**  The local functionals `λ_v` (the `v`-components of the compatible
`p`-torsion functionals realised by the `μ_p`-idèles which are `ζ` over a place `v` of `k` and `1`
elsewhere) separate the points of `V = colim_L H²(Gal(L/k),𝔽_p)`: a nonzero colimit class has a
nonzero `v`-component for some place `v` of `k`.  (Route: pick a level `L` with `x = of_L h`; by
Kummer `κ_L h = h ∪ ζ` is nonzero, so by Hasse–Brauer–Noether (`Work.SSGRoute.ext_units_local_hasse`,
`NK.GlobalCFTdeep.hbnUnits`) some place `w` of `L` has a nonzero localisation; the class `y` whose
components are the localisations over the orbit of `w` and `0` elsewhere is nonzero and supported in
one Galois orbit, so `y ∘ classGroupMap ≠ 0` by exactness of the class formation sequence and E8′
`Work.SSGRoute.brauer_single_place`; that value is `lamV v x` at `v = placeUnder w`.) -/
theorem phi0_lamV_separates (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (x : Work.SSGRoute.LevelCohLimit (k := k) (K := K) (Ω := Ω) p) (hx : x ≠ 0) :
    ∃ v : NK.GlobalCFT.Place k,
      Work.SSGRoute.Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x ≠ 0 := by
  classical
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  -- Step 1: a level representative of `x`
  obtain ⟨L, h, hLh⟩ : ∃ (L : Lvl k K Ω) (h : LevelCoh (k := k) (K := K) (Ω := Ω) p L),
      LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h = x :=
    LevelCohLimit.induction (k := k) (K := K) (Ω := Ω) p
      (C := fun y => ∃ (L : Lvl k K Ω) (h : LevelCoh (k := k) (K := K) (Ω := Ω) p L),
        LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h = y)
      (fun L h => ⟨L, h, rfl⟩) x
  haveI : FiniteDimensional K ↥L.1 :=
    NK.GlobalCFT.Inclusion.globalCFT_finiteDimensional_of_numberField
  -- Step 2: the Kummer coefficient class `𝔽_p → Lˣ`, `1 ↦ ζ`
  obtain ⟨u, hu, z, hz⟩ := exists_zetaCoeff p k ↥L.1 ζ hζ
  have hz1 : ((Additive.toMul (z.hom (1 : ZMod p)) : (↥L.1)ˣ) : ↥L.1) =
      algebraMap k ↥L.1 ζ := by
    have h1 : z.hom (1 : ZMod p) = Additive.ofMul u := by
      simpa using hz 1
    rw [h1, toMul_ofMul]
    exact hu
  -- Step 3: the Kummer push `κ = h ∪ ζ` of `h` is non-zero
  set κ : extH (unitsK k ↥L.1) 2 :=
    h.comp (Abelian.Ext.mk₀ z) (add_zero 2) with hκ
  have hκne : κ ≠ 0 := by
    intro hk0
    obtain ⟨L', hNF, hFD, hGal, hLL, hzero⟩ :=
      E4R3.kummer_dies_at_higher_level_clean p k K Ω ζ hζ L.1 z hz1 h
        hk0
    let L'v : Lvl k K Ω := ⟨L', hNF, hFD, hGal⟩
    have hLLv : L ≤ L'v := hLL
    have hx0 : x = 0 := by
      rw [← hLh, ← LevelCohLimit.of_levelMap (k := k) (K := K) (Ω := Ω) p hLLv h,
        levelMap_apply]
      exact (congrArg (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L'v) hzero).trans
        (LevelCohLimit.of_zero (k := k) (K := K) (Ω := Ω) p L'v)
    exact hx hx0
  -- Step 4: some place of `L` has a non-zero localisation of `κ` (Hasse–Brauer–Noether)
  obtain ⟨w, hw⟩ : ∃ w : NK.GlobalCFT.Place ↥L.1,
      (extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) κ).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w)) (add_zero 2) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hκne (hbn_ext_units k ↥L.1 κ hc)
  -- Step 5: the base-level place `v` and the indicator function
  set wK : NK.GlobalCFT.Place K := phi0LevelPlaceUnder (K := K) L.1 w with hwK
  set v : NK.GlobalCFT.Place k := Phi0.placeUnder (k := k) (K := K) wK with hv
  set g : NK.GlobalCFT.Place k → ZMod p := fun v' => if v' = v then 1 else 0 with hg
  set a : NK.GlobalCFT.Place K → ZMod p :=
    fun w' => g (Phi0.placeUnder (k := k) (K := K) w') with ha
  have ha_inv : ∀ (σ : K ≃ₐ[k] K) (w' : NK.GlobalCFT.Place K), a (σ • w') = a w' := by
    intro σ w'
    show g (Phi0.placeUnder (k := k) (K := K) (σ • w')) =
      g (Phi0.placeUnder (k := k) (K := K) w')
    rw [Phi0.placeUnder_smul]
  -- Step 6: the local–global cup formula at the level `L`
  obtain ⟨y, hyloc, hyphi⟩ :=
    phi0_muClassHom_pairing p k K Ω ζ hζ a ha_inv L.1 z hz1 h
  refine ⟨v, ?_⟩
  intro hzero
  -- Step 7: `lamV v x` is the image of `y ∘ classGroupMap` in the colimit
  have hlamV : Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v x
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (y.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k ↥L.1))
            (add_zero 2)) := by
    have h1 : Phi0.lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v
        = Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
            (Phi0.cOfFun (k := k) (K := K) p ζ hζ g) := rfl
    have hcOf : Phi0.cOfFun (k := k) (K := K) p ζ hζ g
        = muClassHom p k K ζ hζ a ha_inv := rfl
    rw [h1, ← hLh, Phi0.phiColim_of, hcOf, hyphi]
  have hy0 : y.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k ↥L.1))
      (add_zero 2) = 0 :=
    classLevelLimit_of_injective_aux (k := k) (K := K) (Ω := Ω) L
      (by rw [← hlamV, hzero, map_zero])
  -- Step 8: exactness of the class formation sequence: `y` comes from `Lˣ`
  obtain ⟨a₀, ha₀⟩ :=
    Abelian.Ext.covariant_sequence_exact₂ (X := unitRep (↥L.1 ≃ₐ[k] ↥L.1))
      (S := sesK k ↥L.1) (NK.HassePrinciple.ideleShortComplex_shortExact k ↥L.1) y hy0
  have hloc_eq : ∀ w' : NK.GlobalCFT.Place ↥L.1,
      (extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') y).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k ↥L.1 w')) (add_zero 2)
        = (extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') a₀).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w')) (add_zero 2) := by
    intro w'
    rw [← ha₀]
    exact loc_ideleIncl_comp (k := k) (L := ↥L.1) w' a₀
  -- Step 9: the localisation of `a₀` at `w` is non-zero
  have hlocw : (extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) a₀).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w)) (add_zero 2) ≠ 0 := by
    rw [← hloc_eq w,
      hyloc w wK (by rw [hwK]; exact phi0LevelPlaceUnder_liesOver (K := K) L.1 w)]
    have ha1 : a wK = 1 := by
      rw [ha, hg, hv]
      exact if_pos rfl
    rw [ha1, ZMod.val_one p, one_smul]
    exact hw
  -- Step 10: the localisations of `a₀` away from the orbit of `w` vanish, contradicting E8′
  have haway : ∀ w' : NK.GlobalCFT.Place ↥L.1,
      (∀ σ : ↥L.1 ≃ₐ[k] ↥L.1, σ • w ≠ w') →
      (extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') a₀).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w')) (add_zero 2) = 0 := by
    intro w' hw'
    set wK' : NK.GlobalCFT.Place K := phi0LevelPlaceUnder (K := K) L.1 w' with hwK'
    have hlies : NK.GlobalCFT.Place.LiesOver w' wK' := by
      rw [hwK']; exact phi0LevelPlaceUnder_liesOver (K := K) L.1 w'
    rw [← hloc_eq w', hyloc w' wK' hlies]
    have hzero_a : a wK' = 0 := by
      have hne : Phi0.placeUnder (k := k) (K := K) wK' ≠ v := by
        intro heq
        have h1 : NK.GlobalCFT.Place.LiesOver w' wK' := hlies
        have h2 : NK.GlobalCFT.Place.LiesOver wK' v := heq ▸
          Phi0.placeUnder_liesOver (k := k) (K := K) wK'
        have h3 : NK.GlobalCFT.Place.LiesOver w' v :=
          place_liesOver_trans (K := k) (L := K) (M := ↥L.1) h1 h2
        have h4 : NK.GlobalCFT.Place.LiesOver w v :=
          place_liesOver_trans (K := k) (L := K) (M := ↥L.1)
            (by rw [hwK]; exact phi0LevelPlaceUnder_liesOver (K := K) L.1 w)
            (hv.symm ▸ Phi0.placeUnder_liesOver (k := k) (K := K) wK)
        obtain ⟨σ, hσ⟩ :=
          NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := k) (L := ↥L.1) h4 h3
        exact hw' σ hσ
      rw [ha, hg]
      exact if_neg hne
    rw [hzero_a, ZMod.val_zero, zero_smul]
  have hcontra : (extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) a₀).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w)) (add_zero 2) = 0 := by
    rw [brauer_single_place_ext_aux (k := k) (L := ↥L.1) a₀ w haway]
    exact (extHRestrict_comp_mk0 (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w)
        (0 : extH (unitsK k ↥L.1) 2)
        (NK.HassePrinciple.unitsToLocalUnits k ↥L.1 w)).trans (E6Util.extHMap_zero _ _)
  exact hlocw hcontra

end

end Work.SSGRoute
