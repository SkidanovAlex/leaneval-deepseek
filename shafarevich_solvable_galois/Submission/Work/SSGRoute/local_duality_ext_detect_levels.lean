import Mathlib
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.E6Calc.extCor_levelPair
import Submission.Work.SSGRoute.extCor_yoneda_comp
import Submission.Work.SSGRoute.Z8.SylowSetup
import Submission.Work.SSGRoute.Z8.levelPair_vanish_of_vanish_closure
import Submission.Work.SSGRoute.Z8.localUnits_extH_pTorsion_card_gcd
import Submission.Work.SSGRoute.Z8.extCor_injective_pTorsion_gcd
import Submission.Work.SSGRoute.E7bZ8Step1
import Submission.Work.SSGRoute.exists_galoisClosure_level
import Submission.Work.SSGRoute.detectAbove_pgroup
import Submission.Work.SSGRoute.extRes_injective_of_index
import Submission.Work.SSGRoute.exists_localZetaCoeff
import Submission.Work.SSGRoute.pgroup_fixes_primitiveRoot
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.local_duality_ext_detect_h
import Submission.Work.SSGRoute.levelPair_baseChange_in
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7b clause (i), node `Z8`: detection of classes by the levels of the cone

The file proves the requested statement `Work.SSGRoute.local_duality_ext_detect_levels`, whose
proof is the `Z8` assembly of the E7b redesign:

1. a Sylow `p`-subgroup `S₀ ≤ D_w(K/k)` and the fixed field `k' = K^S₀` (so that `D_w(K/k')` is a
   `p`-group, and every simple `𝔽_p[D_w(K/k')]`-module is trivial);
2. the base change `Work.SSGRoute.levelPair_baseChange_in` from `k` to `k'`;
3. the cone hypothesis at `k'` (from the target's hypothesis, transported at the Galois closure of
   each `k'`-level over `k`, using `Work.SSGRoute.detectLevels_levelPair_comapSubgroup_vanish` and
   `Work.SSGRoute.Z8.extCor_injective_pTorsion_gcd`);
4. detection at the base `k'` (`Work.SSGRoute.detectAbove_pgroup`), and injectivity of the Sylow
   restriction (`Work.SSGRoute.extRes_injective_of_index`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

/-! ## Auxiliary facts -/

/-- The place `w` lies over itself, for the trivial extension `K / K`. -/
theorem detectLevels_liesOver_self (K : Type) [Field K] [NumberField K] (w : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Place.LiesOver w w := by
  rcases w with w | q
  · refine NK.GlobalCFT.Place.liesOver_ofInfinite ?_
    exact (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w w).mpr (NumberField.InfinitePlace.comap_id w)
  · refine NK.GlobalCFT.Place.liesOver_ofFinite ?_
    exact (NK.GlobalCFT.Norm.liesOver_iff_under_eq q.asIdeal q.asIdeal).mpr (by
      rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id])

/-- The base-change subgroup of `Work.SSGRoute.levelPair_baseChange_in` attached to a subgroup
`S ≤ D_w` is, for the fixed field `k' = K^S`, the subgroup `S` itself. -/
theorem detectLevels_baseChangeSubgroup_eq (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (S : Subgroup (decompK (k := k) w)) :
    (((decompK (k := ↥(IntermediateField.fixedField (galSub (k := k) w S))) w).map
        (AlgEquiv.restrictScalarsHom (R := k)
          (S := ↥(IntermediateField.fixedField (galSub (k := k) w S))) (A := K))).comap
      (decompK (k := k) w).subtype) = S := by
  have hPD : galSub (k := k) w S ≤ decompK (k := k) w := galSub_le (k := k) w S
  have hmr := map_restrictScalarsHom_decompK_fixedField k K w (galSub (k := k) w S) hPD
  rw [hmr]
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : y = x := Subtype.ext (by simpa using hyx)
    rwa [← hxy]
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A primitive `p`-th root of unity in `K` is fixed by the decomposition group of `w` over the
fixed field `K^S` of a `p`-subgroup `S ≤ D_w`: that group is a `p`-group, and a `p`-group fixes
every `p`-th root of unity. -/
theorem detectLevels_fixedBase_zeta_fixed (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (w : NK.GlobalCFT.Place K)
    (S : Subgroup (decompK (k := k) w)) (hS : IsPGroup p ↥S) :
    ∀ σ : decompK (k := fixedBase (k := k) w S) w,
      (σ : K ≃ₐ[fixedBase (k := k) w S] K) ζ = ζ := by
  intro σ
  exact pgroup_fixes_primitiveRoot p (fixedBase (k := k) w S) K ζ hζ
    (decompK (k := fixedBase (k := k) w S) w) (isPGroup_decompK_fixedBase (k := k) w S hS)
    (σ : K ≃ₐ[fixedBase (k := k) w S] K) σ.2


section PVanish

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **P2 of the `Z8` assembly.**  For a subgroup `S ≤ D` and its preimage `S' = S.comap f`, the
level-`S'` pairing of the restriction `extRes S.subtype y` with `h` has corestriction the level-`D`
pairing of `y` with the corestricted class `extCor h`; if the latter vanishes (which is the
hypothesis `hy` at the single class `extCor h`), the former does too, as soon as corestriction is
injective on the `p`-torsion of `H²(S', B)` and the value is `p`-torsion. -/
theorem detectLevels_levelPair_comapSubgroup_vanish {G D : Type} [Group G] [Group D] [Fintype G]
    [Fintype D]
    (S : Subgroup D) [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    (f : G →* D) [DecidableRel (QuotientGroup.rightRel (S.comap f))]
    [Fintype (G ⧸ S.comap f)]
    (p : ℕ) {M A : Rep Coeff D} {B : Rep Coeff G}
    (ι : Rep.res f A ⟶ B)
    (hM : ∀ m : M, p • m = 0)
    (y : Abelian.Ext M A 1)
    (hy : ∀ t : extH (Rep.res f M) 1, levelPair f ι y t = 0)
    (hker : ∀ t : extH (Rep.res (S.comap f).subtype B) 2, p • t = 0 →
      Work.SSGRoute.extCor (S.comap f) (unitRep G) B 2 t = 0 → t = 0)
    (h : extH (Rep.res (f.subgroupComap S) (Rep.res S.subtype M)) 1) :
    levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι) (extRes S.subtype y) h = 0 := by
  let Z : extH (Rep.res (S.comap f).subtype B) 2 :=
    levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι) (extRes S.subtype y) h
  change Z = 0
  -- the class at the level `S' = S.comap f`, written with `extRes f y`
  have hA : extRes (f.subgroupComap S) (extRes S.subtype y)
      = extRes (S.comap f).subtype (extRes f y) :=
    (SylowDesc.extRes_comp_aux S.subtype (f.subgroupComap S) y).symm.trans
      (SylowDesc.extRes_comp_aux f (S.comap f).subtype y)
  have hz : Z = levelPair (S.comap f).subtype (Rep.resMap (S.comap f).subtype ι) (extRes f y) h := by
    show levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι) (extRes S.subtype y) h
        = levelPair (S.comap f).subtype (Rep.resMap (S.comap f).subtype ι) (extRes f y) h
    simp only [levelPair]
    exact congrArg (fun q => Abelian.Ext.comp h
      (Abelian.Ext.comp q (Abelian.Ext.mk₀ (Rep.resMap (S.comap f).subtype ι)) (add_zero 1))
        rfl) hA
  -- `y` is `p`-torsion, hence so is its restriction
  have hM0 : (p • (𝟙 M : M ⟶ M)) = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro m
    rw [Rep.nsmul_hom]
    rw [show (p • Rep.Hom.hom (𝟙 M)).toLinearMap m
        = p • ((Rep.Hom.hom (𝟙 M)).toLinearMap m) from rfl]
    simpa using hM m
  have hpy : p • y = 0 := by
    have hid : p • y = (Abelian.Ext.mk₀ (p • (𝟙 M : M ⟶ M))).comp y (zero_add 1) := by
      rw [mk₀_nsmul_aux p (𝟙 M : M ⟶ M),
        nsmul_comp_aux p (Abelian.Ext.mk₀ (𝟙 M : M ⟶ M)) y (zero_add 1),
        Abelian.Ext.mk₀_id_comp]
    rw [hid, hM0, Abelian.Ext.mk₀_zero]
    exact Abelian.Ext.zero_comp M _ _ _ rfl
  have hpx : p • (extRes S.subtype y) = 0 := by
    let F : Abelian.Ext M A 1 →+ Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) 1 :=
      (Rep.resFunctor S.subtype).mapExtAddHom M A 1
    have hF : ∀ z : Abelian.Ext M A 1, F z = extRes S.subtype z := fun _ => rfl
    rw [← hF y, ← map_nsmul F p y, hpy, map_zero]
  -- the value of the goal is `p`-torsion
  have hpz : p • Z = 0 := by
    have hgen : ∀ (n : ℕ), n • levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι)
        (extRes S.subtype y) h
        = levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι)
            (n • extRes S.subtype y) h := by
      intro n
      induction n with
      | zero => rw [zero_nsmul, zero_nsmul, levelPair_zero]
      | succ n ih => rw [succ_nsmul, succ_nsmul, ih, ← levelPair_add]
    have hZ : Z = levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι)
        (extRes S.subtype y) h := rfl
    rw [hZ, hgen p, hpx, levelPair_zero]
  -- corestriction of the value is killed by `hy`
  have hcor : extCor (S.comap f) (unitRep G) B 2 Z = 0 := by
    rw [hz]
    rw [E6Calc.extCor_levelPair (S.comap f) (extRes f y) h ι]
    have hhy := hy (extCor (S.comap f) (unitRep G) (Rep.res f M) 1 h)
    simp only [levelPair] at hhy
    rw [← hhy]
    exact Abelian.Ext.comp_assoc_of_third_deg_zero _ (extRes f y) (Abelian.Ext.mk₀ ι) rfl
  exact hker Z hpz hcor

end PVanish

/-! ## The target -/

theorem local_duality_ext_detect_levels (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K) :
    ∀ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
      (∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
        [FiniteDimensional k L] [IsGalois k L]
        (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
        (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
        (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
        (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
        (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
          ι.hom (Additive.ofMul u) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
        (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
        levelPair f ι y h = 0) → y = 0 := by
  classical
  intro y hy
  -- A Sylow `p`-subgroup of `D_w(K/k)`, and the fixed field `k' = K^{S₀}`.
  obtain ⟨S₀, hS₀grp, hS₀idx⟩ := exists_isPGroup_sylow_decompK p k K w
  let k' := fixedBase (k := k) w S₀
  -- The base-change subgroup of `levelPair_baseChange_in` at `(k, k', K)`.
  let Sbc : Subgroup (decompK (k := k) w) :=
    ((decompK (k := k') w).map (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))).comap
      (decompK (k := k) w).subtype
  have hSbc : Sbc = S₀ := detectLevels_baseChangeSubgroup_eq k K w S₀
  have hidx : ¬ p ∣ Sbc.index := by rw [hSbc]; exact hS₀idx
  -- The base change `k → k'`.
  obtain ⟨-, eE, hY3⟩ := levelPair_baseChange_in p k k' K w M
  let M' : Rep Coeff (K ≃ₐ[k'] K) :=
    Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M
  -- The transported cone hypothesis at the base `k'`.
  have hV' : VanishesAbove k' K (eE (extRes Sbc.subtype y)) K w (MonoidHom.id _) (𝟙 _) := by
    intro L hFL hNFL hA1 hA2 hST hFinL hGalL w' hw' g hg ι₁ hι₁ h
    letI := hFL
    letI := hNFL
    letI := hA1
    letI := hA2
    letI := hST
    letI := hFinL
    letI := hGalL
    -- a `k`-algebra structure on `L` exhibiting the tower `k ⊆ k' ⊆ L`
    letI : Algebra k L := RingHom.toAlgebra ((algebraMap k' L).comp (algebraMap k k'))
    letI : SMul k' L := Algebra.toSMul
    haveI : IsScalarTower k k' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    -- the Galois closure of the `k'`-level `L` over `k`, and a place `wc` above `w'` above `w`
    obtain ⟨Lc, hLcF, hLcNF, hLcA1, hLcA2, hLcA3, hLcA4, hLcF5, hLcF6, hLcF7, hLcF8, hLcF9,
      hLcF10, hLcF11, hLcF12, hLcF13, hLcF14, hLcF15, wc, hwcw', hwcw⟩ :=
      exists_galoisClosure_level k k' K L w w' hw'
    letI := hLcF
    letI := hLcNF
    letI := hLcA1
    letI := hLcA2
    letI := hLcA3
    letI := hLcA4
    letI := hLcF5
    letI := hLcF6
    letI := hLcF7
    letI := hLcF8
    letI := hLcF9
    letI := hLcF10
    letI := hLcF11
    letI := hLcF12
    letI := hLcF13
    letI := hLcF14
    letI := hLcF15
    -- the closure-level vanishing, for every choice of `k'`-level data
    have htop : ∀ (fc : MulAction.stabilizer (Lc ≃ₐ[k'] Lc) wc →* decompK (k := k') w)
        (hfc : ∀ σ, ((fc σ : decompK (k := k') w) : K ≃ₐ[k'] K) =
          galRes k' K Lc (σ : Lc ≃ₐ[k'] Lc))
        (ιc : Rep.res fc (localUnitsK (k := k') w) ⟶ NK.HassePrinciple.localUnitsRep k' Lc wc)
        (hιc : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ, ιc.hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits wc w hwcw u))
        (hc : extH (Rep.res fc (Rep.res (decompK (k := k') w).subtype M')) 1),
        levelPair fc ιc (eE (extRes Sbc.subtype y)) hc = 0 := by
      intro fc hfc ιc hιc hc
      -- the `k`-level data at `Lc`
      obtain ⟨f, hf⟩ := decompK_restrict_exists k K Lc w wc hwcw
      obtain ⟨ι, hι⟩ := localUnitsMap_exists k K Lc w wc hwcw f hf
      -- the base change at `Lc`
      obtain ⟨hY3a, hY3b, eH, eB, hY3eq⟩ := hY3 Lc wc hwcw f hf ι hι fc hfc ιc hιc
      -- the two `p`-torsion cardinalities of the dichotomy
      have hcardG : Nat.card {x : extH (NK.HassePrinciple.localUnitsRep k Lc wc) 2 //
            p • x = 0}
          = Nat.gcd p (Nat.card (MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc)) :=
        Z8.localUnits_extH_pTorsion_card_gcd p k Lc wc
      have hcardS : Nat.card {x : extH (Rep.res (Sbc.comap f).subtype
            (NK.HassePrinciple.localUnitsRep k Lc wc)) 2 // p • x = 0}
          = Nat.gcd p (Nat.card (Sbc.comap f)) := by
        have h1 : Nat.card (decompK (k := k') wc) = Nat.card (Sbc.comap f) := hY3a
        rw [hY3b, Z8.localUnits_extH_pTorsion_card_gcd p k' Lc wc, h1]
      haveI : Fintype (MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc) := Fintype.ofFinite _
      haveI : Fintype ((MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc) ⧸ Sbc.comap f) :=
        Fintype.ofFinite _
      -- corestriction is injective on the `p`-torsion at the level `Sbc.comap f`
      have hker : ∀ t : extH (Rep.res (Sbc.comap f).subtype
            (NK.HassePrinciple.localUnitsRep k Lc wc)) 2, p • t = 0 →
          Work.SSGRoute.extCor (Sbc.comap f) (unitRep (MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc))
            (NK.HassePrinciple.localUnitsRep k Lc wc) 2 t = 0 → t = 0 := by
        intro t ht h0
        refine Z8.extCor_injective_pTorsion_gcd (p := p)
          (G := MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc) (S := Sbc.comap f) ?_
          (NK.HassePrinciple.localUnitsRep k Lc wc) hcardS hcardG t ht h0
        rw [Subgroup.index_comap_of_surjective _ (decompK_restrict_surjective k K w Lc wc hwcw f hf),
          hSbc]
        exact hS₀idx
      -- the level-`Sbc.comap f` pairing vanishes
      have hP2 := detectLevels_levelPair_comapSubgroup_vanish (p := p) (S := Sbc) (f := f)
        (M := Rep.res (decompK (k := k) w).subtype M) (A := localUnitsK (k := k) w)
        (B := NK.HassePrinciple.localUnitsRep k Lc wc) ι hM y
        (fun t => hy Lc wc hwcw f hf ι hι t) hker (eH.symm hc)
      -- the interlacing identity of the base change
      have key := hY3eq (extRes Sbc.subtype y) (eH.symm hc)
      rw [AddEquiv.apply_symm_apply, hP2, map_zero] at key
      exact key
    -- descend from the closure to `L`
    have hP4 := Z8.levelPair_vanish_of_vanish_closure (k' := k') (K := K) w M'
      (eE (extRes Sbc.subtype y)) L w' hw' Lc wc hwcw' hwcw htop
    have hA : (MonoidHom.id (MulAction.stabilizer (K ≃ₐ[k'] K) w)).comp g = g :=
      MonoidHom.id_comp g
    have hB : Rep.resMap g (𝟙 (Rep.res (MonoidHom.id (MulAction.stabilizer (K ≃ₐ[k'] K) w))
        (localUnitsK (k := k') w))) ≫ ι₁ = ι₁ := by
      rw [resMap_id]
      exact Category.id_comp ι₁
    try rw [hA]
    rw [hB]
    exact hP4 g hg ι₁ hι₁ h
  -- detection at the base `k'`, where `D_w(K/k')` is a `p`-group
  have hD' : IsPGroup p (decompK (k := k') w) := isPGroup_decompK_fixedBase (k := k) w S₀ hS₀grp
  obtain ⟨u, z, hu, hz, hzm⟩ :=
    exists_localZetaCoeff p k' K w ζ hζ (detectLevels_fixedBase_zeta_fixed p k K ζ hζ w S₀ hS₀grp)
  let N' : Rep Coeff (decompK (k := k') w) := Rep.res (decompK (k := k') w).subtype M'
  haveI : Finite N' := ‹Finite M›
  have hN' : ∀ n : N', p • n = 0 := fun n => hM n
  have hdet : DetectAbove k' K w N' := detectAbove_pgroup p k' K w hD' z hz N' hN'
  have hy'0 : eE (extRes Sbc.subtype y) = 0 :=
    hdet K w (detectLevels_liesOver_self K w) (MonoidHom.id _)
      (fun σ => by
        rw [show galRes k' K K = MonoidHom.id (K ≃ₐ[k'] K) from
          AlgEquiv.restrictNormalHom_id k' K]
        rfl)
      (𝟙 _)
      (fun u => by
        rw [localAlgebraMapUnits_self K w (detectLevels_liesOver_self K w) u]
        rfl)
      _ hV'
  -- injectivity of the base change, then of the Sylow restriction
  have h1 : extRes Sbc.subtype y = 0 := by
    refine eE.injective ?_
    rw [map_zero]
    exact hy'0
  have h2 : extRes S₀.subtype y = 0 := by
    rw [← hSbc]
    exact h1
  haveI : Fintype (decompK (k := k) w) := Fintype.ofFinite _
  haveI : Fintype ((decompK (k := k) w) ⧸ S₀) := Fintype.ofFinite _
  haveI : Finite (Rep.res (decompK (k := k) w).subtype M) := ‹Finite M›
  have hgoal : extRes S₀.subtype y =
      extRes S₀.subtype (0 : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w) 1) := by
    rw [h2]
    exact (map_zero ((Rep.resFunctor S₀.subtype).mapExtAddHom
      (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)).symm
  exact extRes_injective_of_index (p := p) (S := S₀) hS₀idx
    (Rep.res (decompK (k := k) w).subtype M) hM (localUnitsK (k := k) w) hgoal

end Work.SSGRoute
