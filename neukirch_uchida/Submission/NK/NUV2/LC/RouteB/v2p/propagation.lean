import Mathlib
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.NUV2.LC.RouteB.unitsLift_kummerLevel
import Submission.NK.NUV2.LC.RouteB.v2.towerEqZeroAux
import Submission.NK.CFTLib.HRclean.ARLClean
import Submission.NK.HassePrinciple.UnitsColimit
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique

/-!
# Propagation of the `locL`-vanishing under inflation (Route B, fibre world)

`NK.NUV2.LC.RouteB.v2p.locL_unitsLevelMap_eq_zero`: for finite Galois levels `L ≤ M` of `K'/K`,
a subgroup `V ≤ Gal(K'/K)` with `Gal(K'/L) ≤ V`, a class `b ∈ H²(LevelGroup V L, Lˣ)` and places
`w` of `↥L`, `w'` of `↥M` with `w' | w`, the vanishing of `locL V L w b` implies the vanishing of
`locL V M w' (unitsLevelMap V hLM b)`.

The proof follows `Submission/Work/NUV2/LC/RouteB/v3/LevelChangeSquare.lean` and `v3/_dev2.lean`, but
is written in the *fibre* world (`locUnits_tower_fibre` / `RouteBDeps`), so that it can be imported
together with the assembly `NK.NUV2.LC.RouteB.v2.assembly` and the fibre lemma
`NK.NUV2.LC.RouteB.v2.locL_unitsLevelMap_fibre`:

* the two base fields `↥(levelBase V L)` and `↥(levelBase V M)` are canonically isomorphic (both are
  `K'^V`), and the induced identification of the Galois groups is the composite restriction
  `rhoRestrict`;
* the *level-change square* `locUnits_rhoRestrict_unitsInclRepM_eq` compares the localisations over
  the two bases;
* the *dictionary naturality* identifies the transport of `unitsLevelMap` with the transport of
  `unitsLift` along `rhoRestrict`.

The copies of `rhoRestrict` / `unitsInclRepM` used here come from
`Submission.NK.CFTLib.HRclean.ARLClean`, which is import-compatible with the fibre world (the
copies in `Submission.NK.NUV2.ARL.HR.TransferSupport` transitively import `locUnits_tower_eq_zero`
and therefore clash with the fibre world).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

open NK.GlobalCFT CategoryTheory
open NK.HassePrinciple

namespace NK.NUV2.LC.RouteB.v2p

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The base machinery for the change of base field -/

lemma mem_levelBase_iff (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (x : ↥(L : IntermediateField K K')) :
    x ∈ levelBase (K := K) (K' := K') V L ↔ (x : K') ∈ IntermediateField.fixedField V := by
  rw [levelBase, IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h v hv
    have h' : (NK.HassePrinciple.levelRestrict L v) x = x := h _ ⟨v, hv, rfl⟩
    have h2 := congrArg (fun y : ↥(L : IntermediateField K K') => (y : K')) h'
    exact (AlgEquiv.restrictNormal_commutes v (L : IntermediateField K K') x).symm.trans h2
  · intro h g hg
    obtain ⟨v, hv, rfl⟩ := hg
    refine (algebraMap ↥(L : IntermediateField K K') K').injective ?_
    exact (AlgEquiv.restrictNormal_commutes v (L : IntermediateField K K') x).trans (h v hv)

lemma fixedField_le_of_fixingSubgroup_le {L : FiniteGaloisIntermediateField K K'}
    {V : Subgroup Gal(K'/K)} (hF : L.fixingSubgroup ≤ V) :
    IntermediateField.fixedField V ≤ (L : IntermediateField K K') := by
  have h := IntermediateField.fixedField_le hF
  rwa [InfiniteGalois.fixedField_fixingSubgroup (L : IntermediateField K K')] at h

noncomputable def baseRingHom (V : Subgroup Gal(K'/K)) {L M : FiniteGaloisIntermediateField K K'}
    (hLM : (L : IntermediateField K K') ≤ (M : IntermediateField K K')) :
    ↥(levelBase V L) →+* ↥(levelBase V M) where
  toFun x := ⟨IntermediateField.inclusion hLM x.1,
    (mem_levelBase_iff V M _).mpr (by
      change ((IntermediateField.inclusion hLM x.1 : ↥(M : IntermediateField K K')) : K')
        ∈ IntermediateField.fixedField V
      rw [show ((IntermediateField.inclusion hLM x.1 : ↥(M : IntermediateField K K')) : K')
        = (x.1 : K') from rfl]
      exact (mem_levelBase_iff V L x.1).mp x.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.1 b.1)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a.1 b.1)

lemma baseRingHom_injective (V : Subgroup Gal(K'/K)) {L M : FiniteGaloisIntermediateField K K'}
    (hLM : (L : IntermediateField K K') ≤ (M : IntermediateField K K')) :
    Function.Injective (baseRingHom (K := K) (K' := K') V hLM) := by
  intro x y hxy
  have h : IntermediateField.inclusion hLM x.1 = IntermediateField.inclusion hLM y.1 :=
    congrArg Subtype.val hxy
  exact Subtype.ext ((IntermediateField.inclusion hLM).injective h)

lemma baseRingHom_surjective (V : Subgroup Gal(K'/K)) {L M : FiniteGaloisIntermediateField K K'}
    (hLM : (L : IntermediateField K K') ≤ (M : IntermediateField K K'))
    (hF : L.fixingSubgroup ≤ V) :
    Function.Surjective (baseRingHom (K := K) (K' := K') V hLM) := by
  intro y
  have hy : (y.1 : K') ∈ IntermediateField.fixedField V := (mem_levelBase_iff V M y.1).mp y.2
  have hyL : (y.1 : K') ∈ (L : IntermediateField K K') := fixedField_le_of_fixingSubgroup_le hF hy
  refine ⟨⟨⟨(y.1 : K'), hyL⟩, (mem_levelBase_iff V L _).mpr hy⟩, ?_⟩
  refine Subtype.ext ?_
  refine (algebraMap ↥(M : IntermediateField K K') K').injective ?_
  change (algebraMap ↥(M : IntermediateField K K') K')
      (IntermediateField.inclusion hLM ⟨(y.1 : K'), hyL⟩) =
    (algebraMap ↥(M : IntermediateField K K') K') y.1
  rw [show (algebraMap ↥(M : IntermediateField K K') K')
      (IntermediateField.inclusion hLM ⟨(y.1 : K'), hyL⟩)
      = ((⟨(y.1 : K'), hyL⟩ : ↥(L : IntermediateField K K')) : K') from rfl]
  rfl

noncomputable def baseRingEquiv (V : Subgroup Gal(K'/K)) {L M : FiniteGaloisIntermediateField K K'}
    (hLM : (L : IntermediateField K K') ≤ (M : IntermediateField K K'))
    (hF : L.fixingSubgroup ≤ V) :
    ↥(levelBase V L) ≃+* ↥(levelBase V M) :=
  RingEquiv.ofBijective (baseRingHom V hLM)
    ⟨baseRingHom_injective V hLM, baseRingHom_surjective V hLM hF⟩

/-! ## The level-change square for the `rhoRestrict`-localisation -/

section General

variable {K L M E : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Field E] [NumberField E] [Algebra K L] [Algebra K M] [Algebra K E]
  [Algebra L E] [Algebra M E] [IsScalarTower K L E] [IsScalarTower K M E]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
  [IsGalois K L] [IsGalois K M] [IsGalois K E] [IsGalois M E]

/-- The restriction map `Gal(E/M) →* Gal(L/K)` carries the stabiliser of a place `ŵ` of `E` into
the stabiliser of the place `v'` of `L` below it. -/
theorem rhoRestrict_smul_eq_of_fixes (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') (σ : E ≃ₐ[M] E) (hσ : σ • ŵ = ŵ) :
    (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ) • v' = v' := by
  have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := L) (L := E)
      (τ := σ.restrictScalars K)
      (A := NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ)
      (fun y => NK.CFTLib.HRclean.ARL.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) σ y) hv
  rw [show (σ.restrictScalars K) • ŵ = ŵ from hσ] at h1
  exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique h1 hv

/-- The induced map of stabilisers `Γ_ŵ^{E/M} →* Γ_{v'}^{L/K}`. -/
noncomputable def stabilizerMapRho (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    MulAction.stabilizer (E ≃ₐ[M] E) ŵ →* MulAction.stabilizer (L ≃ₐ[K] L) v' where
  toFun σ := ⟨NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1, by
    rw [MulAction.mem_stabilizer_iff]
    exact rhoRestrict_smul_eq_of_fixes ŵ v' hv σ.1 (MulAction.mem_stabilizer_iff.mp σ.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ.1 τ.1)

theorem stabilizerMapRho_subtype (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype.comp (stabilizerMapRho ŵ v' hv) =
      (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)).comp
        (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype :=
  MonoidHom.ext fun σ => rfl

/-- Cast of the local algebra map along a change of the place upstairs. -/
lemma localAlgebraMapUnits_cast_up {a a' : NK.GlobalCFT.Place E} {b b' : NK.GlobalCFT.Place L}
    (h1 : a = a') (h2 : b = b') (Ha : NK.GlobalCFT.Place.LiesOver a b)
    (H : NK.GlobalCFT.Place.LiesOver a' b') (x : (NK.GlobalCFT.Place.localField L b)ˣ) :
    h1 ▸ (NK.GlobalCFT.Place.localAlgebraMapUnits a b Ha x)
      = NK.GlobalCFT.Place.localAlgebraMapUnits a' b' H (h2 ▸ x) := by
  cases h1
  exact NK.HassePrinciple.localAlgebraMapUnits_cast a h2 Ha H x

/-- The local algebra map along a restriction of scalars. -/
lemma localRingEquiv_localAlgebraMapUnits_of_restrict' (ŵ : NK.GlobalCFT.Place E)
    (v' : NK.GlobalCFT.Place L) (σ : E ≃ₐ[M] E) (A : L ≃ₐ[K] L)
    (hA : ∀ y : L, algebraMap L E (A y) = σ (algebraMap L E y))
    {h : NK.GlobalCFT.Place.LiesOver ŵ v'}
    {h' : NK.GlobalCFT.Place.LiesOver (σ • ŵ) (A • v')}
    (a : (NK.GlobalCFT.Place.localField L v')ˣ) :
    Units.map (NK.GlobalCFT.Place.localRingEquiv σ ŵ).toMonoidHom
        (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' h a) =
      NK.GlobalCFT.Place.localAlgebraMapUnits (σ • ŵ) (A • v') h'
        (Units.map (NK.GlobalCFT.Place.localRingEquiv A v').toMonoidHom a) :=
  NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict (K := K) (F := L) (L := E)
    (τ := σ.restrictScalars K) A hA h h' a

/-- The local coefficient morphism `L_{v'}ˣ → E_ŵˣ` along the restriction
`Γ_ŵ^{E/M} →* Γ_{v'}^{L/K}`. -/
noncomputable def localUnitsMapRhoCoeff (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    Rep.res (stabilizerMapRho ŵ v' hv) (NK.HassePrinciple.localUnitsRep K L v') ⟶
      NK.HassePrinciple.localUnitsRep M E ŵ :=
  Rep.ofHom
    { toFun := ⇑(NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv).toAdditive
      map_add' := fun x y =>
        map_add (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul
          (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv
              (NK.HassePrinciple.localUnitsEquiv v'
                (stabilizerMapRho ŵ v' hv σ) (Additive.toMul x)))
            = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv ŵ σ
              (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv (Additive.toMul x)))
        congr 1
        set u : (NK.GlobalCFT.Place.localField L v')ˣ := Additive.toMul x with hu
        have hσ : σ.1 • ŵ = ŵ := MulAction.mem_stabilizer_iff.mp σ.2
        have hA : (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) • v' = v' :=
          rhoRestrict_smul_eq_of_fixes ŵ v' hv σ.1 hσ
        have hcoe : ∀ y : L, algebraMap L E
            ((NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) y)
            = σ.1 (algebraMap L E y) :=
          fun y => NK.CFTLib.HRclean.ARL.rhoRestrict_apply_coe (K := K) (L := L) (M := M) (E := E) σ.1 y
        have h' : NK.GlobalCFT.Place.LiesOver ((σ.1.restrictScalars K) • ŵ)
            ((NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) • v') :=
          NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := L) (L := E)
            (τ := σ.1.restrictScalars K)
            (A := NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1)
            hcoe hv
        have key := localRingEquiv_localAlgebraMapUnits_of_restrict' (K := K) (L := L) (M := M)
          (E := E) ŵ v' σ.1
          (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) hcoe
          (h := hv) (h' := h') u
        rw [show stabilizerMapRho ŵ v' hv σ =
            (⟨NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1, hA⟩ :
              MulAction.stabilizer (L ≃ₐ[K] L) v') from Subtype.ext rfl]
        rw [NK.NUV2.LC.RouteB.v2.localUnitsEquiv_eq_cast (F := K) (L := L),
          NK.NUV2.LC.RouteB.v2.localUnitsEquiv_eq_cast (F := M) (L := E)]
        rw [key]
        exact (localAlgebraMapUnits_cast_up
          (a := σ.1 • ŵ) (a' := ŵ) (b := (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M)
            (E := E) σ.1) • v') (b' := v') hσ hA h' hv
          (Units.map (NK.GlobalCFT.Place.localRingEquiv
            (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E) σ.1) v').toMonoidHom
            u)).symm }

/-- The local level map `H²(Γ_{v'}^{L/K}, L_{v'}ˣ) → H²(Γ_ŵ^{E/M}, E_ŵˣ)`. -/
noncomputable def localLevelMapRho (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    groupCohomology (NK.HassePrinciple.localUnitsRep K L v') 2 ⟶
      groupCohomology (NK.HassePrinciple.localUnitsRep M E ŵ) 2 :=
  groupCohomology.map (stabilizerMapRho ŵ v' hv)
      (𝟙 (Rep.res (stabilizerMapRho ŵ v' hv) (NK.HassePrinciple.localUnitsRep K L v'))) 2 ≫
    groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
      (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2

/-! ### The changes of level

We record the value of the two natural coefficient morphisms on elements of `Additive _`, which is
what the elementwise comparison of morphisms of representations reduces to. -/

@[simp] theorem unitsInclRepM_hom_ofMul (u : Lˣ) :
    (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)).hom (Additive.ofMul u)
      = Additive.ofMul (Units.map (algebraMap L E).toMonoidHom u) := rfl

@[simp] theorem localUnitsMapRhoCoeff_hom_ofMul (ŵ : NK.GlobalCFT.Place E)
    (v' : NK.GlobalCFT.Place L) (hv : NK.GlobalCFT.Place.LiesOver ŵ v')
    (x : (NK.GlobalCFT.Place.localField L v')ˣ) :
    (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv).hom (Additive.ofMul x)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ v' hv x) := rfl

/-- Naturality of the localisation on `L` in the coefficient morphism of the tower. -/
theorem localLevelMapRho_naturality_aux (ŵ : NK.GlobalCFT.Place E) (v' : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) v'))
        (NK.HassePrinciple.unitsToLocalUnits K L v') 2 ≫
      (groupCohomology.map (stabilizerMapRho ŵ v' hv)
          (𝟙 (Rep.res (stabilizerMapRho ŵ v' hv)
            (NK.HassePrinciple.localUnitsRep K L v'))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
          (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2)
      = groupCohomology.map (stabilizerMapRho ŵ v' hv)
          ((Rep.resFunctor (stabilizerMapRho ŵ v' hv)).map
              (NK.HassePrinciple.unitsToLocalUnits K L v') ≫
            localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2 := by
  rw [← Category.assoc]
  rw [← NK.NUV2.LC.RouteB.v2.map_resFunctor_map (stabilizerMapRho ŵ v' hv)
    (NK.HassePrinciple.unitsToLocalUnits K L v') 2]
  rw [← NK.NUV2.LC.RouteB.v2.map_f_comp_id (stabilizerMapRho ŵ v' hv)
    ((Rep.resFunctor (stabilizerMapRho ŵ v' hv)).map
      (NK.HassePrinciple.unitsToLocalUnits K L v'))
    (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2]

/-- **The square of level change.**  The composite
`H²(Gal(L/K), Lˣ) → H²(Gal(E/M), Eˣ) → H²(Γ_ŵ^{E/M}, E_ŵˣ)` (inflation along `L ⊆ E` followed by
restriction along `Gal(E/M) ⊆ Gal(E/K)` and localisation) equals the localisation at the place
`v'` below `ŵ` followed by the local level map `localLevelMapRho`. -/
theorem locUnits_rhoRestrict_unitsInclRepM_eq (ŵ : NK.GlobalCFT.Place E)
    (v' : NK.GlobalCFT.Place L) (hv : NK.GlobalCFT.Place.LiesOver ŵ v') :
    (groupCohomology.map (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E))
        (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := K) (L := L) (M := M) (E := E)) 2) ≫
      (NK.HassePrinciple.locUnits M E ŵ)
      = (NK.HassePrinciple.locUnits K L v') ≫
        (localLevelMapRho (K := K) (L := L) (M := M) (E := E) ŵ v' hv) := by
  rw [show (NK.HassePrinciple.locUnits M E ŵ) =
        (groupCohomology.map (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype
            (NK.HassePrinciple.unitsRep M E))) 2 ≫
         groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
          (NK.HassePrinciple.unitsToLocalUnits M E ŵ) 2) from rfl,
      show (NK.HassePrinciple.locUnits K L v') =
        (groupCohomology.map (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype
            (NK.HassePrinciple.unitsRep K L))) 2 ≫
         groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) v'))
          (NK.HassePrinciple.unitsToLocalUnits K L v') 2) from rfl]
  rw [show (localLevelMapRho (K := K) (L := L) (M := M) (E := E) ŵ v' hv) =
        (groupCohomology.map (stabilizerMapRho ŵ v' hv)
          (𝟙 (Rep.res (stabilizerMapRho ŵ v' hv)
            (NK.HassePrinciple.localUnitsRep K L v'))) 2 ≫
         groupCohomology.map (MonoidHom.id (MulAction.stabilizer (E ≃ₐ[M] E) ŵ))
          (localUnitsMapRhoCoeff (K := K) (L := L) (M := M) (E := E) ŵ v' hv) 2) from rfl]
  conv_lhs => rw [NK.NUV2.LC.RouteB.v2.map_id_comp_apply, ← groupCohomology.map_comp]
  conv_rhs => rw [Category.assoc]
  conv_rhs => rw [localLevelMapRho_naturality_aux (K := K) (L := L) (M := M) (E := E) ŵ v' hv]
  conv_rhs => rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr
    (G := MulAction.stabilizer (E ≃ₐ[M] E) ŵ) (H := L ≃ₐ[K] L)
    (A := NK.HassePrinciple.unitsRep K L)
    (B := NK.HassePrinciple.localUnitsRep M E ŵ)
    (f := (NK.CFTLib.HRclean.ARL.rhoRestrict (K := K) (L := L) (M := M) (E := E)).comp
      (MulAction.stabilizer (E ≃ₐ[M] E) ŵ).subtype)
    (g := (MulAction.stabilizer (L ≃ₐ[K] L) v').subtype.comp (stabilizerMapRho ŵ v' hv))
    (stabilizerMapRho_subtype ŵ v' hv).symm ?_ 2
  ext x
  conv_lhs => rw [← ofMul_toMul x]
  conv_rhs => rw [← ofMul_toMul x]
  simp only [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap, LinearMap.comp_apply,
    LinearMap.id_apply, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.id_apply,
    NK.HassePrinciple.unitsToLocalUnits_apply, unitsInclRepM_hom_ofMul,
    localUnitsMapRhoCoeff_hom_ofMul]
  exact (NK.NUV2.LC.RouteB.v2.localAlgebraMapUnits_algebraMap_units (L := L) (M := E) hv
    (Additive.toMul x)).symm


end General

theorem locL_unitsLevelMap_eq_zero {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup Gal(K'/K)) (L M : FiniteGaloisIntermediateField K K')
    (hLM : L ≤ M) (hF : L.fixingSubgroup ≤ V)
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L)
    {w : NK.GlobalCFT.Place ↥(L : IntermediateField K K')}
    {w' : NK.GlobalCFT.Place ↥(M : IntermediateField K K')}
    (hw : @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
      ((IntermediateField.inclusion hLM).toAlgebra) w' w)
    (hb : NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V L w b = 0) :
    NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w'
      ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) = 0 := by
  have hLM' : (L : IntermediateField K K') ≤ (M : IntermediateField K K') := hLM
  letI : Algebra ↥(levelBase V L) ↥(levelBase V M) := (baseRingHom V hLM').toAlgebra
  letI : Algebra ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') :=
    (IntermediateField.inclusion hLM').toAlgebra
  letI : Algebra ↥(levelBase V L) ↥(M : IntermediateField K K') :=
    ((algebraMap ↥(levelBase V M) ↥(M : IntermediateField K K')).comp (baseRingHom V hLM')).toAlgebra
  letI : SMul ↥(levelBase V L) ↥(levelBase V M) := Algebra.toSMul
  letI : SMul ↥(levelBase V M) ↥(M : IntermediateField K K') := Algebra.toSMul
  letI : SMul ↥(levelBase V L) ↥(M : IntermediateField K K') := Algebra.toSMul
  haveI : IsScalarTower ↥(levelBase V L) ↥(levelBase V M) ↥(M : IntermediateField K K') :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower ↥(levelBase V L) ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsGalois ↥(levelBase V L) ↥(levelBase V M) :=
    IsGalois.of_equiv_equiv (F := ↥(levelBase V M)) (E := ↥(levelBase V M))
      (M := ↥(levelBase V L)) (N := ↥(levelBase V M))
      (f := (baseRingEquiv V hLM' hF).symm) (g := RingEquiv.refl ↥(levelBase V M))
      (hcomp := by
        refine RingHom.ext fun x => ?_
        exact RingEquiv.apply_symm_apply (baseRingEquiv V hLM' hF) x)
  haveI : IsGalois ↥(levelBase V L) ↥(M : IntermediateField K K') :=
    IsGalois.of_equiv_equiv (F := ↥(levelBase V M)) (E := ↥(M : IntermediateField K K'))
      (M := ↥(levelBase V L)) (N := ↥(M : IntermediateField K K'))
      (f := (baseRingEquiv V hLM' hF).symm) (g := RingEquiv.refl ↥(M : IntermediateField K K'))
      (hcomp := by
        refine RingHom.ext fun x => ?_
        exact congrArg (algebraMap ↥(levelBase V M) ↥(M : IntermediateField K K'))
          (RingEquiv.apply_symm_apply (baseRingEquiv V hLM' hF) x))
  haveI : FiniteDimensional ↥(levelBase V L) ↥(levelBase V M) :=
    FiniteDimensional.of_surjective
      ({ toFun := baseRingHom V hLM'
         map_add' := map_add _
         map_smul' := fun c x => by
           simp only [Algebra.smul_def, map_mul]
           rfl } : ↥(levelBase V L) →ₗ[↥(levelBase V L)] ↥(levelBase V M))
      (fun y => baseRingHom_surjective V hLM' hF y)
  -- the bridge
  have hbridge_pt : ∀ σ : ↥(M : IntermediateField K K') ≃ₐ[↥(levelBase V M)]
      ↥(M : IntermediateField K K'),
      NK.CFTLib.HRclean.ARL.rhoRestrict (K := ↥(levelBase V L)) (L := ↥(L : IntermediateField K K'))
        (M := ↥(levelBase V M)) (E := ↥(M : IntermediateField K K')) σ
      = (levelGroupEquiv (K := K) (K' := K') V L)
          ((NK.BrauerHasse.levelQuotHom (U := V) hLM)
            ((levelGroupEquiv (K := K) (K' := K') V M).symm σ)) := by
    intro σ
    obtain ⟨g, rfl⟩ := (levelGroupEquiv (K := K) (K' := K') V M).surjective σ
    induction g using QuotientGroup.induction_on with
    | H v =>
      simp only [MulEquiv.symm_apply_apply]
      refine AlgEquiv.ext fun y => ?_
      refine (algebraMap ↥(L : IntermediateField K K') K').injective ?_
      have hcoe : ∀ z : ↥(L : IntermediateField K K'),
          (algebraMap ↥(M : IntermediateField K K') K')
            (algebraMap ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') z)
          = (algebraMap ↥(L : IntermediateField K K') K') z := fun z => rfl
      have hLHS : (algebraMap ↥(L : IntermediateField K K') K')
          (NK.CFTLib.HRclean.ARL.rhoRestrict (K := ↥(levelBase V L))
            (L := ↥(L : IntermediateField K K')) (M := ↥(levelBase V M))
            (E := ↥(M : IntermediateField K K'))
            ((levelGroupEquiv (K := K) (K' := K') V M) (QuotientGroup.mk v)) y)
          = (v : Gal(K'/K)) ((algebraMap ↥(L : IntermediateField K K') K') y) := by
        have h1 := congrArg (algebraMap ↥(M : IntermediateField K K') K')
          (NK.CFTLib.HRclean.ARL.rhoRestrict_apply_coe (K := ↥(levelBase V L))
            (L := ↥(L : IntermediateField K K')) (M := ↥(levelBase V M))
            (E := ↥(M : IntermediateField K K'))
            ((levelGroupEquiv (K := K) (K' := K') V M) (QuotientGroup.mk v)) y)
        rw [hcoe] at h1
        rw [h1]
        rw [NK.NUV2.LC.RouteB.levelGroupEquiv_apply]
        rw [NK.HassePrinciple.levelGroupRestrictHom_mk]
        rw [show (algebraMap ↥(M : IntermediateField K K') K')
              (((NK.HassePrinciple.levelRestrict M) (v : Gal(K'/K)))
                (algebraMap ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') y))
            = (v : Gal(K'/K)) ((algebraMap ↥(M : IntermediateField K K') K')
                (algebraMap ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') y))
            from AlgEquiv.restrictNormal_commutes (v : Gal(K'/K))
              (M : IntermediateField K K') _]
        rw [hcoe]
      have hRHS : (algebraMap ↥(L : IntermediateField K K') K')
          (((levelGroupEquiv (K := K) (K' := K') V L)
            ((NK.BrauerHasse.levelQuotHom (U := V) hLM) (QuotientGroup.mk v))) y)
          = (v : Gal(K'/K)) ((algebraMap ↥(L : IntermediateField K K') K') y) := by
        rw [NK.NUV2.LC.RouteB.levelGroupEquiv_apply]
        rw [show (NK.BrauerHasse.levelQuotHom (U := V) hLM) (QuotientGroup.mk v)
            = QuotientGroup.mk v from QuotientGroup.map_mk _ _ _ _ v]
        rw [NK.HassePrinciple.levelGroupRestrictHom_mk]
        exact AlgEquiv.restrictNormal_commutes (v : Gal(K'/K)) (L : IntermediateField K K') y
      rw [hLHS, hRHS]
  have hbridge_hom :
      (NK.BrauerHasse.levelQuotHom (U := V) hLM).comp
          (levelGroupEquiv (K := K) (K' := K') V M).symm.toMonoidHom
        = (levelGroupEquiv (K := K) (K' := K') V L).symm.toMonoidHom.comp
          (NK.CFTLib.HRclean.ARL.rhoRestrict (K := ↥(levelBase V L))
            (L := ↥(L : IntermediateField K K')) (M := ↥(levelBase V M))
            (E := ↥(M : IntermediateField K K'))) := by
    refine MonoidHom.ext fun σ => ?_
    simp only [MonoidHom.comp_apply]
    rw [hbridge_pt σ]
    simp
  -- the naturality of the level map under the dictionaries
  have hnat : ∀ b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L,
      (unitsLift (K := K) (K' := K') V M)
          ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b)
        = (groupCohomology.map
              (NK.CFTLib.HRclean.ARL.rhoRestrict (K := ↥(levelBase V L))
                (L := ↥(L : IntermediateField K K')) (M := ↥(levelBase V M))
                (E := ↥(M : IntermediateField K K')))
              (NK.CFTLib.HRclean.ARL.unitsInclRepM (K := ↥(levelBase V L))
                (L := ↥(L : IntermediateField K K')) (M := ↥(levelBase V M))
                (E := ↥(M : IntermediateField K K'))) 2).hom
            ((unitsLift (K := K) (K' := K') V L) b) := by
    intro b
    rw [unitsLift_apply, unitsLift_apply, NK.HassePrinciple.unitsLevelMap,
      groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]
    conv_lhs => rw [← ConcreteCategory.comp_apply]
    conv_rhs => rw [← ConcreteCategory.comp_apply]
    rw [← groupCohomology.map_comp]
    rw [← groupCohomology.map_comp]
    exact congrArg (fun (f : groupCohomology (NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V L) 2 ⟶
        groupCohomology (NK.HassePrinciple.unitsRep (↥(levelBase V M))
          (↥(M : IntermediateField K K'))) 2) => f.hom b)
      (groupCohomology.map_congr (A := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V L)
        (B := NK.HassePrinciple.unitsRep (↥(levelBase V M))
          (↥(M : IntermediateField K K'))) hbridge_hom (by
        ext x
        simp only [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap, LinearMap.comp_apply,
          LinearMap.id_apply, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.id_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.refl_apply, NK.HassePrinciple.unitsLevelMapCoeff_apply,
          NK.HassePrinciple.unitsInclLinearMap_apply, NK.HassePrinciple.unitsInclHom,
          NK.CFTLib.HRclean.ARL.unitsInclRepM, Rep.ofHom_hom,
          Representation.IntertwiningMap.toLinearMap_apply]
        rfl) 2)
  -- the assembly
  have key : (NK.HassePrinciple.locUnits ↥(levelBase V M) ↥(M : IntermediateField K K') w')
      ((unitsLift (K := K) (K' := K') V M)
        ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b)) = 0 := by
    rw [hnat b]
    have hsq := locUnits_rhoRestrict_unitsInclRepM_eq
      (K := ↥(levelBase V L)) (L := ↥(L : IntermediateField K K'))
      (M := ↥(levelBase V M)) (E := ↥(M : IntermediateField K K')) w' w hw
    have h2 := congrArg (fun f => f.hom ((unitsLift (K := K) (K' := K') V L) b)) hsq
    simp only [ConcreteCategory.comp_apply] at h2
    rw [h2]
    rw [show (NK.HassePrinciple.locUnits ↥(levelBase V L) ↥(L : IntermediateField K K') w).hom
        ((unitsLift (K := K) (K' := K') V L) b) = 0 from hb]
    exact map_zero _
  exact key

end NK.NUV2.LC.RouteB.v2p
