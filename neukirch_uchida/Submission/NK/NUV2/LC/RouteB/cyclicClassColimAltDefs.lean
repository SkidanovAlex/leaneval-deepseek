import Mathlib
import Submission.NK.NUV2.LC.RouteB.exists_muColim_avatar
import Submission.NK.NUV2.LC.RouteB.muToH2_add
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic
import Submission.NK.NUV2.RouteE.levelSymbol
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.NUV2.LC.finiteSupportTwistDefs
import Submission.NK.CFTLib.IdeleHasse.Descent.transferLevels
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite

/-!
# The cyclic-algebra class of Route 2: the class `X` and its elementary properties

This module contains the *concrete* class `X : Fˣ → H²(G_F, Z/p)` of the target statement
`NK.NUV2.LC.RouteB.cyclicClassColimAlt`, built from Route C's cyclic-algebra class
`NK.NUV2.RouteC.powHom b (deltaHomChar · χ)`, together with its elementary properties
(additivity, the global norm criterion).  It is separated from the target file so that lemmas about
`X` can be stated and proved without importing the (still open) target statement.

## The construction

* `routeCClass` — Route C's class `b ∪ δχ` in `H²(Gal(E/F), Eˣ)`;
* `unitsLevelEquiv` — a fixed transport `H²(LevelGroup ⊤ ⟨E⟩, Eˣ) ≃+ H²(Gal(E/F), Eˣ)`
  (`NK.NUV2.LC.RouteB.nonempty_addEquiv_unitsLevelH2_top`);
* `cyclicGamma b` — the image of Route C's class in the *units colimit* `H2Units ⊤`, i.e.
  `H2Units.ofLevel ⊤ ⟨E⟩ (unitsLevelEquiv.symm (routeCClass b))`.  Because the level-`E`
  representative is visible, this is the form in which the localisation dictionary can be proved;
* `cyclicAvatarY` — the `μ_p`-avatar of `cyclicGamma`, i.e. a chosen preimage under
  `NK.HassePrinciple.kummerColim` (existence from
  `NK.NUV2.ABHN.kummerColim_surjective_pTorsion`);
* `cyclicClassMap` — the class `X b := muToH2 (Y b)` of the target statement.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace NK.NUV2.LC.RouteB

/-- **Route C's cyclic-algebra class** `b ∪ δχ` in `H²(Gal(E/F), Eˣ)`: the cup product of `b`
(in the `H⁰`-slot, via `NK.NUV2.RouteC.powHom`) with the class `δχ` attached to the character
`χ` (`NK.NUV2.RouteC.deltaHomChar`). -/
noncomputable def routeCClass {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (χ : Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ) (b : Fˣ) :
    (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) :=
  (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E)) (NK.NUV2.RouteC.powHom (F := F) (E := E) b) 2)
    ((NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E)) χ)

/-- **A fixed faithful character** of the (finite cyclic) Galois group of `E/F`. -/
noncomputable def faithfulChar {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E)) :
    Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ :=
  Classical.choose (exists_faithful_character_of_isCyclic' (G := E ≃ₐ[F] E) hcyc)

/-- The defining property of `faithfulChar`. -/
theorem faithfulChar_spec {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E)) :
    addOrderOf (faithfulChar hcyc) = Nat.card (E ≃ₐ[F] E) :=
  Classical.choose_spec (exists_faithful_character_of_isCyclic' (G := E ≃ₐ[F] E) hcyc)

/-- The character generating the cyclic class at the level `E` (an abbreviation for
`faithfulChar`). -/
noncomputable abbrev levelChar {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E)) :
    Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ :=
  faithfulChar hcyc


/-! ## The `LevelGroup`-based units localisation

The localisation of the units level cohomology at a place, expressed in the `LevelGroup`
vocabulary.  These are copies of the definitions of
`Submission/Work/NUV2/LC/RouteB/level_kills_aux.lean` (that module cannot be imported together with
`muColimEquivH2ProfiniteOfIsPrimitiveRoot`: they define the same name `NK.NUV2.ABHN.levelCompare`
with different types), renamed with the prefix `lvl`. -/

/-- The base field of a level: the fixed field of the image of `V` in `Gal(L/K)`. -/
noncomputable abbrev lvlBase {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    IntermediateField K (↥L) :=
  IntermediateField.fixedField (V.map (NK.HassePrinciple.levelRestrict L))

/-- The level-group dictionary. -/
noncomputable def lvlGroupEquiv {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LevelGroup V L ≃* Gal(↥L/↥(lvlBase V L)) :=
  NK.HassePrinciple.levelGroupMulEquivLevelGalois V L

/-- The transport from the `LevelGroup`-based units level cohomology to the number-field units
cohomology. -/
noncomputable def lvlUnitsLift {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L ≃+
      (groupCohomology (NK.HassePrinciple.unitsRep (↥(lvlBase V L)) (↥L)) 2) := by
  refine ((groupCohomology.mapIso (A := NK.HassePrinciple.unitsRep (↥(lvlBase V L)) (↥L))
    (B := NK.HassePrinciple.unitsLevelRep V L)
    (lvlGroupEquiv V L)
    (LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive (↥L)ˣ)) ?_ 2).toLinearEquiv).toAddEquiv
  intro g
  induction g using QuotientGroup.induction_on with
  | H v => simp only [NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl

/-- **The `LevelGroup`-based units localisation** at a place of the level field. -/
noncomputable abbrev lvlLoc {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (w : NK.GlobalCFT.Place ↥L)
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) :=
  (NK.HassePrinciple.locUnits (↥(lvlBase V L)) (↥L) w).hom ((lvlUnitsLift V L) b)

section Main

variable (F : Type) [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
  [IsSepClosure F F'] (E : IntermediateField F F') [FiniteDimensional F E] [IsGalois F E]
  [NumberField ↥E]

/-- **The transport between the level-`E` units cohomology and the Galois cohomology
`H²(Gal(E/F), Eˣ)`** (a fixed choice from
`NK.NUV2.LC.RouteB.nonempty_addEquiv_unitsLevelH2_top`). -/
noncomputable def unitsLevelEquiv :
    (NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) ⟨E⟩) ≃+
      (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥E) 2) :=
  Classical.choice (nonempty_addEquiv_unitsLevelH2_top (F := F) (F' := F') ⟨E⟩)

/-- **The cyclic-algebra class in the units colimit**, with a *visible* level-`E`
representative. -/
noncomputable def cyclicGamma (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) :
    Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) :=
  fun b => NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) ⟨E⟩
    ((unitsLevelEquiv F F' E).symm
      (routeCClass (levelChar (F := F) (E := ↥E) hcyc) b))

/-- The defining property of `cyclicGamma`: it is the class of the level-`E` representative. -/
theorem cyclicGamma_apply (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (b : Fˣ) :
    cyclicGamma F F' E hcyc b =
      NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) ⟨E⟩
        ((unitsLevelEquiv F F' E).symm
          (routeCClass (levelChar (F := F) (E := ↥E) hcyc) b)) := rfl

/-- **The additivity of the cyclic-algebra class in the units colimit.** -/
theorem cyclicGamma_add (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (b₁ b₂ : Fˣ) :
    cyclicGamma F F' E hcyc (b₁ * b₂) =
      cyclicGamma F F' E hcyc b₁ + cyclicGamma F F' E hcyc b₂ := by
  rw [cyclicGamma_apply, cyclicGamma_apply, cyclicGamma_apply]
  have hmap : routeCClass (levelChar (F := F) (E := ↥E) hcyc) (b₁ * b₂) =
      routeCClass (levelChar (F := F) (E := ↥E) hcyc) b₁ +
        routeCClass (levelChar (F := F) (E := ↥E) hcyc) b₂ := by
    show (groupCohomology.map (MonoidHom.id (↥E ≃ₐ[F] ↥E))
        (NK.NUV2.RouteC.powHom (F := F) (E := ↥E) (b₁ * b₂)) 2)
        ((NK.NUV2.RouteC.deltaHomChar (↥E ≃ₐ[F] ↥E)) _) = _
    rw [NK.NUV2.RouteC.powHom_mul]
    exact NK.NUV2.RouteE.map_add_apply _ _ _ _
  rw [hmap, map_add, NK.NUV2.ABHN.H2Units.ofLevel_add]

/-- **The vanishing criterion for the level-`E` representative**: the representative vanishes if
and only if `b` is a global norm (Route C). -/
theorem unitsLevelEquiv_symm_eq_zero_iff (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (b : Fˣ) :
    (unitsLevelEquiv F F' E).symm (routeCClass (levelChar (F := F) (E := ↥E) hcyc) b) = 0 ↔
      b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F)) := by
  have h0 : (unitsLevelEquiv F F' E).symm 0 = 0 := map_zero _
  rw [← h0, (unitsLevelEquiv F F' E).symm.injective.eq_iff]
  exact NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic (F := F) (E := ↥E)
    hcyc (levelChar (F := F) (E := ↥E) hcyc) (faithfulChar_spec hcyc) b

/-- **The global norm criterion for `cyclicGamma`.** -/
theorem cyclicGamma_eq_zero_iff (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (b : Fˣ) :
    cyclicGamma F F' E hcyc b = 0 ↔
      b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F)) := by
  have hinj := H2Units_ofLevel_injective_top (F := F) (F' := F') ⟨E⟩
  rw [cyclicGamma_apply]
  constructor
  · intro h
    have h' : (unitsLevelEquiv F F' E).symm (routeCClass (levelChar (F := F) (E := ↥E) hcyc) b) = 0 := by
      apply hinj
      rw [h, H2Units_ofLevel_zero]
    exact (unitsLevelEquiv_symm_eq_zero_iff F F' E hcyc b).mp h'
  · intro h
    rw [(unitsLevelEquiv_symm_eq_zero_iff F F' E hcyc b).mpr h, H2Units_ofLevel_zero]

/-- **`p • cyclicGamma b = 0`**: the cyclic-algebra class is `p`-torsion. -/
theorem cyclicGamma_p_torsion (p : ℕ) (hp : p.Prime) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E))
    (hdeg : Module.finrank F E = p) (b : Fˣ) :
    p • cyclicGamma F F' E hcyc b = 0 := by
  have hpow : ∀ n : ℕ, cyclicGamma F F' E hcyc (b ^ n) = n • cyclicGamma F F' E hcyc b := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, zero_nsmul]
      exact (cyclicGamma_eq_zero_iff F F' E hcyc 1).mpr
        ⟨Units.map (algebraMap F ↥E : F →* ↥E) 1, by simp⟩
    | succ k ih => rw [pow_succ, cyclicGamma_add, ih, succ_nsmul]
  have hb : cyclicGamma F F' E hcyc (b ^ p) = 0 := by
    rw [cyclicGamma_eq_zero_iff]
    refine ⟨Units.map (algebraMap F ↥E : F →* ↥E) b, ?_⟩
    haveI : Module.Free F ↥E := Module.Free.of_divisionRing F ↥E
    have h := Algebra.norm_algebraMap (R := F) (S := ↥E) (b : F)
    rw [hdeg] at h
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map]
    exact h
  rw [← hpow p]
  exact hb

/-- **The `μ_p`-avatar of the cyclic-algebra class** (existence from
`NK.NUV2.ABHN.kummerColim_surjective_pTorsion`). -/
noncomputable def cyclicAvatarY (p : ℕ) (hp : p.Prime) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E))
    (hdeg : Module.finrank F E = p) :
    Fˣ → NK.HassePrinciple.MuColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) :=
  fun b => Classical.choose (NK.NUV2.ABHN.kummerColim_surjective_pTorsion (K := F) (K' := F')
    p hp (cyclicGamma F F' E hcyc b) (cyclicGamma_p_torsion F F' E p hp hcyc hdeg b))

/-- The defining property of the avatar. -/
theorem kummerColim_cyclicAvatarY (p : ℕ) (hp : p.Prime) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E))
    (hdeg : Module.finrank F E = p) (b : Fˣ) :
    NK.HassePrinciple.kummerColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))
      (cyclicAvatarY F F' E p hp hcyc hdeg b) = cyclicGamma F F' E hcyc b :=
  Classical.choose_spec (NK.NUV2.ABHN.kummerColim_surjective_pTorsion (K := F) (K' := F')
    p hp (cyclicGamma F F' E hcyc b) (cyclicGamma_p_torsion F F' E p hp hcyc hdeg b))

/-- **The additivity of the avatar** (from the injectivity of the Kummer map on the colimits). -/
theorem cyclicAvatarY_add (p : ℕ) (hp : p.Prime) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E))
    (hdeg : Module.finrank F E = p) (b₁ b₂ : Fˣ) :
    cyclicAvatarY F F' E p hp hcyc hdeg (b₁ * b₂) =
      cyclicAvatarY F F' E p hp hcyc hdeg b₁ + cyclicAvatarY F F' E p hp hcyc hdeg b₂ := by
  refine NK.HassePrinciple.kummerColim_injective (K := F) (K' := F') p hp
    (⊤ : Subgroup Gal(F'/F)) ?_
  rw [kummerColim_add, kummerColim_cyclicAvatarY, kummerColim_cyclicAvatarY,
    kummerColim_cyclicAvatarY, cyclicGamma_add]

/-- **The global norm criterion for the avatar.** -/
theorem cyclicAvatarY_eq_zero_iff (p : ℕ) (hp : p.Prime) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E))
    (hdeg : Module.finrank F E = p) (b : Fˣ) :
    cyclicAvatarY F F' E p hp hcyc hdeg b = 0 ↔
      b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F)) := by
  rw [← (NK.HassePrinciple.kummerColim_injective (K := F) (K' := F') p hp
      (⊤ : Subgroup Gal(F'/F))).eq_iff,
    kummerColim_cyclicAvatarY, kummerColim_zero, cyclicGamma_eq_zero_iff]

/-- **The cyclic-algebra class of the target statement**: `X b := muToH2 (Y b)`. -/
noncomputable def cyclicClassMap (p : ℕ) (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (hdeg : Module.finrank F E = p) :
    Fˣ → NK.BrauerHasse.H2Profinite (K := F) (K' := F') p ⊤ :=
  fun b => @NK.NUV2.ABHN.muToH2 F F' _ _ _ _ p ⟨hp.ne_zero⟩ ζ hζ
    (cyclicAvatarY F F' E p hp hcyc hdeg b)

/-- The unfolding rule for `cyclicClassMap`. -/
theorem cyclicClassMap_apply (p : ℕ) (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (hdeg : Module.finrank F E = p) (b : Fˣ) :
    cyclicClassMap F F' E p hp hζ hcyc hdeg b =
      @NK.NUV2.ABHN.muToH2 F F' _ _ _ _ p ⟨hp.ne_zero⟩ ζ hζ
        (cyclicAvatarY F F' E p hp hcyc hdeg b) := rfl

/-- `muToH2` kills `0`. -/
theorem muToH2_zero (p : ℕ) (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    @NK.NUV2.ABHN.muToH2 F F' _ _ _ _ p ⟨hp.ne_zero⟩ ζ hζ
      (0 : NK.HassePrinciple.MuColim (K := F) (K' := F') p ⊤) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := muToH2_add (K := F) (K' := F') p hζ
    (0 : NK.HassePrinciple.MuColim (K := F) (K' := F') p ⊤) 0
  rw [zero_add] at h
  exact (add_left_cancel (a := NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ 0) (b := 0)
    (by rw [add_zero]; exact h)).symm

/-- **Additivity of the cyclic-algebra class** `X`. -/
theorem cyclicClassMap_add (p : ℕ) (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (hdeg : Module.finrank F E = p) (b₁ b₂ : Fˣ) :
    cyclicClassMap F F' E p hp hζ hcyc hdeg (b₁ * b₂) =
      cyclicClassMap F F' E p hp hζ hcyc hdeg b₁ +
        cyclicClassMap F F' E p hp hζ hcyc hdeg b₂ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [cyclicClassMap_apply, cyclicClassMap_apply, cyclicClassMap_apply,
    cyclicAvatarY_add F F' E p hp hcyc hdeg b₁ b₂, muToH2_add]

/-- **The global norm criterion for the cyclic-algebra class** `X`. -/
theorem cyclicClassMap_eq_zero_iff (p : ℕ) (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) (hdeg : Module.finrank F E = p) (b : Fˣ) :
    cyclicClassMap F F' E p hp hζ hcyc hdeg b = 0 ↔
      b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hz := muToH2_zero F F' p hp hζ
  have hiff : cyclicClassMap F F' E p hp hζ hcyc hdeg b = 0 ↔
      cyclicAvatarY F F' E p hp hcyc hdeg b = 0 := by
    constructor
    · intro h
      have h1 : NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ
          (cyclicAvatarY F F' E p hp hcyc hdeg b) =
            NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ 0 := by
        rw [hz]; exact (cyclicClassMap_apply F F' E p hp hζ hcyc hdeg b).symm.trans h
      exact NK.NUV2.ABHN.muColimEquiv (K := F) (K' := F') p hζ |>.injective h1
    · intro h
      rw [cyclicClassMap_apply, h, hz]
  exact hiff.trans (cyclicAvatarY_eq_zero_iff F F' E p hp hcyc hdeg b)

end Main

end NK.NUV2.LC.RouteB
