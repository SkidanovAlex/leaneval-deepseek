/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `MuColim 2 ⊤` and `H2Profinite 2 ⊤` are equivalent

At `p = 2` and in characteristic `0` the cyclotomic coefficient module `μ_2(L) = {±1}` is the
*trivial* `ℤ/2`-module at every finite Galois level `L`, and canonically identified with
`ZMod 2 = NK.BrauerHasse.Coeff 2`: `-1` is fixed by every field automorphism and it is the only
non-trivial square root of unity.  Consequently the two filtered systems

* `NK.HassePrinciple.MuColim 2 ⊤ = colim_L H²(Gal(L/K), μ_2(L))` (the `μ_p`-colimit of
  `Submission/Work/HassePrinciple/`, with coefficients `μ_2(L) ⊆ Lˣ`), and
* `NK.BrauerHasse.H2Profinite 2 ⊤ = colim_L H²(Gal(L/K), Z/2)` (the trivial-coefficient
  profinite cohomology of `Submission/Work/BrauerHasse/`)

have the same levels and the same transition maps, so their colimits are equivalent as types.
The levelwise comparison is the coefficient comparison
`NK.IndecomposedDeep.H2congrEquiv` of `Submission/Work/IndecomposedDeep/twistTwoComparison.lean`
(the "`μ_2`-twist is trivial" comparison, made available there for number fields and reproduced
here for arbitrary fields of characteristic `0`), assembled over the colimits through the
universal properties `NK.BrauerTwist.LevelSystem.lift` and `NK.BrauerHasse.H2Profinite.lift`.

## Main results

* `NK.NUV2.LC.muTwoAddEquiv` — the coefficient identification `μ_2(L) ≃+ Z/2`, natural for the
  inclusions `μ_2(L) → μ_2(L')` (`muTwoAddEquiv_muLevelInclLinearMap`) and equivariant for the
  (trivial) Galois action (`muTwoAddEquiv_equivariance`);
* `NK.NUV2.LC.levelCompare` — the induced levelwise equivalence of the level cohomologies,
  natural for the transition maps (`levelCompare_muLevelMap`);
* `NK.NUV2.LC.muColimEquiv` — the equivalence of the two colimits;
* `NK.NUV2.LC.muColimEquiv_h2Profinite` — the same, as a `Nonempty` statement.
-/

import Mathlib
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.IndecomposedDeep.twistTwoComparison
import Submission.NK.BrauerTwist.Profinite

open CategoryTheory Representation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

namespace NK.NUV2.LC

section Setup

variable {K K' : Type u} [Field K] [CharZero K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The triviality of the action on `μ_2` -/

/-- Every field automorphism fixes every second root of unity: the only second roots of unity are
`1` and `-1`, and both are fixed. -/
theorem rootsOfUnity_two_smul_eq_self {F : Type u} [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (x : ↥(rootsOfUnity 2 F)) : σ • x = x := by
  have hx : ((x : Fˣ) : F) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 2 (x : Fˣ)).mp x.2, Units.val_one]
  apply Subtype.ext
  rw [NK.HassePrinciple.coe_smul_rootsOfUnity]
  apply Units.ext
  rw [AlgEquiv.smul_units_def, Units.coe_map]
  rcases sq_eq_one_iff.mp hx with h1 | h1
  · rw [h1, map_one]
  · rw [h1]
    change (σ : F →+* F) (-1) = -1
    rw [map_neg, map_one]

/-- The twisted level representation `μ_2(L)`, with its universes pinned. -/
noncomputable abbrev muLevelRepTwo (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} NK.HassePrinciple.CoeffInt (NK.BrauerHasse.LevelGroup V L) :=
  NK.HassePrinciple.muLevelRep 2 V L

/-- The representation `μ_2(L)` of the level group is trivial in characteristic `0`. -/
lemma muLevelRep_two_rho_eq_self (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (g : NK.BrauerHasse.LevelGroup V L) (y : Additive ↥(rootsOfUnity 2 ↥L)) :
    (muLevelRepTwo V L).ρ g y = y := by
  show (NK.HassePrinciple.levelGroupRestrictHom V L g) • y = y
  refine Additive.toMul.injective ?_
  rw [show Additive.toMul ((NK.HassePrinciple.levelGroupRestrictHom V L g) • y)
      = (NK.HassePrinciple.levelGroupRestrictHom V L g) • Additive.toMul y from rfl]
  exact rootsOfUnity_two_smul_eq_self _ _

/-- In characteristic zero, `-1` is a primitive second root of unity of every intermediate field
of a separable closure. -/
theorem isPrimitiveRoot_neg_one_two_field (L : FiniteGaloisIntermediateField K K') :
    IsPrimitiveRoot (-1 : ↥L) 2 := by
  have h0 : IsPrimitiveRoot (-1 : K) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  simpa using h0.map_of_injective (algebraMap K ↥L).injective

/-! ## The coefficient identification `μ_2(L) ≃ Z/2`, uniformly in `L`

The identification is the composite

`μ_2(L) → μ_2(K')`  (the inclusion of the roots of unity of `L` into those of `K'`, an
isomorphism because both groups have the two elements `±1`) followed by a fixed identification
`μ_2(K') ≅ Z/2` (via the primitive root `-1`).  Building it this way makes the naturality in the
level inclusions immediate: both `μ_2(L) → μ_2(K')` and `μ_2(L) → μ_2(L') → μ_2(K')` are the
inclusion of the element in `K'`. -/

/-- The canonical identification `μ_2(L) ≃* μ_2(K')`, given by the inclusion `L ⊆ K'`. -/
noncomputable def ruTwoIso (L : FiniteGaloisIntermediateField K K') :
    ↥(rootsOfUnity 2 ↥L) ≃* ↥(rootsOfUnity 2 K') :=
  (Subgroup.equivMapOfInjective (rootsOfUnity 2 ↥L) (Units.map (algebraMap ↥L K'))
    (Units.map_injective (algebraMap ↥L K').injective)).trans
  (MulEquiv.subgroupCongr
    (IsPrimitiveRoot.map_rootsOfUnity (isPrimitiveRoot_neg_one_two_field L)
      (algebraMap ↥L K').injective))

/-- `ruTwoIso` does not change the underlying element of `K'`. -/
lemma ruTwoIso_coe (L : FiniteGaloisIntermediateField K K') (y : ↥(rootsOfUnity 2 ↥L)) :
    (((ruTwoIso L y : ↥(rootsOfUnity 2 K')) : (K')ˣ) : K') = ((y : (↥L)ˣ) : K') := by
  rw [ruTwoIso, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply, Units.coe_map]
  rfl

/-- `ruTwoIso` is natural for the coefficient inclusions of the level system. -/
lemma ruTwoIso_muLevelIncl {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (y : ↥(rootsOfUnity 2 ↥L)) :
    ruTwoIso L' (NK.HassePrinciple.muLevelIncl 2 L L' h y) = ruTwoIso L y := by
  apply Subtype.ext
  apply Units.ext
  rw [ruTwoIso_coe, ruTwoIso_coe]
  rfl

/-- A fixed identification `Z/2 ≃+ μ_2(K')`, through the primitive root `-1`. -/
noncomputable def ruAddEquivTwo :
    ULift.{u,0} (ZMod 2) ≃+ Additive ↥(rootsOfUnity 2 K') :=
  let h : IsPrimitiveRoot (-1 : K') 2 := by
    have h0 : IsPrimitiveRoot (-1 : K) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
    simpa using h0.map_of_injective (algebraMap K K').injective
  let hζ : IsPrimitiveRoot (h.isUnit (by norm_num)).unit 2 :=
    IsPrimitiveRoot.isUnit_unit (by norm_num) h
  (AddEquiv.ulift (α := ZMod 2)).trans
    ((IsPrimitiveRoot.zmodEquivZPowers hζ).trans
      (MulEquiv.toAdditive (MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq hζ))))

/-- **The coefficient identification `μ_2(L) ≃+ Z/2`.** -/
noncomputable def muTwoAddEquiv (L : FiniteGaloisIntermediateField K K') :
    Additive ↥(rootsOfUnity 2 ↥L) ≃+ NK.BrauerHasse.Coeff.{u} 2 :=
  (MulEquiv.toAdditive (ruTwoIso L)).trans (ruAddEquivTwo (K := K) (K' := K')).symm

/-- The coefficient inclusion `μ_2(L) → μ_2(L')` of the level system, with its universes pinned. -/
noncomputable abbrev muLevelInclLinearMapTwo {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') :
    Additive ↥(rootsOfUnity 2 ↥L) →ₗ[NK.HassePrinciple.CoeffInt.{u}]
      Additive ↥(rootsOfUnity 2 ↥L') :=
  NK.HassePrinciple.muLevelInclLinearMap 2 L L' h

/-- **Naturality of the coefficient identification for the coefficient inclusions.** -/
lemma muTwoAddEquiv_muLevelInclLinearMap {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(rootsOfUnity 2 ↥L)) :
    muTwoAddEquiv L' (muLevelInclLinearMapTwo h x) = muTwoAddEquiv L x := by
  have hnat := ruTwoIso_muLevelIncl h (Additive.toMul x)
  have h2 : muTwoAddEquiv L' (muLevelInclLinearMapTwo h x)
      = (ruAddEquivTwo (K := K) (K' := K')).symm
          (Additive.ofMul
            (ruTwoIso L' (NK.HassePrinciple.muLevelIncl 2 L L' h (Additive.toMul x)))) := rfl
  rw [h2, hnat]
  rfl

/-! ## The comparison of the level cohomologies -/

/-- The trivial level representation `Z/2` of the level group. -/
noncomputable def trivLevelRep (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} (NK.BrauerHasse.Coeff.{u} 2) (NK.BrauerHasse.LevelGroup V L) :=
  Rep.trivial (NK.BrauerHasse.Coeff.{u} 2) (NK.BrauerHasse.LevelGroup V L)
    (NK.BrauerHasse.Coeff.{u} 2)

/-- **The coefficient identification is equivariant for the (trivial) actions** of the level
group on `μ_2(L)` and on `Z/2`. -/
theorem muTwoAddEquiv_equivariance (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    ∀ (g : NK.BrauerHasse.LevelGroup V L) (y : Additive ↥(rootsOfUnity 2 ↥L)),
      muTwoAddEquiv L ((muLevelRepTwo V L).ρ g y) = (trivLevelRep V L).ρ g (muTwoAddEquiv L y) := by
  intro g y
  show muTwoAddEquiv L ((muLevelRepTwo V L).ρ g y) = muTwoAddEquiv L y
  rw [muLevelRep_two_rho_eq_self V L g y]

/-- **The levelwise comparison** of the `μ_2`-cohomology and the trivial-coefficient cohomology. -/
noncomputable def levelCompare (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.MuLevelH2 2 V L ≃
      NK.BrauerHasse.H2 2 (NK.BrauerHasse.LevelGroup V L) :=
  NK.IndecomposedDeep.H2congrEquiv (A := muLevelRepTwo V L) (B := trivLevelRep V L)
    (muTwoAddEquiv L) (muTwoAddEquiv_equivariance V L)

/-- **Naturality of the levelwise comparison for the transition maps.** -/
lemma levelCompare_muLevelMap (V : Subgroup Gal(K'/K)) {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') (a : NK.HassePrinciple.MuLevelH2 2 V L) :
    levelCompare V L' (NK.HassePrinciple.muLevelMap 2 V h a) =
      NK.BrauerHasse.levelMap 2 (U := V) h (levelCompare V L a) := by
  show NK.IndecomposedDeep.H2congr (muTwoAddEquiv L') (muTwoAddEquiv_equivariance V L')
        (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h)
          (NK.HassePrinciple.muLevelMapCoeff 2 V h) 2 a) =
      (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h)
        (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := V) h)) 2)
        (NK.IndecomposedDeep.H2congr (muTwoAddEquiv L) (muTwoAddEquiv_equivariance V L) a)
  exact NK.IndecomposedDeep.H2congr_map (NK.BrauerHasse.levelQuotHom (U := V) h)
    (NK.HassePrinciple.muLevelMapCoeff 2 V h)
    (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := V) h))
    (muTwoAddEquiv L) (muTwoAddEquiv L')
    (muTwoAddEquiv_equivariance V L) (muTwoAddEquiv_equivariance V L')
    (fun x => by
      change (muTwoAddEquiv L') (muLevelInclLinearMapTwo h x) = (muTwoAddEquiv L) x
      exact muTwoAddEquiv_muLevelInclLinearMap (L := L) (L' := L') h x) a

/-! ## The comparison of the colimits -/

/-- The comparison map from the `μ_2`-colimit to the trivial-coefficient profinite cohomology. -/
noncomputable def muToH2 :
    NK.HassePrinciple.MuColim (K := K) (K' := K') 2 ⊤ →
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 ⊤ :=
  (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).lift
    (fun L a => NK.BrauerHasse.H2Profinite.ofLevel L (levelCompare ⊤ L a))
    (by
      intro L L' h a
      show NK.BrauerHasse.H2Profinite.ofLevel L'
          (levelCompare ⊤ L' (NK.HassePrinciple.muLevelMap 2 ⊤ h a)) = _
      rw [levelCompare_muLevelMap ⊤ h a, NK.BrauerHasse.H2Profinite.ofLevel_levelMap])

/-- The comparison map from the trivial-coefficient profinite cohomology to the `μ_2`-colimit. -/
noncomputable def h2ToMu :
    NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 ⊤ →
      NK.HassePrinciple.MuColim (K := K) (K' := K') 2 ⊤ :=
  NK.BrauerHasse.H2Profinite.lift (p := 2) (U := ⊤)
    (fun L b => NK.HassePrinciple.MuColim.ofLevel 2 ⊤ L ((levelCompare ⊤ L).symm b))
    (by
      intro L L' h b
      have key : (levelCompare ⊤ L').symm (NK.BrauerHasse.levelMap 2 (U := ⊤) h b) =
          NK.HassePrinciple.muLevelMap 2 ⊤ h ((levelCompare ⊤ L).symm b) := by
        have h1 := levelCompare_muLevelMap ⊤ h ((levelCompare ⊤ L).symm b)
        rw [Equiv.apply_symm_apply] at h1
        exact ((levelCompare ⊤ L').symm_apply_eq).mpr h1.symm
      rw [key]
      exact NK.BrauerTwist.LevelSystem.ofLevel_map
        (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤) h
        ((levelCompare ⊤ L).symm b))

/-- The computation rule for `muToH2` on the class of a level. -/
lemma muToH2_ofLevel (L : FiniteGaloisIntermediateField K K')
    (a : (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).obj L) :
    muToH2 ((NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).ofLevel L a) =
      NK.BrauerHasse.H2Profinite.ofLevel L (levelCompare ⊤ L a) := rfl

/-- The computation rule for `h2ToMu` on the class of a level. -/
lemma h2ToMu_ofLevel (L : FiniteGaloisIntermediateField K K')
    (b : NK.BrauerHasse.LevelH2 2 ⊤ L) :
    h2ToMu (NK.BrauerHasse.H2Profinite.ofLevel L b) =
      (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).ofLevel L
        ((levelCompare ⊤ L).symm b) := rfl

/-- The two comparison maps are inverse on the levels. -/
lemma h2ToMu_muToH2_ofLevel (L : FiniteGaloisIntermediateField K K')
    (a : (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).obj L) :
    h2ToMu (muToH2 ((NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).ofLevel L a)) =
      (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).ofLevel L a :=
  (congrArg h2ToMu (muToH2_ofLevel L a)).trans
    ((h2ToMu_ofLevel L (levelCompare ⊤ L a)).trans
      (congrArg ((NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤).ofLevel L)
        (Equiv.symm_apply_apply (levelCompare ⊤ L) a)))

/-- The two comparison maps are inverse on the levels (other direction). -/
lemma muToH2_h2ToMu_ofLevel (L : FiniteGaloisIntermediateField K K')
    (b : NK.BrauerHasse.LevelH2 2 ⊤ L) :
    muToH2 (h2ToMu (NK.BrauerHasse.H2Profinite.ofLevel L b)) =
      NK.BrauerHasse.H2Profinite.ofLevel L b :=
  (congrArg muToH2 (h2ToMu_ofLevel L b)).trans
    ((muToH2_ofLevel L ((levelCompare ⊤ L).symm b)).trans
      (congrArg (NK.BrauerHasse.H2Profinite.ofLevel L)
        (Equiv.apply_symm_apply (levelCompare ⊤ L) b)))

lemma muToH2_left_inv :
    Function.LeftInverse (h2ToMu (K := K) (K' := K')) (muToH2 (K := K) (K' := K')) := by
  intro x
  obtain ⟨L, a, rfl⟩ :=
    NK.BrauerTwist.LevelSystem.ofLevel_surjective
      (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') 2 ⊤) x
  exact h2ToMu_muToH2_ofLevel L a

lemma muToH2_right_inv :
    Function.RightInverse (h2ToMu (K := K) (K' := K')) (muToH2 (K := K) (K' := K')) := by
  intro y
  obtain ⟨L, b, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective (p := 2) (U := ⊤) y
  exact muToH2_h2ToMu_ofLevel L b

/-- **The two colimits are equivalent.** -/
noncomputable def muColimEquiv :
    NK.HassePrinciple.MuColim (K := K) (K' := K') 2 ⊤ ≃
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 ⊤ where
  toFun := muToH2
  invFun := h2ToMu
  left_inv := muToH2_left_inv
  right_inv := muToH2_right_inv

end Setup

/-- **The `μ_2`-colimit and the trivial-coefficient profinite cohomology `H²(·, Z/2)` agree.**

Over any field `K` of characteristic `0` with separable closure `K'`, the `μ_2`-colimit
`NK.HassePrinciple.MuColim 2 ⊤ = colim_L H²(Gal(L/K), μ_2(L))` and the profinite cohomology
`NK.BrauerHasse.H2Profinite 2 ⊤ = colim_L H²(Gal(L/K), Z/2)` are equivalent as types: at `p = 2`
the cyclotomic module `μ_2 = {±1}` is the trivial `Z/2`-module, and the levelwise identification
`μ_2(L) ≃+ Z/2` (natural in the levels, `muTwoAddEquiv_muLevelInclLinearMap`) induces an
isomorphism of the two filtered systems, hence of their colimits. -/
theorem muColimEquiv_h2Profinite (K : Type) [Field K] [CharZero K] (K' : Type) [Field K']
    [Algebra K K'] [IsSepClosure K K'] :
    Nonempty (NK.HassePrinciple.MuColim (K := K) (K' := K') 2 ⊤ ≃
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 ⊤) :=
  ⟨muColimEquiv (K := K) (K' := K')⟩

end NK.NUV2.LC
