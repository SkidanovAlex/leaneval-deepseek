import Mathlib
import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.NUV2.LC.unitsLevelH2_addOrderOf_realization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open NK.HassePrinciple

namespace NK.NUV2.LC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The level dictionary, at the level of representations

The level group `LevelGroup V L = V ⧸ (V ⊓ Gal(K'/L))` is the Galois group of the finite extension
`L/(L ⊓ K'^V)`, and the two descriptions (restriction to `L` of an element of `V`, versus an
`(L ⊓ K'^V)`-automorphism of `L`) identify the unit representations.  This gives the additive
identification `UnitsLevelH2 V L ≃+ H²(Gal(L/(L ⊓ K'^V)), Lˣ)` with integral coefficients. -/

/-- Computation rule for `IntermediateField.fixingSubgroupEquiv`. -/
lemma fixingSubgroupEquiv_apply_coe {F' : Type} [Field F'] {E : Type} [Field E] [Algebra F' E]
    (K₀ : IntermediateField F' E) (σ : ↥K₀.fixingSubgroup) (x : E) :
    (IntermediateField.fixingSubgroupEquiv K₀ σ) x = (σ : Gal(E/F')) x := rfl

/-- Computation rule for `levelGroupMulEquivLevelGalois`: on the class of an element of `V`, it is
the restriction of that element to `L`. -/
theorem levelGroupMulEquivLevelGalois_apply_coe (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (g : NK.BrauerHasse.LevelGroup V L) (x : ↥L) :
    (NK.HassePrinciple.levelGroupMulEquivLevelGalois V L g) x
      = (NK.HassePrinciple.levelGroupRestrictHom V L g) x := by
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (L.fixingSubgroup.subgroupOf V) g
  rw [← hv, QuotientGroup.mk'_apply, NK.HassePrinciple.levelGroupMulEquivLevelGalois]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivRange, MulEquiv.ofBijective_apply,
    QuotientGroup.rangeKerLift, MonoidHom.rangeRestrict, QuotientGroup.lift_mk]
  rw [fixingSubgroupEquiv_apply_coe]
  simp only [MulEquiv.subgroupCongr_symm_apply]
  rfl

/-- **The level cohomology with unit coefficients is the cohomology of the Galois group of the
level extension.**  The two representations of `LevelGroup V L` on `Lˣ` — the restriction action
along `levelGroupRestrictHom V L`, and the action through the identification of the level group with
`Gal(L/(L ⊓ K'^V))` — have the same `CoeffInt`-linear underlying action. -/
theorem nonempty_addEquiv_unitsLevelH2_level {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    Nonempty (NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits
        (↥(IntermediateField.fixedField (Subgroup.map (NK.HassePrinciple.levelRestrict L) V)))
        (↥L)) 2) := by
  classical
  let F : IntermediateField K ↥L :=
    IntermediateField.fixedField (V.map (NK.HassePrinciple.levelRestrict L))
  let e : NK.BrauerHasse.LevelGroup V L ≃* (↥L ≃ₐ[↥F] ↥L) :=
    NK.HassePrinciple.levelGroupMulEquivLevelGalois V L
  have hrep : Rep.res (NK.HassePrinciple.levelGroupRestrictHom V L)
        (Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt (↥L ≃ₐ[K] ↥L) (Additive (↥L)ˣ))
      = Rep.res e.toMonoidHom (Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt
          (↥L ≃ₐ[↥F] ↥L) (Additive (↥L)ˣ)) := by
    have hρ : ((Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt
          (↥L ≃ₐ[K] ↥L) (Additive (↥L)ˣ)).ρ.comp
          (NK.HassePrinciple.levelGroupRestrictHom V L))
        = ((Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt (↥L ≃ₐ[↥F] ↥L)
              (Additive (↥L)ˣ)).ρ.comp e.toMonoidHom) := by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro u
      show Additive.ofMul ((NK.HassePrinciple.levelGroupRestrictHom V L g) • (Additive.toMul u : (↥L)ˣ))
        = Additive.ofMul ((e g) • (Additive.toMul u : (↥L)ˣ))
      congr 1
      rw [AlgEquiv.smul_units_def, AlgEquiv.smul_units_def]
      congr 1
      ext x
      simpa using (levelGroupMulEquivLevelGalois_apply_coe V L g x).symm
    exact congrArg (fun r => Rep.of (k := NK.HassePrinciple.CoeffInt)
      (G := NK.BrauerHasse.LevelGroup V L) (X := Additive (↥L)ˣ) r) hρ
  obtain ⟨φ₁⟩ := nonempty_addEquiv_groupCohomology_res_mulEquiv
    (A := Rep.ofDistribMulAction NK.HassePrinciple.CoeffInt (↥L ≃ₐ[↥F] ↥L)
      (Additive (↥L)ˣ)) e 2
  obtain ⟨φ₂⟩ := nonempty_addEquiv_groupCohomology_two_coeffTransfer
    (k := NK.HassePrinciple.CoeffInt) (k' := ℤ) (G := ↥L ≃ₐ[↥F] ↥L)
    (V := Additive (↥L)ˣ)
  exact ⟨(hrep.symm ▸ φ₁).trans φ₂⟩

end NK.NUV2.LC
