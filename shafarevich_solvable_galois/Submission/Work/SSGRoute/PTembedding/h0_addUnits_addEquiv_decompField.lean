import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PTembedding.KummerMuDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

set_option maxHeartbeats 800000

/-- `H⁰(D_A, Ωˣ) ≃+ (↥F)ˣ` for the decomposition field `F = Ω^{D_A}`. -/
theorem h0_addUnits_addEquiv_decompField
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nonempty (↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) ≃+
      Additive (Units ↥(Work.SSGRoute.mup.decompField k Ω A))) := by
  -- `F` is the decomposition field `Ω^{D_A}`; `H⁰(D_A, Ωˣ)` is the group of `D_A`-invariant
  -- units of `Ω`.
  let F : IntermediateField k Ω := IntermediateField.fixedField (SSGRoute.decomp k A)
  -- An invariant unit of `Ω` lies in the fixed field `F`.
  have hmem : ∀ (x : ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))),
      ((Additive.toMul x.1 : Units Ω) : Ω) ∈ F := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have h := x.2 ⟨g, hg⟩
    have h2 : (g : Ω ≃ₐ[k] Ω) • (Additive.toMul x.1 : Units Ω) = (Additive.toMul x.1 : Units Ω) :=
      congrArg Additive.toMul h
    exact congrArg (fun u : Units Ω => (u : Ω)) h2
  -- ... and it is nonzero, hence a unit of `F`.
  have hne : ∀ (x : ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))),
      (⟨((Additive.toMul x.1 : Units Ω) : Ω), hmem x⟩ : F) ≠ 0 := by
    intro x h
    exact (Additive.toMul x.1 : Units Ω).ne_zero (by simpa using congrArg Subtype.val h)
  -- Conversely, a unit of `F`, viewed in `Ω`, is invariant under `D_A`.
  have hinv : ∀ (y : Additive (Units F)),
      (Additive.ofMul (Units.map (algebraMap ↥F Ω).toMonoidHom (Additive.toMul y)))
        ∈ Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) := by
    intro y
    rw [Work.GroupCohomology.mem_invariants]
    intro g
    rw [show g • (Additive.ofMul ((Units.map (algebraMap ↥F Ω).toMonoidHom) (Additive.toMul y)) : Additive (Units Ω)) = Additive.ofMul ((g : Ω ≃ₐ[k] Ω) • ((Units.map (algebraMap ↥F Ω).toMonoidHom) (Additive.toMul y))) from rfl]
    rw [Additive.ofMul.injective.eq_iff]
    apply Units.ext
    rw [Units.coe_map]
    have hv : (↑g : Ω ≃ₐ[k] Ω) ((↑(Additive.toMul y) : ↥F) : Ω) = ((↑(Additive.toMul y) : ↥F) : Ω) := by
      have h2 : ((↑(Additive.toMul y) : ↥F) : Ω) ∈ IntermediateField.fixedField (SSGRoute.decomp k A) := by
        change ((↑(Additive.toMul y) : ↥F) : Ω) ∈ F
        exact ((Additive.toMul y : (↥F)ˣ) : ↥F).2
      exact (IntermediateField.mem_fixedField_iff (SSGRoute.decomp k A) _).mp h2 g g.2
    show (↑g : Ω ≃ₐ[k] Ω) • ((algebraMap ↥F Ω) (↑(Additive.toMul y) : ↥F)) = (algebraMap ↥F Ω) (↑(Additive.toMul y) : ↥F)
    rw [AlgEquiv.smul_def]
    exact hv
  -- The two maps.
  let toF : ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) → Additive (Units F) :=
    fun x => Additive.ofMul (Units.mk0 (⟨((Additive.toMul x.1 : Units Ω) : Ω), hmem x⟩ : F) (hne x))
  let toH : Additive (Units F) → ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) :=
    fun y => ⟨Additive.ofMul (Units.map (algebraMap ↥F Ω).toMonoidHom (Additive.toMul y)), hinv y⟩
  have hleft : Function.LeftInverse toH toF := by
    intro x
    apply Subtype.ext
    apply Additive.toMul.injective
    change (Units.map (algebraMap ↥F Ω).toMonoidHom (Units.mk0 (⟨((Additive.toMul x.1 : Units Ω) : Ω), hmem x⟩ : F) (hne x)) : Units Ω) = Additive.toMul x.1
    rw [Units.ext_iff, Units.coe_map, Units.val_mk0]
    rfl
  have hright : Function.RightInverse toH toF := by
    intro y
    have hU : Units.mk0 (⟨((Additive.toMul (toH y).1 : Units Ω) : Ω), hmem (toH y)⟩ : F) (hne (toH y)) = Additive.toMul y := by
      apply Units.ext
      rw [Units.val_mk0]
      apply Subtype.ext
      change ((↑(Additive.toMul (toH y).1) : Units Ω) : Ω) = (((Additive.toMul y : (↥F)ˣ) : ↥F) : Ω)
      rw [show (Additive.toMul (toH y).1 : Units Ω) = Units.map (algebraMap ↥F Ω).toMonoidHom (Additive.toMul y) from rfl]
      rw [Units.coe_map]
      rfl
    exact congrArg Additive.ofMul hU
  have hadd : ∀ x y, toF (x + y) = toF x + toF y := by
    intro x y
    have hU : Units.mk0 (⟨((Additive.toMul (x + y).1 : Units Ω) : Ω), hmem (x + y)⟩ : F) (hne (x + y))
        = Units.mk0 (⟨((Additive.toMul x.1 : Units Ω) : Ω), hmem x⟩ : F) (hne x)
          * Units.mk0 (⟨((Additive.toMul y.1 : Units Ω) : Ω), hmem y⟩ : F) (hne y) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
      apply Subtype.ext
      rfl
    exact congrArg Additive.ofMul hU
  exact ⟨AddEquiv.mk ⟨toF, toH, hleft, hright⟩ hadd⟩

end Work.SSGRoute.PTembedding
