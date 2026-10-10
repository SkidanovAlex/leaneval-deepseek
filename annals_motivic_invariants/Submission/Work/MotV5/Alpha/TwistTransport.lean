import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.AsTwCoordAt
import Submission.Work.MotV5.Alpha.CoeffAct

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Transport of the AS twist fields along the coefficient action

Continuing `Submission.Work.MotV5.Alpha.CoeffAct`: the coefficient action `Φ` of an `𝕜`-algebra
automorphism `σ` of `Kb = Kb 𝕜` (acting on `Om D` on the constants by `σ`, fixing the Klein
coordinates `κᵢ`) commutes with the projective fifth-torsion shift `σS` (`KleinData.ShiftOf`),
and consequently transports the twisted-action fixed fields and the twist fields
`asTwistFieldTrue`.

The commutativity is the only place where `KleinData.Generates` is used: `Φ σS Φ⁻¹` and `σS` are
both `Kb`-linear and agree on the Klein ratios, which generate `Om D` over `Kb`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MotV5.Alpha

open IntermediateField

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 Fixed fields of cyclic groups -/

/-- The fixed field of `⟨A⟩` is the set of points fixed by `A` itself. -/
theorem mem_fixedField_zpowers_iff (D : Work.MotV.KleinData 𝕜)
    (A : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D) (x : Work.MotV.Om D) :
    x ∈ IntermediateField.fixedField (Subgroup.zpowers A) ↔ A x = x := by
  constructor
  · intro h
    exact (IntermediateField.mem_fixedField_iff _ x).mp h A (Subgroup.mem_zpowers A)
  · intro h
    refine (IntermediateField.mem_fixedField_iff _ x).mpr ?_
    intro f hf
    have hstab : Subgroup.zpowers A ≤
        MulAction.stabilizer (Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D) x :=
      Subgroup.zpowers_le.mpr ((MulAction.mem_stabilizer_iff).mpr h)
    exact (MulAction.mem_stabilizer_iff).mp (hstab hf)

/-- **Conjugation of a twisted-action fixed field.**  If `A' = Φ A Φ⁻¹` then `Φ` carries the fixed
field of `⟨A⟩` onto the fixed field of `⟨A'⟩`. -/
theorem coeffAut_fixedField_iff (D : Work.MotV.KleinData 𝕜)
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (A A' : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (hA' : ∀ y : Work.MotV.Om D, A' y = Φ (A (Φ.symm y))) (x : Work.MotV.Om D) :
    Φ x ∈ IntermediateField.fixedField (Subgroup.zpowers A') ↔
      x ∈ IntermediateField.fixedField (Subgroup.zpowers A) := by
  rw [mem_fixedField_zpowers_iff D A' (Φ x), mem_fixedField_zpowers_iff D A x, hA',
    AlgEquiv.symm_apply_apply, Φ.injective.eq_iff]

/-! ## §2 The coefficient action commutes with the fifth-torsion shift -/

/-- `σS` acts on the Klein ratios by shifting the index and dividing by the first ratio. -/
theorem shiftOf_asRatio (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS) (i : Fin 5) :
    σS (Work.MotV5.asRatio D i) = Work.MotV5.asRatio D (i + 1) / Work.MotV5.asRatio D 1 := by
  obtain ⟨lam, hlam, hshift⟩ := hσS
  have hκ0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.1.coord0_ne (Work.MotV.Kb 𝕜)
  have h1 : ((0 : Fin 5) + 1) = 1 := rfl
  simp only [Work.MotV5.asRatio, map_div₀, hshift i, hshift 0, h1]
  rw [mul_div_mul_left _ _ hlam]
  field_simp

/-- Two `Kb`-algebra automorphisms of `Om D` agreeing on the Klein ratios are equal. -/
theorem algEquiv_eq_of_ratio_eq (D : Work.MotV.KleinData 𝕜)
    (hgen : IntermediateField.adjoin (Work.MotV.Kb 𝕜)
      (Set.range (Work.MotV5.asRatio D)) = ⊤)
    (f g : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (h : ∀ i : Fin 5, f (Work.MotV5.asRatio D i) = g (Work.MotV5.asRatio D i)) : f = g := by
  have hE : (⊤ : IntermediateField (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) ≤
      { carrier := {x | f x = g x}
        zero_mem' := by simp
        one_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_add, map_add, ha, hb]
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, map_mul, ha, hb]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [map_inv₀, map_inv₀, ha]
        algebraMap_mem' := fun c => by
          show f (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
            = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
          rw [AlgEquiv.commutes f c, AlgEquiv.commutes g c] } := by
    rw [← hgen, IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact h i
  ext x
  exact hE IntermediateField.mem_top

/-- **The coefficient action commutes with the fifth-torsion shift.**  `Φ σS Φ⁻¹ = σS`: both are
`Kb`-linear and act in the same way on the Klein ratios, which generate `Om D` over `Kb`. -/
theorem coeffAut_conj_shiftOf (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS)
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV5.asRatio D i) = Work.MotV5.asRatio D i) :
    ∀ z : Work.MotV.Om D, Φ (σS (Φ.symm z)) = σS z := by
  have hgen : IntermediateField.adjoin (Work.MotV.Kb 𝕜)
      (Set.range (Work.MotV5.asRatio D)) = ⊤ := hD.2.2.1 (Work.MotV.Kb 𝕜)
  let Ψ₀ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D := Φ * (σS.restrictScalars 𝕜) * Φ.symm
  have hΨ₀ : ∀ c : Work.MotV.Kb 𝕜,
      Ψ₀ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c := by
    intro c
    have hsymm : Φ.symm (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ.symm c) := by
      have h := hΦc (σ.symm c)
      rw [AlgEquiv.apply_symm_apply] at h
      exact (AlgEquiv.symm_apply_eq Φ).mpr h.symm
    have hstep : Ψ₀ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = Φ (σS (Φ.symm (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c))) := by
      simp only [Ψ₀, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
    rw [hstep, hsymm, AlgEquiv.commutes σS (σ.symm c), hΦc (σ.symm c),
      AlgEquiv.apply_symm_apply σ]
  let Ψ : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D :=
    AlgEquiv.ofRingEquiv (f := Ψ₀.toRingEquiv) hΨ₀
  have hΨeq : Ψ = σS := by
    refine algEquiv_eq_of_ratio_eq D hgen Ψ σS fun i => ?_
    have hsymmi : Φ.symm (Work.MotV5.asRatio D i) = Work.MotV5.asRatio D i :=
      (AlgEquiv.symm_apply_eq Φ).mpr (hΦratio i).symm
    have hstep : Ψ (Work.MotV5.asRatio D i) = Φ (σS (Φ.symm (Work.MotV5.asRatio D i))) := by
      show Ψ₀ (Work.MotV5.asRatio D i) = Φ (σS (Φ.symm (Work.MotV5.asRatio D i)))
      simp only [Ψ₀, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
    rw [hstep, hsymmi, shiftOf_asRatio D hD σS hσS i, map_div₀, hΦratio (i + 1), hΦratio 1]
  intro z
  have h := congrFun (congrArg (fun e : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D =>
    (e : Work.MotV.Om D → Work.MotV.Om D)) hΨeq) z
  have h2 : Ψ₀ z = σS z := by
    rwa [show (Ψ : Work.MotV.Om D → Work.MotV.Om D) = ⇑Ψ₀ from rfl] at h
  simpa only [Ψ₀, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using h2

/-- **The coefficient action commutes with the fifth-torsion shift** (pointwise form). -/
theorem coeffAut_comm_shiftOf (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS)
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV5.asRatio D i) = Work.MotV5.asRatio D i)
    (y : Work.MotV.Om D) : Φ (σS y) = σS (Φ y) := by
  have h := coeffAut_conj_shiftOf D hD σS hσS Φ σ hΦc hΦratio (Φ y)
  rwa [AlgEquiv.symm_apply_apply] at h

end Work.MotV5.Alpha
