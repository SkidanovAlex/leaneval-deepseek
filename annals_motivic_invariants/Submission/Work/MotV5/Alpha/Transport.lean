import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.AsTwCoordAt
import Submission.Work.MotV5.LamAS.root_eq_asRoot_add
import Submission.Work.MotV5.Alpha.CoeffAct
import Submission.Work.MotV5.Alpha.TwistTransport
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Transport of the AS twist data along the coefficient action

Given `Φ : Om D ≃ₐ[𝕜] Om D` (the coefficient action of an `𝕜`-automorphism `σ` of `Kb 𝕜` extending
`β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜`) and twisting data `(f, τ, σS, σ₁)`, the transported data
`(β f, Φ τ Φ⁻¹, σS, σ σ₁ σ⁻¹)` is again admissible (`ASTwistData`), and `Φ` carries the twist
field of the first datum onto the twist field of the second.  This is the field-theoretic core of
the `α`-reduction of the LAM node.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotV5.Alpha

open IntermediateField

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 The transported twisted action -/

/-- The twisted action commutes with the coefficient action, in the sense that
`A' = Φ A Φ⁻¹`, where `A'` is the twisted action of the transported data. -/
theorem asTwistAction_transport (D : Work.MotV.KleinData 𝕜)
    (τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (τ' : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hτ' : ∀ x : Work.MotV.Om D, τ' x = Φ (τ₂ (Φ.symm x)))
    (hσS : ∀ y : Work.MotV.Om D, Φ (σS y) = σS (Φ y)) (x : Work.MotV.Om D) :
    Work.MotV5.asTwistAction D τ' σS x
      = Φ (Work.MotV5.asTwistAction D τ₂ σS (Φ.symm x)) := by
  show σS (τ' x) = Φ (σS (τ₂ (Φ.symm x)))
  rw [hτ', hσS]

/-! ## §2 Transport of the twist field -/

/-- **The twist field is transported by the coefficient action.** -/
theorem asTwistFieldTrue_transport_iff (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₂ : RatFunc 𝕜)
    (τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS)
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV5.asRatio D i) = Work.MotV5.asRatio D i)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (τ' : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (hτ' : ∀ x : Work.MotV.Om D, τ' x = Φ (τ₂ (Φ.symm x))) (x : Work.MotV.Om D) :
    Φ x ∈ Work.MotV5.asTwistFieldTrue D (β f₂) τ' σS ↔
      x ∈ Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS := by
  have hcomm := coeffAut_comm_shiftOf D hD σS hσS Φ σ hΦc hΦratio
  rw [Work.MotV5.asTwistFieldTrue, Work.MotV5.asTwistFieldTrue, IntermediateField.mem_inf,
    IntermediateField.mem_inf]
  refine and_congr ?_ (coeffAut_asFieldL_iff D β σ hσβ Φ hΦc hΦratio f₂ x)
  refine (coeffAut_fixedField_iff D Φ (Work.MotV5.asTwistAction D τ₂ σS)
    (Work.MotV5.asTwistAction D τ' σS) (fun y => ?_) x)
  exact asTwistAction_transport D τ₂ σS τ' Φ hτ' hcomm y

/-! ## §3 The Artin–Schreier generator of the transported data -/

/-- A `𝕜`-algebra automorphism of `Kb 𝕜` fixes the image of `ℤ`. -/
theorem kb_intCast (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜) (n : ℤ) :
    σ (algebraMap ℤ (Work.MotV.Kb 𝕜) n) = algebraMap ℤ (Work.MotV.Kb 𝕜) n := by
  rw [IsScalarTower.algebraMap_apply ℤ 𝕜 (Work.MotV.Kb 𝕜) n,
    AlgEquiv.commutes σ (algebraMap ℤ 𝕜 n),
    ← IsScalarTower.algebraMap_apply ℤ 𝕜 (Work.MotV.Kb 𝕜) n]

/-- A `RatFunc 𝕜`-algebra automorphism of `Kb 𝕜` fixes the image of `ℤ`. -/
theorem kb_intCast' (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) (n : ℤ) :
    σ (algebraMap ℤ (Work.MotV.Kb 𝕜) n) = algebraMap ℤ (Work.MotV.Kb 𝕜) n := by
  rw [IsScalarTower.algebraMap_apply ℤ (RatFunc 𝕜) (Work.MotV.Kb 𝕜) n,
    AlgEquiv.commutes σ (algebraMap ℤ (RatFunc 𝕜) n),
    ← IsScalarTower.algebraMap_apply ℤ (RatFunc 𝕜) (Work.MotV.Kb 𝕜) n]

/-- **The transported `𝕜`-automorphism of `Kb` is `K`-linear.** -/
theorem transport_sigma_linear (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c)) (c : RatFunc 𝕜) :
    σ (σ₂ (σ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)))
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c := by
  have hsymm : σ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β.symm c) := by
    have h := hσβ (β.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq σ).mpr h.symm
  rw [hsymm, AlgEquiv.commutes σ₂ (β.symm c), hσβ (β.symm c),
    AlgEquiv.apply_symm_apply β]

/-- **The transported Artin–Schreier generator.**  If `σ₂ (asRoot f) = asRoot f + 1` and `σ` extends
`β` then `σ σ₂ σ⁻¹ (asRoot (β f)) = asRoot (β f) + 1`. -/
theorem transport_sigma_asRoot (f : RatFunc 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (hσ₂ : σ₂ (Work.MotV5.asRoot f) = Work.MotV5.asRoot f + 1) :
    σ (σ₂ (σ.symm (Work.MotV5.asRoot (β f)))) = Work.MotV5.asRoot (β f) + 1 := by
  -- `u := σ⁻¹ (asRoot (β f))` is a root of `X⁵ - X - f`, hence `u = asRoot f + k`
  have hu : (σ.symm (Work.MotV5.asRoot (β f))) ^ 5 - σ.symm (Work.MotV5.asRoot (β f))
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) f := by
    have h := congrArg σ.symm (Work.MotV5.asRoot_spec (β f))
    rw [map_sub, map_pow] at h
    have hc : σ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β f))
        = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) f := by
      have h2 : σ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β f))
          = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β.symm (β f)) := by
        have h3 := hσβ (β.symm (β f))
        rw [AlgEquiv.apply_symm_apply] at h3
        exact (AlgEquiv.symm_apply_eq σ).mpr h3.symm
      rwa [AlgEquiv.symm_apply_apply] at h2
    rwa [hc] at h
  obtain ⟨k, hk⟩ := Work.MotV5.LamAS.root_eq_asRoot_add f hu
  -- hence `σ (asRoot f) + k = asRoot (β f)`
  have hkey : σ (Work.MotV5.asRoot f) + algebraMap ℤ (Work.MotV.Kb 𝕜) ((k : Fin 5) : ℤ)
      = Work.MotV5.asRoot (β f) := by
    have h := congrArg σ hk
    rw [map_add, kb_intCast σ] at h
    rw [← h, AlgEquiv.apply_symm_apply]
  -- and consequently the transported generator acts as required
  have hstep : σ (σ₂ (σ.symm (Work.MotV5.asRoot (β f))))
      = σ (Work.MotV5.asRoot f) + 1 + algebraMap ℤ (Work.MotV.Kb 𝕜) ((k : Fin 5) : ℤ) := by
    rw [hk, map_add, hσ₂, kb_intCast' σ₂]
    simp only [map_add, map_one]
    rw [kb_intCast σ]
  rw [hstep]
  linear_combination (norm := first | refl_ring1 | ring1) hkey

end Work.MotV5.Alpha
