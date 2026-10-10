import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotV5.LamAS.Setup
import Submission.Work.MotC.adjoin_genX_genY_eq_top
import Submission.Work.MotV5.LamAS.coeffOm_conj_shiftOf

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coefficient action of `Gal(L/K)` is the restriction of the coefficient action of `Gal(K̄/K)`

The base-change map `asIota : M = L(E) → Kb(E) = Om D` intertwines the coefficient action of
`γ ∈ Gal(L/K)` on `M` (`asCoeff`) with the coefficient action of any extension `γ̃ ∈ Gal(K̄/K)` of
`γ` to `K̄` (`asCoeffOm`): the two sides are `K`-algebra homomorphisms agreeing on the constants `L`
and on the coordinates `x, y`, which generate `M` over `L`
(`Work.MotC.adjoin_genX_genY_eq_top`).

Consequently `σS` commutes with the coefficient action on `M` as well, which is what makes the
twisted Galois action `ψ_γ = σS ^ (χ γ) ∘ γ̃` multiplicative.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace Work.MotV5.LamAS

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The coefficient action of `γ ∈ Gal(K̄/K)` on `Om D = K̄(E)`: the `K`-algebra automorphism
acting on the constants `K̄` by `γ` and fixing `x, y`. -/
noncomputable def asCoeffOm (D : Work.MotV.KleinData 𝕜)
    (γ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) :
    Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D :=
  Work.MotV5.coeffAction (R := 𝕜) (K := RatFunc 𝕜) (L := Work.MotV.Kb 𝕜) D.E γ

theorem asCoeffOm_algebraMap (D : Work.MotV.KleinData 𝕜)
    (γ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) (c : Work.MotV.Kb 𝕜) :
    asCoeffOm D γ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c) =
      algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (γ c) :=
  Work.MotV5.coeffAction_algebraMap (R := 𝕜) (K := RatFunc 𝕜) (L := Work.MotV.Kb 𝕜) D.E γ c

theorem asCoeffOm_genX (D : Work.MotV.KleinData 𝕜)
    (γ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) :
    asCoeffOm D γ (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) =
      Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
  Work.MotV5.coeffAction_genX (R := 𝕜) (K := RatFunc 𝕜) (L := Work.MotV.Kb 𝕜) D.E γ

theorem asCoeffOm_genY (D : Work.MotV.KleinData 𝕜)
    (γ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) :
    asCoeffOm D γ (Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜))) =
      Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
  Work.MotV5.coeffAction_genY (R := 𝕜) (K := RatFunc 𝕜) (L := Work.MotV.Kb 𝕜) D.E γ

/-- **The base-change map intertwines the two coefficient actions.**  If `γ̃ ∈ Gal(K̄/K)` extends
`γ ∈ Gal(L/K)`, then `asIota (asCoeff γ y) = asCoeffOm γ̃ (asIota y)` for all `y ∈ M`. -/
theorem asIota_asCoeff (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (γb : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hγb : ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      γb (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) l) =
        algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) (γ l))
    (y : asML D f₁ f₂) :
    asIota D f₁ f₂ (asCoeff D f₁ f₂ γ y) = asCoeffOm D γb (asIota D f₁ f₂ y) := by
  classical
  -- the equaliser, as an `↥L`-intermediate field of `M`
  let S : IntermediateField ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) :=
    { carrier := {z : asML D f₁ f₂ |
        asIota D f₁ f₂ (asCoeff D f₁ f₂ γ z) = asCoeffOm D γb (asIota D f₁ f₂ z)}
      mul_mem' := fun {a b} ha hb => by
        have ha' : asIota D f₁ f₂ (asCoeff D f₁ f₂ γ a) =
            asCoeffOm D γb (asIota D f₁ f₂ a) := ha
        have hb' : asIota D f₁ f₂ (asCoeff D f₁ f₂ γ b) =
            asCoeffOm D γb (asIota D f₁ f₂ b) := hb
        show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ (a * b)) =
          asCoeffOm D γb (asIota D f₁ f₂ (a * b))
        rw [map_mul, map_mul, map_mul, map_mul, ha', hb']
      one_mem' := by
        show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ 1) = asCoeffOm D γb (asIota D f₁ f₂ 1)
        simp
      add_mem' := fun {a b} ha hb => by
        have ha' : asIota D f₁ f₂ (asCoeff D f₁ f₂ γ a) =
            asCoeffOm D γb (asIota D f₁ f₂ a) := ha
        have hb' : asIota D f₁ f₂ (asCoeff D f₁ f₂ γ b) =
            asCoeffOm D γb (asIota D f₁ f₂ b) := hb
        show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ (a + b)) =
          asCoeffOm D γb (asIota D f₁ f₂ (a + b))
        rw [map_add, map_add, map_add, map_add, ha', hb']
      zero_mem' := by
        show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ 0) = asCoeffOm D γb (asIota D f₁ f₂ 0)
        simp
      inv_mem' := fun {a} ha => by
        have ha' : asIota D f₁ f₂ (asCoeff D f₁ f₂ γ a) =
            asCoeffOm D γb (asIota D f₁ f₂ a) := ha
        show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ a⁻¹) =
          asCoeffOm D γb (asIota D f₁ f₂ a⁻¹)
        rw [map_inv₀, map_inv₀, map_inv₀, map_inv₀, ha']
      algebraMap_mem' := fun l => by
        show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ
            (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)) =
          asCoeffOm D γb (asIota D f₁ f₂
            (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
        rw [asCoeff_algebraMap, asIota_algebraMap, asIota_algebraMap, asCoeffOm_algebraMap]
        exact (congrArg (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) (hγb l)).symm }
  have htop : (⊤ : IntermediateField ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)) ≤ S := by
    rw [← Work.MotC.adjoin_genX_genY_eq_top (asE2 D f₁ f₂)]
    rw [IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ (Work.MotV.genX (asE2 D f₁ f₂))) =
        asCoeffOm D γb (asIota D f₁ f₂ (Work.MotV.genX (asE2 D f₁ f₂)))
      rw [asCoeff_genX, asIota_genX, asCoeffOm_genX]
    · show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ (Work.MotV.genY (asE2 D f₁ f₂))) =
        asCoeffOm D γb (asIota D f₁ f₂ (Work.MotV.genY (asE2 D f₁ f₂)))
      rw [asCoeff_genY, asIota_genY, asCoeffOm_genY]
  exact htop trivial

end Work.MotV5.LamAS
