import Mathlib
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotV5.LamAS.asTransport
import Submission.Work.MotV5.LamAS.asExtension

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.LamAS

open WeierstrassCurve WeierstrassCurve.Affine

/-- The coefficient action of `σ ∈ Gal(K̄/K)` on `Om D` fixes every Klein coordinate `κ_i` (they
are `𝕜`-rational expressions in `x, y`).  Local copy of
`Work.MotV5.LamAS.coeffAction_fixes_kleinCoord` (whose file is not imported here). -/
private theorem coeffAction_fixes_kleinCoord' {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) (i : Fin 5) :
    Work.MotV5.coeffAction D.E σ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i := by
  simp only [Work.MotV.kleinCoord_eq_sum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · rw [← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (D.coord i m),
      IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) (D.coord i m)]
    exact (Work.MotV5.coeffAction D.E σ).commutes _
  · exact Work.MotV5.coeffAction_kleinBas D σ m

/-- The lift `σS'` of the fifth-torsion shift to `M = L(E)` commutes with the coefficient action of `Gal(L/K)` on `M`. -/
theorem asSigmaLift_comm (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : RatFunc 𝕜)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS)
    (σS' : Work.MotV5.LamAS.asML D f₁ f₂ ≃ₐ[↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
      Work.MotV5.LamAS.asML D f₁ f₂)
    (hσS' : ∀ x : Work.MotV5.LamAS.asML D f₁ f₂,
      Work.MotV5.LamAS.asIota D f₁ f₂ (σS' x) =
        σS (Work.MotV5.LamAS.asIota D f₁ f₂ x))
    (γ : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
    (x : Work.MotV5.LamAS.asML D f₁ f₂) :
    σS' (Work.MotV5.LamAS.asCoeff D f₁ f₂ γ x) =
      Work.MotV5.LamAS.asCoeff D f₁ f₂ γ (σS' x) := by
  -- Extend `γ ∈ Gal(L/K)` to `γb ∈ Gal(K̄/K)`, and transport the statement to `Ω = K̄(E)` via
  -- the (injective) base-change map `asIota`.
  obtain ⟨γb, hγb⟩ := asExtension 𝕜 f₁ f₂ γ
  have hγb' : ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      γb (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) l) =
        algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) (γ l) := by
    intro l; simpa using hγb l
  -- On `Ω` the coefficient action of `γb` commutes with the fifth-torsion shift `σS`
  -- (`coeffOm_conj_shiftOf`, whose geometric input is `ShiftOf`).
  have hcomm : ∀ z : Work.MotV.Om D,
      asCoeffOm D γb (σS z) = σS (asCoeffOm D γb z) := by
    have h := coeffOm_conj_shiftOf 𝕜 D hD ((asCoeffOm D γb).restrictScalars 𝕜)
      (fun i => coeffAction_fixes_kleinCoord' D γb i)
      (fun c => ⟨γb c, asCoeffOm_algebraMap D γb c⟩) σS hσS
    intro z
    have hz := h (((asCoeffOm D γb).restrictScalars 𝕜) z)
    rw [show ((asCoeffOm D γb).restrictScalars 𝕜)⁻¹
        (((asCoeffOm D γb).restrictScalars 𝕜) z) = z from
      AlgEquiv.symm_apply_apply _ z] at hz
    exact hz
  -- Both sides have the same image under `asIota`.
  have h1 : asIota D f₁ f₂ (σS' (asCoeff D f₁ f₂ γ x)) =
      σS (asCoeffOm D γb (asIota D f₁ f₂ x)) := by
    rw [hσS' (asCoeff D f₁ f₂ γ x), asIota_asCoeff D f₁ f₂ γ γb hγb' x]
  have h2 : asIota D f₁ f₂ (asCoeff D f₁ f₂ γ (σS' x)) =
      asCoeffOm D γb (σS (asIota D f₁ f₂ x)) := by
    rw [asIota_asCoeff D f₁ f₂ γ γb hγb' (σS' x), hσS' x]
  apply asIota_injective D f₁ f₂
  rw [h1, h2, hcomm]

end Work.MotV5.LamAS
