import Mathlib
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotV5.LamAS.linearDisjoint_of_isGalois_of_inf_bot
import Submission.Work.MotV5.LamAS.asF_transfer
import Submission.Work.MotV5.LamAS.asIota_range

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.MotV5.LamAS

/-- The range of the algebra map out of an intermediate field is its underlying subalgebra. -/
theorem range_toAlgHom_eq_toSubalgebra {K E : Type*} [Field K] [Field E] [Algebra K E]
    (S : IntermediateField K E) :
    (IsScalarTower.toAlgHom K ↥S E).range = S.toSubalgebra := by
  rw [show IsScalarTower.toAlgHom K ↥S E = S.val from rfl, IntermediateField.range_val]

/-- The twist field of a class `g ∈ {f₁, f₂}`, pulled back to `M = L(E)` along the base-change map `asIota`, is linearly disjoint from the constants `L` over `K = RatFunc 𝕜`. -/
theorem asF_linearDisjoint (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    [hGal : IsGalois (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
    [hFin : FiniteDimensional (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (hg : g = f₁ ∨ g = f₂) :
    (Work.MotV5.LamAS.asF D f₁ f₂ g τ σS).LinearDisjoint
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) := by
  -- The range of the base-change map `asIota` is `Ω = kleinField D ⊔ L`.
  have hRange : (asIota D f₁ f₂).fieldRange =
      Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂) :=
    asIota_range 𝕜 D hD f₁ f₂
  -- The twist field meets the constants `L` in `K` (and generates `M` together with them).
  obtain ⟨-, -, hinf⟩ := asF_transfer 𝕜 D hD f₁ f₂ g τ σS σ h hg hRange
  -- `L` embeds into `M` with image `asLImageM`, so `hGal`/`hFin` transfer to the image.
  haveI hGalL : IsGalois (RatFunc 𝕜) ↥(asLImageM D f₁ f₂) :=
    IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom (RatFunc 𝕜)
      ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)))
  haveI hFinL : FiniteDimensional (RatFunc 𝕜) ↥(asLImageM D f₁ f₂) :=
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom (RatFunc 𝕜)
      ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂))).toLinearEquiv.finiteDimensional
  -- The Galois criterion, applied with `A = L` (finite Galois) and `B = asF`.
  have hLI : (asLImageM D f₁ f₂).LinearDisjoint ↥(asF D f₁ f₂ g τ σS) :=
    linearDisjoint_of_isGalois_of_inf_bot (A := asLImageM D f₁ f₂)
      (B := asF D f₁ f₂ g τ σS) (by rw [inf_comm]; exact hinf)
  -- Rewrite both sides as subalgebra linear disjointness; the image of `L` is `asLImageM`.
  rw [IntermediateField.linearDisjoint_iff]
  rw [show (IsScalarTower.toAlgHom (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      (asML D f₁ f₂)).range = (asLImageM D f₁ f₂).toSubalgebra from rfl]
  rw [IntermediateField.linearDisjoint_iff] at hLI
  rw [range_toAlgHom_eq_toSubalgebra] at hLI
  exact Subalgebra.LinearDisjoint.symm hLI

end Work.MotV5.LamAS
