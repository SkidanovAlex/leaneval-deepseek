import Mathlib
import Submission.Work.MotV5.LamAS.asML
import Submission.Work.MotV5.LamAS.algClosure_algHom_surjective

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.MotV5.LamAS

/-- Every `K`-algebra automorphism of the two-root Artin–Schreier field `L = K⟮asRoot f₁, asRoot f₂⟯` extends to a `K`-algebra automorphism of the algebraic closure `Kb 𝕜` (by the standard extension of embeddings of algebraic extensions into an algebraically closed field). -/
theorem asExtension (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)) :
    ∃ γb : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜,
      ∀ l : ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂),
        γb (l : Work.MotV.Kb 𝕜) = (γ l : Work.MotV.Kb 𝕜) := by
  -- `L = K⟮asRoot f₁, asRoot f₂⟯` is the intermediate field to be embedded.
  let L := ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
  -- The `K`-embedding `L → Kb 𝕜` induced by `γ`.
  let f : L →ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜 :=
    (IsScalarTower.toAlgHom (RatFunc 𝕜) L (Work.MotV.Kb 𝕜)).comp γ.toAlgHom
  -- `Kb 𝕜` is algebraic over `L` (it is algebraic over `RatFunc 𝕜`) and algebraically closed
  -- and `K`-algebraically closed, so the embedding `f` extends to `Kb 𝕜 →ₐ[K] Kb 𝕜`.
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := RatFunc 𝕜)
    (L := L) (E := Work.MotV.Kb 𝕜) (M := Work.MotV.Kb 𝕜) f
  have hφ' : ∀ l : L, φ (l : Work.MotV.Kb 𝕜) = (γ l : Work.MotV.Kb 𝕜) := by
    intro l
    have h := DFunLike.congr_fun hφ l
    have e1 : (AlgHom.domRestrict L φ) l = φ (l : Work.MotV.Kb 𝕜) := rfl
    have e2 : f l = (γ l : Work.MotV.Kb 𝕜) := rfl
    rw [e1, e2] at h
    exact h
  -- An injective `𝕜`-algebra endomorphism of `Kb 𝕜 = \overline{𝕜(t)}` is surjective.
  have hinj : Function.Injective φ := RingHom.injective (φ : Work.MotV.Kb 𝕜 →+* Work.MotV.Kb 𝕜)
  have hsurj : Function.Surjective φ :=
    algClosure_algHom_surjective (K := 𝕜) (φ.restrictScalars 𝕜) (fun a b h => hinj h)
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩, hφ'⟩

end Work.MotV5.LamAS
