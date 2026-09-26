import Mathlib
import Submission.Work.Drive.jetDefs

/-!
# Lifting scalar surjectivity to `Space`-valued coefficients (`Fin 5` version)

`Fin 5`-instance of `Work.Drive.space_surjective_of_scalar`
(`Submission/Work/Drive/space_surjective_of_scalar.lean`): if the scalar evaluation map
`d ↦ (∑ j, ℓ i j * d j)_i` is onto, then so is the `Space`-valued map
`c ↦ (∑ j, ℓ i j • c j)_i`, by solving each coordinate direction of `Space` separately
(`spaceCoord` / `spaceOfFun`, `Submission/Work/Drive/jetDefs.lean`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **Scalar surjectivity lifts to `Space`-valued coefficients.** -/
theorem space_five_surjective_of_scalar {ℓ : Fin 5 → Fin 9 → ℝ}
    (h : ∀ A : Fin 5 → ℝ, ∃ d : Fin 9 → ℝ, ∀ i : Fin 5, ∑ j : Fin 9, ℓ i j * d j = A i) :
    ∀ A : Fin 5 → Space, ∃ c : Fin 9 → Space, ∀ i : Fin 5, ∑ j : Fin 9, (ℓ i j) • c j = A i := by
  intro A
  choose d hd using h
  refine ⟨fun j => spaceOfFun (fun k => d (fun i => (A i).ofLp k) j), fun i => ?_⟩
  refine WithLp.ofLp_injective 2 (funext fun k => ?_)
  have hcoord : spaceCoord k (∑ j : Fin 9, (ℓ i j) • spaceOfFun (fun k => d (fun i => (A i).ofLp k) j))
      = spaceCoord k (A i) := by
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, spaceCoord_spaceOfFun, spaceCoord_apply]
    exact hd (fun i => spaceCoord k (A i)) i
  have h2 : spaceCoord k (∑ j : Fin 9, (ℓ i j) • spaceOfFun (fun k => d (fun i => (A i).ofLp k) j))
      = (∑ j : Fin 9, (ℓ i j) • spaceOfFun (fun k => d (fun i => (A i).ofLp k) j)).ofLp k := rfl
  rw [h2] at hcoord
  simpa only [spaceCoord_apply] using hcoord

end

end Work.Drive
