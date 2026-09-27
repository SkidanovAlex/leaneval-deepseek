import Mathlib
import Submission.Work.Drive.BoxParityDefs

namespace Work.Drive

open Set

/-- **Uniqueness of integral curves** for a time-independent Lipschitz vector field on
`Amb m = ℝ^{m+1}`: two global solutions of `γ' = w ∘ γ` that agree at one time are equal
everywhere.

This is the standard uniqueness theorem for ODEs with a Lipschitz right-hand side
(`ODE_solution_unique_univ`), applied to the time-independent field `v t = w` with the
Lipschitz constant `L` valid on all of `Amb m`. -/
theorem integralCurve_unique {m : ℕ} {w : Work.Drive.Amb m → Work.Drive.Amb m} {L : NNReal}
    (hw : LipschitzWith L w) {γ γ' : ℝ → Work.Drive.Amb m}
    (hγ : ∀ t, HasDerivAt γ (w (γ t)) t) (hγ' : ∀ t, HasDerivAt γ' (w (γ' t)) t) {t₀ : ℝ}
    (h : γ t₀ = γ' t₀) : γ = γ' :=
  ODE_solution_unique_univ (v := fun _ : ℝ => w) (s := fun _ : ℝ => Set.univ) (K := L)
    (fun _ => hw.lipschitzOnWith) (fun t => ⟨hγ t, trivial⟩) (fun t => ⟨hγ' t, trivial⟩) h

end Work.Drive
