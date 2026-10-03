import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.invFunOn_differentiableOn

namespace Work.Horn.HB

/-- **The basin coordinate of the petal is a homeomorphism onto its image.**

`Φ` is holomorphic on the parabolic basin (`ParabData.Φ_holo`), hence on the open connected petal
`Ωp` (`Ωp_open`, `Ωp_sub`), and injective there (`Φ_inj`); being nonconstant (its Abel equation
`Φ (f₀ z) = Φ z + 1` holds along `f₀ '' Ωp ⊆ Ωp`, so `Φ` takes distinct values at `z` and `f₀ z`),
its inverse function on the image is holomorphic — this is the local inverse-function theorem
applied at each point of `Ωp` (`Work.Repel.invFunOn_differentiableOn`).  In particular the inverse
of `Φ|Ωp` is continuous on `Φ '' Ωp`, which is the content of the requested statement. -/
theorem Psi_inverse {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ Ψ : ℂ → ℂ, (∀ w ∈ d.Φ '' d.Ωp, Ψ w ∈ d.Ωp ∧ d.Φ (Ψ w) = w) ∧
      ContinuousOn Ψ (d.Φ '' d.Ωp) := by
  refine ⟨Function.invFunOn d.Φ d.Ωp, fun w hw => ⟨?_, ?_⟩, ?_⟩
  · exact Function.invFunOn_mem hw
  · exact Function.invFunOn_eq hw
  · have hdiff : DifferentiableOn ℂ d.Φ d.Ωp := d.Φ_holo.mono d.Ωp_sub
    exact (Work.Repel.invFunOn_differentiableOn d.Ωp_open d.Φ_inj hdiff).continuousOn

end Work.Horn.HB
