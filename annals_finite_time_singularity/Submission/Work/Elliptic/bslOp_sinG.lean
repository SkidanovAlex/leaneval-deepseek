import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Algebra
import Submission.Work.Elliptic.bslOp_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- `L(Ψ + G sin 2θ) = L(Ψ) - (α²z²G'' + α(5+α)zG') sin 2θ` at every `(z,θ)` with
`cos θ ≠ 0`: the `sin 2θ`-direction of `L` is purely radial, so adding a multiple of
`sin 2θ` shifts `LΨ` by the one-dimensional operator
`α²z² d²/dz² + α(5+α)z d/dz` applied to `G`, times `sin 2θ`.  Together with
`Lzero_sin_two` this is the identity behind §'The singular term' of the paper. -/
lemma bslOp_sinG (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (G : ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ)) (hG : ContDiffAt ℝ 2 G z)
    (hθ : Real.cos θ ≠ 0) :
    bslOp α (fun z θ => Ψ z θ + G z * Real.sin (2 * θ)) z θ
      = bslOp α Ψ z θ
        - (α ^ 2 * z ^ 2 * deriv (fun z' => deriv G z') z + α * (5 + α) * z * deriv G z)
            * Real.sin (2 * θ) := by
  -- the `sin 2θ`-part `(z,θ) ↦ G z · sin 2θ` is `C²` at `(z,θ)`
  have hΦ : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => G z * Real.sin (2 * θ))) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => G p.1) (z, θ) :=
      hG.comp (z, θ) contDiffAt_fst
    have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by fun_prop
    have hfun : Function.uncurry (fun z θ => G z * Real.sin (2 * θ))
        = fun p : ℝ × ℝ => G p.1 * Real.sin (2 * p.2) := rfl
    rw [hfun]
    exact h1.mul h2
  -- additivity of `L`, then the closed form of `L` on the `sin 2θ` direction
  rw [bslOp_add α Ψ (fun z θ => G z * Real.sin (2 * θ)) z θ hθ hΨ hΦ,
      bslOp_sin_two_mul α G z θ hθ]
  ring

end Work.Elliptic
