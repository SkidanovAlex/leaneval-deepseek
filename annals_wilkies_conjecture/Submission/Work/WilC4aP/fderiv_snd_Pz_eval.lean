import Mathlib
import Submission.Work.WilC4aP.Basic

namespace Work.WilC4aP

/-- The right-hand partial derivative of `(z, w) ↦ (Pz P z).eval w` at `(z₀, α)` is the
multiplication map by `(Pz P z₀).derivative.eval α`.

This is the chain rule along `w ↦ (z₀, w)`, whose derivative is `inr`, together with the
fact that the analytical derivative of the polynomial evaluation `w ↦ p.eval w` is
`w ↦ p.derivative.eval w`. -/
theorem fderiv_snd_Pz_eval (P : Polynomial (ℂ → ℂ)) (z₀ α : ℂ)
    (hdiff : DifferentiableAt ℂ (fun p : ℂ × ℂ => (Work.WilC4aP.Pz P p.1).eval p.2) (z₀, α)) :
    (fderiv ℂ (fun p : ℂ × ℂ => (Work.WilC4aP.Pz P p.1).eval p.2) (z₀, α))
        ∘L ContinuousLinearMap.inr ℂ ℂ ℂ
      = ((Work.WilC4aP.Pz P z₀).derivative.eval α) • (1 : ℂ →L[ℂ] ℂ) := by
  -- Derivative of the affine right inclusion `w ↦ (z₀, w)`.
  have hG : HasFDerivAt (fun t : ℂ => (z₀, t)) (ContinuousLinearMap.inr ℂ ℂ ℂ) α :=
    hasFDerivAt_prodMk_right z₀ α
  -- Chain rule: the composition is `w ↦ (Pz P z₀).eval w`, restricted to the second slot.
  have hcomp := hdiff.hasFDerivAt.comp α hG
  have h1 : fderiv ℂ (fun p : ℂ × ℂ => (Work.WilC4aP.Pz P p.1).eval p.2) (z₀, α)
        ∘L ContinuousLinearMap.inr ℂ ℂ ℂ
      = fderiv ℂ (fun t : ℂ => (Work.WilC4aP.Pz P z₀).eval t) α := by
    rw [← hcomp.fderiv]
    rfl
  rw [h1, Polynomial.fderiv]
  -- `Polynomial.fderiv` produces `smulRight 1 c`, which is `c • 1` for the commutative field `ℂ`.
  apply ContinuousLinearMap.ext_ring
  simp

end Work.WilC4aP
