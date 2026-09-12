import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Analysis.MvPolynomial

set_option autoImplicit false

/-- A real (coordinate-wise) translation preserves stability of a real multivariate
polynomial: if `p` is stable (zero, or nonvanishing on the open upper half plane), then
the substitution `X_i ↦ X_i + w_i` (real `w`) is stable too. -/
theorem isStable_bind_add (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ)
    (hp : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (w i)) p = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
          (MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (w i)) p) ≠ 0 := by
  classical
  rcases hp with hp0 | hpz
  · left
    simp [hp0]
  · right
    intro z
    let z' : Fin n → UpperHalfPlane := fun i => w i +ᵥ z i
    have hne : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) p ≠ 0 :=
      hpz z'
    have hfun : (fun i : Fin n =>
          MvPolynomial.aeval (fun j : Fin n => ((z j : UpperHalfPlane) : ℂ))
            (MvPolynomial.X i + MvPolynomial.C (w i))) =
        (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) := by
      funext i
      dsimp [z']
      simp
      ring
    have hmain :
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
            (MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (w i)) p)
          = MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) p := by
      rw [MvPolynomial.aeval_bind₁ (R := ℝ) (S := ℂ)
        (f := fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
        (g := fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (w i)) (φ := p)]
      rw [hfun]
    rw [hmain]
    exact hne

end Commons.Analysis.MvPolynomial