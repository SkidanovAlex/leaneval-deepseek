import Mathlib
import Submission.Work.ZeroEst.mderiv_adjugate_mul
import Submission.Work.ZeroEst.ps_eq_C_mul_of_deriv_mul
import Submission.Work.ZeroEst3.minorsODES

/-!
# `Work.ZeroEstB.minor_det_prop`

Let `Ψ` be an `r × m` matrix of power series over `ℚ` whose columns solve the first order linear
system `sq • Ψ' = N Ψ` with `sq ≠ 0`.  Then *every* maximal minor `det(Ψ.submatrix id T)` of `Ψ` is
`C c` times a fixed nonzero one `det(Ψ.submatrix id T₀)`.

Indeed each maximal minor satisfies the scalar ODE `sq • D_S' = tr(N) · D_S`
(`Work.ZeroEst3.minorsODES`), so any two of them have vanishing Wronskian; since `sq ≠ 0` and
`PowerSeries ℚ` is a domain, `D_T' · D_T₀ = D_T · D_T₀'`, and
`Work.ZeroEst.ps_eq_C_mul_of_deriv_mul` says that two power series satisfying a Wronskian relation
are proportional by a constant, which over a field is `PowerSeries.C c` with `c : ℚ`.
-/

namespace Work.ZeroEstB

open Matrix PowerSeries

theorem minor_det_prop {r m : ℕ} (sq : PowerSeries ℚ) (Psi : Matrix (Fin r) (Fin m) (PowerSeries ℚ))
    (N : Matrix (Fin r) (Fin r) (PowerSeries ℚ)) (hsq : sq ≠ 0)
    (h : sq • Work.ZeroEst.mderiv Psi = N * Psi)
    (T₀ : Fin r → Fin m) (hdet₀ : (Psi.submatrix id T₀).det ≠ 0) (T : Fin r → Fin m) :
    ∃ c : ℚ, (Psi.submatrix id T).det = PowerSeries.C c * (Psi.submatrix id T₀).det := by
  classical
  -- The matrix identity `sq • Ψ' = N Ψ` read entrywise.
  have hODE : ∀ i j, sq * PowerSeries.derivative (R := ℚ) (Psi i j) = ∑ k, N i k * Psi k j := by
    intro i j
    have hij := congr_fun (congr_fun h i) j
    simpa [Matrix.smul_apply, Work.ZeroEst.mderiv_apply, Matrix.mul_apply] using hij
  -- Every maximal minor satisfies the scalar ODE `sq * D_S' = tr N * D_S`.
  have key : ∀ S : Fin r → Fin m,
      sq * PowerSeries.derivative (R := ℚ) ((Psi.submatrix id S).det)
        = Matrix.trace N * (Psi.submatrix id S).det :=
    fun S => Work.ZeroEst3.minorsODES Psi sq N hODE S
  by_cases hT : (Psi.submatrix id T).det = 0
  · -- A vanishing minor is `C 0` times the fixed one.
    exact ⟨0, by rw [hT, map_zero, zero_mul]⟩
  · -- Otherwise both minors solve the same first order ODE, so their Wronskian vanishes.
    have hw : PowerSeries.derivative (R := ℚ) (Psi.submatrix id T).det * (Psi.submatrix id T₀).det
        = (Psi.submatrix id T).det * PowerSeries.derivative (R := ℚ) (Psi.submatrix id T₀).det := by
      have hA : sq * (PowerSeries.derivative (R := ℚ) (Psi.submatrix id T).det
            * (Psi.submatrix id T₀).det)
          = Matrix.trace N * ((Psi.submatrix id T).det * (Psi.submatrix id T₀).det) := by
        rw [← mul_assoc, key T, mul_assoc]
      have hB : sq * (PowerSeries.derivative (R := ℚ) (Psi.submatrix id T₀).det
            * (Psi.submatrix id T).det)
          = Matrix.trace N * ((Psi.submatrix id T).det * (Psi.submatrix id T₀).det) := by
        calc sq * (PowerSeries.derivative (R := ℚ) (Psi.submatrix id T₀).det
              * (Psi.submatrix id T).det)
            = (sq * PowerSeries.derivative (R := ℚ) (Psi.submatrix id T₀).det)
                * (Psi.submatrix id T).det := (mul_assoc _ _ _).symm
          _ = (Matrix.trace N * (Psi.submatrix id T₀).det) * (Psi.submatrix id T).det := by
                rw [key T₀]
          _ = Matrix.trace N * ((Psi.submatrix id T₀).det * (Psi.submatrix id T).det) :=
                mul_assoc _ _ _
          _ = Matrix.trace N * ((Psi.submatrix id T).det * (Psi.submatrix id T₀).det) := by
                rw [mul_comm (Psi.submatrix id T₀).det (Psi.submatrix id T).det]
      have hcancel := mul_left_cancel₀ hsq (hA.trans hB.symm)
      rw [mul_comm (PowerSeries.derivative (R := ℚ) (Psi.submatrix id T₀).det)
        (Psi.submatrix id T).det] at hcancel
      exact hcancel
    exact Work.ZeroEst.ps_eq_C_mul_of_deriv_mul hdet₀ hw

end Work.ZeroEstB
