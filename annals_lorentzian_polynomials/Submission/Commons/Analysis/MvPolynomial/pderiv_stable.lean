import Mathlib.Algebra.MvPolynomial.PDeriv
import Submission.Commons.Analysis.Complex.Polynomial.deriv_stable_of_stable
import Submission.Commons.Analysis.MvPolynomial.top_in_j_stable_of_stable
import Submission.Commons.Analysis.MvPolynomial.pderiv_stable_of_stable_nonneg

set_option linter.unusedVariables false

open MvPolynomial UpperHalfPlane
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace Commons.Analysis.MvPolynomial

/-- Partial derivatives preserve stability: if `p` is stable on the open upper half
plane (i.e. `p` is zero, or `p` does not vanish at any point of `UpperHalfPlane^m`),
then so is the partial derivative `∂_j p` (or it is zero).  This is the multivariate
Gauss--Lucas-type statement; no assumption on the coefficients is needed. -/
theorem pderiv_stable {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (j : Fin m) :
    (p = 0 ∨ ∀ z : Fin m → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) →
    (MvPolynomial.pderiv (R := ℝ) j p = 0 ∨ ∀ z : Fin m → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ))
        (MvPolynomial.pderiv (R := ℝ) j p) ≠ 0) := by
  classical
  intro hstab
  rcases hstab with hp0 | hpstab
  · left
    rw [hp0]
    simp [MvPolynomial.pderiv]
  · by_cases hpd : MvPolynomial.pderiv (R := ℝ) j p = 0
    · left
      exact hpd
    · right
      intro z
      let zc : Fin m → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
      have hp0' : p ≠ 0 := by
        intro hp0
        apply hpd
        rw [hp0]
        simp [MvPolynomial.pderiv]
      let S : Polynomial ℂ := sliceP zc j p
      have hSstab : ∀ u : UpperHalfPlane, S.eval (u : ℂ) ≠ 0 := by
        intro u
        dsimp [S]
        rw [sliceP_eval]
        let z' : Fin m → UpperHalfPlane := fun i => if i = j then u else z i
        have hval : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (z' i : ℂ)) p ≠ 0 :=
          hpstab z'
        have hfun : (fun i : Fin m => (if i = j then u else z i : UpperHalfPlane) : Fin m → ℂ) =
            (fun i : Fin m => if i = j then (u : ℂ) else zc i) := by
          funext i
          by_cases hij : i = j
          · simp [hij, zc]
          · simp [hij, zc]
        rw [← hfun]
        exact hval
      have hS0 : S ≠ 0 := by
        dsimp [S]
        refine eval_ne_zero_of_coeff (sliceP zc j p) (zc j) ?_
        have hS0' : (sliceP zc j p).eval (zc j) ≠ 0 := by
          rw [sliceP_eval]
          have hfun : (fun i : Fin m => if i = j then zc j else zc i) = zc := by
            funext i
            by_cases hij : i = j
            · simp [zc, hij]
            · simp [zc, hij]
          rw [hfun]
          exact hpstab z
        exact hS0'
      have hd : 1 ≤ degIn p j := degIn_pos_of_pderiv_ne_zero p j hpd
      have hTst := topInJ_stable_of_stable p j (Or.inr hpstab)
      have hT0 : topInJ p j ≠ 0 := topInJ_ne_zero_of_ne_zero p j hp0'
      have hTz : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (z i : ℂ)) (topInJ p j) ≠ 0 :=
        (hTst.resolve_left hT0) z
      have hrel := aeval_topInJ_eq_pow_mul_slice_coeff p j zc
      have hzc_ne : zc j ≠ 0 := UHP_complex_ne_zero (z j)
      have hcoeff_ne : S.coeff (degIn p j) ≠ 0 := by
        dsimp [S]
        by_contra hc
        have hrel' : MvPolynomial.aeval (R := ℝ) zc (topInJ p j) =
            (zc j) ^ degIn p j * (sliceP zc j p).coeff (degIn p j) := hrel
        rw [hc, mul_zero] at hrel'
        have hTz' : MvPolynomial.aeval (R := ℝ) zc (topInJ p j) ≠ 0 := by
          change MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (z i : ℂ)) (topInJ p j) ≠ 0
          exact hTz
        exact hTz' hrel'
      have hderiv : S.derivative = 0 ∨ ∀ u : UpperHalfPlane, S.derivative.eval (u : ℂ) ≠ 0 :=
        Commons.Analysis.Complex.Polynomial.deriv_stable_of_stable S hS0 hSstab
      have hderiv_ne : S.derivative ≠ 0 := by
        intro hder0
        have hc0 : S.coeff (degIn p j) = 0 :=
          coeff_eq_zero_of_derivative_eq_zero (R := ℂ) (P := S) hd hder0
        exact hcoeff_ne hc0
      have hderiv_ev : S.derivative.eval (zc j) ≠ 0 :=
        (hderiv.resolve_left hderiv_ne) (z j)
      by_contra h0
      have hfun : (fun i : Fin m => if i = j then zc j else zc i) =
          (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) := by
        funext i
        by_cases hij : i = j
        · simp [zc, hij]
        · simp [zc, hij]
      have hmain' : S.derivative.eval (zc j) =
          MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ))
            (MvPolynomial.pderiv (R := ℝ) j p) := by
        dsimp [S]
        rw [sliceP_deriv_eval, hfun]
      exact hderiv_ev (by simpa [hmain'] using h0)

end Commons.Analysis.MvPolynomial
