import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.F_bernstein

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

/-- iterated θ-derivative polynomial: S₀ = P, S_{k+1} = i·X·S_k' -/
def thetaPoly (P : ℂ[X]) : ℕ → ℂ[X]
  | 0 => P
  | k + 1 => Polynomial.C Complex.I * (Polynomial.X * (thetaPoly P k).derivative)

@[simp] lemma thetaPoly_zero (P : ℂ[X]) : thetaPoly P 0 = P := rfl
@[simp] lemma thetaPoly_succ (P : ℂ[X]) (k : ℕ) :
    thetaPoly P (k + 1) = Polynomial.C Complex.I * (Polynomial.X * (thetaPoly P k).derivative) := rfl

lemma eθ_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Sec3.eθ y) (Complex.I * Sec3.eθ x) x := by
  unfold Sec3.eθ
  have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) (Complex.I) x := by
    exact (hasDerivAt_mul_const (x := (x : ℂ)) (c := Complex.I)).comp_ofReal
  have h := (HasDerivAt.cexp (x := x) hlin)
  have ht : (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) = Complex.I * Complex.exp ((x : ℂ) * Complex.I) := by ring
  simpa [ht] using h

lemma deriv_poly_eθ (Q : ℂ[X]) (x : ℝ) :
    deriv (fun y : ℝ => Q.eval (Sec3.eθ y)) x = (Complex.I * Sec3.eθ x) * Q.derivative.eval (Sec3.eθ x) := by
  have hQ : HasDerivAt (fun z : ℂ => Q.eval z) (Q.derivative.eval (Sec3.eθ x)) (Sec3.eθ x) :=
    Polynomial.hasDerivAt Q (Sec3.eθ x)
  have hθ : HasDerivAt (fun y : ℝ => Sec3.eθ y) (Complex.I * Sec3.eθ x) x := eθ_hasDerivAt x
  have hcomp := hQ.scomp x hθ
  change HasDerivAt (fun y : ℝ => Q.eval (Sec3.eθ y))
      ((Complex.I * Sec3.eθ x) • Q.derivative.eval (Sec3.eθ x)) x at hcomp
  have hval := hcomp.deriv
  simpa [mul_comm, mul_left_comm, mul_assoc] using hval

lemma thetaPoly_eval_eq_iteratedDeriv (P : ℂ[X]) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => P.eval (Sec3.eθ y)) x = (thetaPoly P k).eval (Sec3.eθ x) := by
  induction k generalizing x with
  | zero => simp [thetaPoly]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => P.eval (Sec3.eθ y))
          = fun y : ℝ => (thetaPoly P k).eval (Sec3.eθ y) := by
        funext y
        exact ih y
      rw [hfun]
      rw [deriv_poly_eθ (thetaPoly P k) x]
      simp
      ring

/-- natDegree of X·Q' is ≤ natDegree Q -/
lemma natDegree_X_mul_derivative_le (Q : ℂ[X]) :
    (Polynomial.X * Q.derivative).natDegree ≤ Q.natDegree := by
  by_cases hz : Q.derivative = 0
  · rw [hz, mul_zero, natDegree_zero]
    exact Nat.zero_le _
  · have hq : 1 ≤ Q.natDegree := by
      by_contra hq0
      have : Q.natDegree = 0 := by omega
      exact hz (Polynomial.derivative_eq_zero.mpr this)
    rw [Polynomial.natDegree_X_mul hz, Polynomial.natDegree_derivative]
    omega

lemma thetaPoly_natDegree_le (P : ℂ[X]) {d : ℕ} (hdeg : P.natDegree ≤ d) (k : ℕ) :
    (thetaPoly P k).natDegree ≤ d := by
  induction k with
  | zero => simpa using hdeg
  | succ k ih =>
      calc
        (thetaPoly P (k + 1)).natDegree
            = (Polynomial.C Complex.I * (X * (thetaPoly P k).derivative)).natDegree := rfl
        _ ≤ (X * (thetaPoly P k).derivative).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ ≤ (thetaPoly P k).natDegree := natDegree_X_mul_derivative_le _
        _ ≤ d := ih

lemma thetaPoly_eval_norm_le (P : ℂ[X]) {d : ℕ} (hdeg : P.natDegree ≤ d) (M : ℝ)
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖P.eval w‖ ≤ M) (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(thetaPoly P k).eval z‖ ≤ (d : ℝ) ^ k * M := by
  induction k generalizing z with
  | zero => simpa using hM z hz
  | succ k ih =>
      let Q := thetaPoly P k
      have hQdeg : Q.natDegree ≤ d := by
        simpa [Q] using thetaPoly_natDegree_le P hdeg k
      have hQnorm : ∀ w : ℂ, ‖w‖ = 1 → ‖Q.eval w‖ ≤ (d : ℝ) ^ k * M := by
        intro w hw
        simpa [Q] using ih w hw
      have hbern := bernstein_poly (P := Q) (n := d) (M := (d : ℝ) ^ k * M) hQdeg hQnorm z hz
      have hnorm : ‖(thetaPoly P (k + 1)).eval z‖ = ‖Q.derivative.eval z‖ := by
        rw [thetaPoly_succ]
        simp [Q, Polynomial.eval_mul, Polynomial.eval_X]
        rw [hz]
        simp
      calc
        ‖(thetaPoly P (k + 1)).eval z‖ = ‖Q.derivative.eval z‖ := hnorm
        _ ≤ (d : ℝ) * ((d : ℝ) ^ k * M) := by simpa [Q] using hbern
        _ = (d : ℝ) ^ (k + 1) * M := by rw [pow_succ]; ring


lemma eθ_div_hasDerivAt (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Sec3.eθ (y / a))
      (((a : ℂ)⁻¹) * (Complex.I * Sec3.eθ (x / a))) x := by
  have hφ : HasDerivAt (fun y : ℝ => y / a) (a⁻¹) x := by
    simpa using ((hasDerivAt_id x).div_const a)
  have hθ := eθ_hasDerivAt (x / a)
  have hc := hθ.scomp x hφ
  -- hc : HasDerivAt (fun y : ℝ => Sec3.eθ (y / a)) ((a⁻¹ : ℝ) • (Complex.I * Sec3.eθ (x / a))) x
  have hsmul : (a⁻¹ : ℝ) • (Complex.I * Sec3.eθ (x / a)) =
      ((a : ℂ)⁻¹) * (Complex.I * Sec3.eθ (x / a)) := by
    rw [Algebra.smul_def]
    change ((a⁻¹ : ℝ) : ℂ) * (Complex.I * Sec3.eθ (x / a)) = ((a : ℂ)⁻¹) * (Complex.I * Sec3.eθ (x / a))
    rw [← Complex.ofReal_inv]
  exact hc.congr_deriv hsmul

lemma hasDerivAt_poly_eθ_div (Q : ℂ[X]) (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Q.eval (Sec3.eθ (y / a)))
      ((((a : ℂ)⁻¹) * (Complex.I * Sec3.eθ (x / a))) • Q.derivative.eval (Sec3.eθ (x / a))) x := by
  have hQ : HasDerivAt (fun z : ℂ => Q.eval z) (Q.derivative.eval (Sec3.eθ (x / a))) (Sec3.eθ (x / a)) :=
    Polynomial.hasDerivAt Q (Sec3.eθ (x / a))
  have hθ := eθ_div_hasDerivAt (a := a) (x := x)
  exact hQ.scomp x hθ

lemma deriv_poly_eθ_div (Q : ℂ[X]) (a x : ℝ) :
    deriv (fun y : ℝ => Q.eval (Sec3.eθ (y / a))) x =
      (((a : ℂ)⁻¹) * (Complex.I * Sec3.eθ (x / a))) * Q.derivative.eval (Sec3.eθ (x / a)) := by
  have hc := hasDerivAt_poly_eθ_div Q a x
  have hv := hc.deriv
  simpa [mul_comm, mul_left_comm, mul_assoc] using hv

lemma thetaPoly_eval_eq_iteratedDeriv_scaled (P : ℂ[X]) (a : ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => P.eval (Sec3.eθ (y / a))) x
      = ((a : ℂ)⁻¹) ^ k * (thetaPoly P k).eval (Sec3.eθ (x / a)) := by
  induction k generalizing x with
  | zero => simp [thetaPoly]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => P.eval (Sec3.eθ (y / a)))
          = fun y : ℝ => ((a : ℂ)⁻¹) ^ k * (thetaPoly P k).eval (Sec3.eθ (y / a)) := by
        funext y
        exact ih y
      rw [hfun]
      have hd := hasDerivAt_poly_eθ_div (thetaPoly P k) a x
      have hc := hd.const_mul (((a : ℂ)⁻¹) ^ k)
      have hv := hc.deriv
      -- hv : deriv (fun y => c * Q.eval (eθ (y/a))) x = c * ((((a:ℂ)⁻¹) * (I*z)) • Q'.eval z)
      change deriv (fun y : ℝ => ((a : ℂ)⁻¹) ^ k * (thetaPoly P k).eval (Sec3.eθ (y / a))) x
          = ((a : ℂ)⁻¹) ^ k * ((((a : ℂ)⁻¹) * (Complex.I * Sec3.eθ (x / a))) •
              (thetaPoly P k).derivative.eval (Sec3.eθ (x / a))) at hv
      rw [hv]
      simp
      ring
