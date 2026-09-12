import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.F_bernstein

/-! Derivative bounds for the Section-3 functions `α`, `β`, `H` (paper
arXiv:1907.09464v1, Lemma 3.5 "Shapiro bounds" and Lemma 3.6 "H derivative
upper bounds").

We need, for every real `x` and `1 ≤ k ≤ 4`:

    ‖α^(k)(x)‖, ‖β^(k)(x)‖ ≤ 2^(-9k)

(any constant ≤ 2^(-9k) is fine; the paper has 2^(-10k)); and, with slack,
for `0 ≤ k ≤ 4`:

    ‖H^(k)(x) − (i^k e^{ix} α(x) + (2i)^k e^{2ix} β(x))‖ ≤ 1/8
    ‖H^(k)(x)‖ ≤ 2^k + 2

SUGGESTED ROUTE (paper §3):
1. First prove a general Bernstein-type iteration for complex polynomials:
   if `R : ℂ[X]`, `natDegree R ≤ d`, and `sup_{|w|=1} ‖R.eval w‖ ≤ M`, then
   the θ-derivatives satisfy `sup_θ ‖(d^k/dθ^k) R.eval(e^{iθ})‖ ≤ d^k · M`.
   Proceed by induction on `k`: define `S_0 := R` and `S_{m+1} := i·X·S_m'`
   (`derivative`), prove `(d^k/dθ^k) R.eval(eθ θ) = S_k.eval(eθ θ)` using
   the chain rule `deriv (fun θ => F.eval (eθ θ)) θ = i·eθ θ · F'.eval(eθ θ)`,
   and bound `sup_{|w|=1}‖S_k.eval w‖ ≤ d^k M` by repeated application of
   the existing complex Bernstein lemma (imported above):
   `bernstein_poly P n hdeg M hM z hz : ‖eval z (derivative P)‖ ≤ (n:ℝ)*M`.
   For `R = P t` use `M = sqrt (2^(t+1))` (`RudinShapiro.norm_P_eval_le`,
   `norm_Q_eval_le`, degree ≤ `2^t` from `P_natDegree_le`).

2. Prove the rescaling identity for iterated derivatives under `x ↦ x/T`:
   `iteratedDeriv k (fun x : ℝ => f (x / (T t : ℝ))) x =
      (1/(T t : ℝ))^k · iteratedDeriv k f (x / (T t : ℝ))`
   by induction on `k` (`iteratedDeriv_succ`, `deriv_comp`, `deriv_const_mul`).

3. Since `alpha t x = (scale t : ℂ) · P.eval(eθ (x/T))` (and similarly `beta`),
   use steps 1–2 with `d = 2^t`, `T = 2^(t+10)` to get the factor
   `scale·T^(-k)·d^k·sqrt(2^(t+1)) = 2^(-10k)` (paper), or simply conclude
   `≤ 2^(-9k)`.

4. For `H`: write `H(x) = f(x)·α(x) + g(x)·β(x)` with `f = e^{ix}`, `g = e^{2ix}`.
   Use the Leibniz rule (`iteratedDeriv_mul`, needs ContDiffAt) plus the known
   `iteratedDeriv k (fun x => eθ x) x = i^k · eθ x` (prove by induction from
   `HasDerivAt`), to show
   `H^(k)(x) − (i^k e^{ix} α + (2i)^k e^{2ix} β)` is a combination of
   `α^(j), β^(j)`, `j ≥ 1`, whose norm is bounded by
   `Σ_{j=1}^k C(k,j) (1 + 2^(k-j)) · 2^(-9j) ≤ 1/8` for `k ≤ 4` (verify by
   `norm_num`-style arithmetic; it is ≈ 0.07).  Then `‖H^(k)‖ ≤ 2^k + 2`
   follows from `‖α‖,‖β‖ ≤ 1` (`Sec3H.norm_alpha_le`, `norm_beta_le`) and the
   triangle inequality (compute numerically; slack is fine).

All functions are analytic so `iteratedDeriv` values exist; you may need
`ContDiffAt`/`ContDiff` side conditions for `iteratedDeriv_mul`/`_add`:
`Complex.exp` is entire and `P.eval ∘ eθ ∘ (·/T)` is smooth (all `ContDiff`),
so these are provable by `fun_prop` / `exact (Sec3H.alpha ...).contDiff` style.
The final file must contain no placeholders. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace Sec3H

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
      change deriv (fun y : ℝ => ((a : ℂ)⁻¹) ^ k * (thetaPoly P k).eval (Sec3.eθ (y / a))) x
          = ((a : ℂ)⁻¹) ^ k * ((((a : ℂ)⁻¹) * (Complex.I * Sec3.eθ (x / a))) •
              (thetaPoly P k).derivative.eval (Sec3.eθ (x / a))) at hv
      rw [hv]
      simp
      rw [pow_succ]
      ring

lemma norm_inv_pow_mul {u : ℝ} (hu : 0 ≤ u) (k : ℕ) (w : ℂ) :
    ‖(((u : ℂ)⁻¹) ^ k) * w‖ = (u⁻¹) ^ k * ‖w‖ := by
  rw [norm_mul]
  have hpow : ‖((u : ℂ)⁻¹) ^ k‖ = (u⁻¹) ^ k := by
    rw [norm_pow]
    rw [norm_inv, norm_of_real, abs_of_nonneg hu]
  rw [hpow]

/-- auxiliary arithmetic bound -/
lemma alpha_bound_aux (t k : ℕ) :
    scale t * ((T t : ℝ)⁻¹) ^ k * ((((2 ^ t : ℕ) : ℝ) ^ k) * Real.sqrt (2 ^ (t + 1) : ℝ))
      ≤ 1 / (2 : ℝ) ^ (9 * k) := by
  have hscale_s : scale t * Real.sqrt (2 ^ (t + 1) : ℝ) = 1 := by
    unfold scale
    field_simp [show Real.sqrt (2 ^ (t + 1) : ℝ) ≠ 0 by positivity]
  have hmain : ((T t : ℝ)⁻¹) * (2 : ℝ) ^ t = 1 / (2 : ℝ) ^ 10 := by
    have hTpow : (T t : ℝ) = (2 : ℝ) ^ t * (2 : ℝ) ^ 10 := by
      have hpa : (2 : ℝ) ^ (t + 10) = (2 : ℝ) ^ t * (2 : ℝ) ^ 10 := by rw [pow_add]
      calc
        (T t : ℝ) = (2 : ℝ) ^ (t + 10) := by unfold T; simp [Nat.cast_pow]
        _ = (2 : ℝ) ^ t * (2 : ℝ) ^ 10 := hpa
    rw [mul_comm, hTpow]
    field_simp [show (2 : ℝ) ^ t ≠ 0 by positivity, show (2 : ℝ) ^ 10 ≠ 0 by positivity]
  have h1 : scale t * ((T t : ℝ)⁻¹) ^ k * ((((2 ^ t : ℕ) : ℝ) ^ k) * Real.sqrt (2 ^ (t + 1) : ℝ))
      = (((T t : ℝ)⁻¹) * (2 : ℝ) ^ t) ^ k := by
    calc
      scale t * ((T t : ℝ)⁻¹) ^ k * ((((2 ^ t : ℕ) : ℝ) ^ k) * Real.sqrt (2 ^ (t + 1) : ℝ))
          = scale t * ((T t : ℝ)⁻¹) ^ k * (((2 : ℝ) ^ t) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ)) := by
              simp [Nat.cast_pow]
      _ = (scale t * Real.sqrt (2 ^ (t + 1) : ℝ)) * (((T t : ℝ)⁻¹) ^ k * ((2 : ℝ) ^ t) ^ k) := by
              let q : ℝ := (2 : ℝ) ^ t
              let s : ℝ := Real.sqrt (2 ^ (t + 1) : ℝ)
              change scale t * ((T t : ℝ)⁻¹) ^ k * (q ^ k * s) = (scale t * s) * (((T t : ℝ)⁻¹) ^ k * q ^ k)
              ring
      _ = (((T t : ℝ)⁻¹) * (2 : ℝ) ^ t) ^ k := by
              rw [hscale_s]
              rw [← mul_pow]
              simp
  calc
    scale t * ((T t : ℝ)⁻¹) ^ k * ((((2 ^ t : ℕ) : ℝ) ^ k) * Real.sqrt (2 ^ (t + 1) : ℝ))
        = (((T t : ℝ)⁻¹) * (2 : ℝ) ^ t) ^ k := h1
    _ = (1 / (2 : ℝ) ^ 10) ^ k := by rw [hmain]
    _ = 1 / (2 : ℝ) ^ (10 * k) := by
            rw [one_div, inv_pow, ← pow_mul]
            ring
    _ ≤ 1 / (2 : ℝ) ^ (9 * k) := by
            have hmono : (2 : ℝ) ^ (9 * k) ≤ (2 : ℝ) ^ (10 * k) := by
              exact pow_le_pow_right₀ (by norm_num) (by omega)
            have h1 : 0 < (2 : ℝ) ^ (9 * k) := by positivity
            exact one_div_le_one_div_of_le h1 hmono


/-- Rescaled-derivative bound for `α` (paper eq. `|α^(k)| ≤ 2^{-10k}`; loose `2^{-9k}` OK). -/
lemma alpha_iter_deriv_le (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (alpha t) x‖ ≤ 1 / 2 ^ (9 * k) := by
  unfold alpha
  rw [iteratedDeriv_const_mul_field]
  rw [norm_scale_mul]
  rw [thetaPoly_eval_eq_iteratedDeriv_scaled]
  have hT0 : 0 < (T t : ℝ) := by
    have h : 0 < 2 ^ (t + 10) := pow_pos (by norm_num) (t + 10)
    exact_mod_cast h
  rw [norm_inv_pow_mul hT0.le]
  have hdeg : (RudinShapiro.P t).natDegree ≤ 2 ^ t :=
    (RudinShapiro.P_natDegree_le t).trans (Nat.sub_le (2 ^ t) 1)
  have hSnorm : ‖(thetaPoly (RudinShapiro.P t) k).eval (Sec3.eθ (x / (T t : ℝ)))‖ ≤
      ((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ) := by
    exact thetaPoly_eval_norm_le (P := RudinShapiro.P t) hdeg
      (Real.sqrt (2 ^ (t + 1) : ℝ)) (RudinShapiro.norm_P_eval_le t) k (Sec3.eθ (x / (T t : ℝ)))
      (Sec3.norm_eθ (x / (T t : ℝ)))
  have hTinv0 : 0 ≤ ((T t : ℝ)⁻¹) ^ k := by positivity
  have hscale0 : 0 ≤ scale t := scale_nonneg t
  have hle : scale t * (((T t : ℝ)⁻¹) ^ k * ‖(thetaPoly (RudinShapiro.P t) k).eval (Sec3.eθ (x / (T t : ℝ)))‖) ≤
      scale t * (((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ))) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSnorm hTinv0) hscale0
  exact le_trans hle (by
    have h' : scale t * (((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ)))
        = scale t * ((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ)) := by ring
    rw [h']
    exact alpha_bound_aux t k)

lemma beta_iter_deriv_le (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (beta t) x‖ ≤ 1 / 2 ^ (9 * k) := by
  unfold beta
  rw [iteratedDeriv_const_mul_field]
  rw [norm_scale_mul]
  rw [thetaPoly_eval_eq_iteratedDeriv_scaled]
  have hT0 : 0 < (T t : ℝ) := by
    have h : 0 < 2 ^ (t + 10) := pow_pos (by norm_num) (t + 10)
    exact_mod_cast h
  rw [norm_inv_pow_mul hT0.le]
  have hdeg : (RudinShapiro.Q t).natDegree ≤ 2 ^ t :=
    (RudinShapiro.Q_natDegree_le t).trans (Nat.sub_le (2 ^ t) 1)
  have hSnorm : ‖(thetaPoly (RudinShapiro.Q t) k).eval (Sec3.eθ (x / (T t : ℝ)))‖ ≤
      ((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ) := by
    exact thetaPoly_eval_norm_le (P := RudinShapiro.Q t) hdeg
      (Real.sqrt (2 ^ (t + 1) : ℝ)) (RudinShapiro.norm_Q_eval_le t) k (Sec3.eθ (x / (T t : ℝ)))
      (Sec3.norm_eθ (x / (T t : ℝ)))
  have hTinv0 : 0 ≤ ((T t : ℝ)⁻¹) ^ k := by positivity
  have hscale0 : 0 ≤ scale t := scale_nonneg t
  have hle : scale t * (((T t : ℝ)⁻¹) ^ k * ‖(thetaPoly (RudinShapiro.Q t) k).eval (Sec3.eθ (x / (T t : ℝ)))‖) ≤
      scale t * (((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ))) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSnorm hTinv0) hscale0
  exact le_trans hle (by
    have h' : scale t * (((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ)))
        = scale t * ((T t : ℝ)⁻¹) ^ k * (((2 ^ t : ℕ) : ℝ) ^ k * Real.sqrt (2 ^ (t + 1) : ℝ)) := by ring
    rw [h']
    exact alpha_bound_aux t k)

lemma exp_c_mul_contDiff {n : WithTop ℕ∞} (c : ℂ) :
    ContDiff ℝ n (fun x : ℝ => Complex.exp (c * (x : ℂ))) := by
  let L : ℝ →L[ℝ] ℂ := ((ContinuousLinearMap.mul ℝ ℂ) c).comp Complex.ofRealCLM
  have hL : ContDiff ℝ n (L : ℝ → ℂ) := ContinuousLinearMap.contDiff L
  have hexp : ContDiff ℝ n (Complex.exp : ℂ → ℂ) :=
    (Complex.contDiff_exp : ContDiff ℂ n (Complex.exp : ℂ → ℂ)).restrict_scalars ℝ
  have h : ContDiff ℝ n (fun x : ℝ => Complex.exp (L x)) := by
    change ContDiff ℝ n (Complex.exp ∘ (L : ℝ → ℂ))
    exact hexp.comp hL
  convert h using 1
  ext x
  exact congrArg Complex.exp (by simp [L, ContinuousLinearMap.mul_apply'])

lemma contDiff_eθ {n : WithTop ℕ∞} : ContDiff ℝ n (fun x : ℝ => Sec3.eθ x) := by
  have h := exp_c_mul_contDiff (n := n) Complex.I
  unfold Sec3.eθ
  convert h using 1
  ext x
  ring

lemma contDiff_eθ_mul {n : WithTop ℕ∞} (c : ℝ) : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (c * x)) := by
  have h := exp_c_mul_contDiff (n := n) (((c : ℂ) * Complex.I))
  unfold Sec3.eθ
  convert h using 1
  ext x
  apply congrArg Complex.exp
  rw [Complex.ofReal_mul]
  ring

lemma polyEval_contDiff {n : WithTop ℕ∞} (Q : ℂ[X]) : ContDiff ℝ n (fun z : ℂ => Q.eval z) := by
  simpa using ((Polynomial.contDiff_aeval (R := ℂ) (𝕜 := ℂ) Q n).restrict_scalars ℝ)

lemma contDiff_alpha {n : WithTop ℕ∞} (t : ℕ) : ContDiff ℝ n (fun x : ℝ => alpha t x) := by
  have hmain : ContDiff ℝ n (fun x : ℝ => (RudinShapiro.P t).eval (Sec3.eθ (x / (T t : ℝ)))) := by
    have hin : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (((T t : ℝ)⁻¹) * x)) := by
      have h := contDiff_eθ_mul (n := n) ((T t : ℝ)⁻¹)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hq := polyEval_contDiff (n := n) (RudinShapiro.P t)
    change ContDiff ℝ n ((fun z : ℂ => (RudinShapiro.P t).eval z) ∘ (fun x : ℝ => Sec3.eθ (x / (T t : ℝ))))
    apply hq.comp
    simpa [div_eq_mul_inv, mul_comm] using hin
  have hc : ContDiff ℝ n (fun _ : ℝ => (scale t : ℂ)) := contDiff_const
  have hprod := hc.mul hmain
  unfold alpha
  exact hprod

lemma contDiff_beta {n : WithTop ℕ∞} (t : ℕ) : ContDiff ℝ n (fun x : ℝ => beta t x) := by
  have hmain : ContDiff ℝ n (fun x : ℝ => (RudinShapiro.Q t).eval (Sec3.eθ (x / (T t : ℝ)))) := by
    have hin : ContDiff ℝ n (fun x : ℝ => Sec3.eθ (((T t : ℝ)⁻¹) * x)) := by
      have h := contDiff_eθ_mul (n := n) ((T t : ℝ)⁻¹)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hq := polyEval_contDiff (n := n) (RudinShapiro.Q t)
    change ContDiff ℝ n ((fun z : ℂ => (RudinShapiro.Q t).eval z) ∘ (fun x : ℝ => Sec3.eθ (x / (T t : ℝ))))
    apply hq.comp
    simpa [div_eq_mul_inv, mul_comm] using hin
  have hc : ContDiff ℝ n (fun _ : ℝ => (scale t : ℂ)) := contDiff_const
  have hprod := hc.mul hmain
  unfold beta
  exact hprod

lemma iteratedDeriv_eθ (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Sec3.eθ y) x = Complex.I ^ k * Sec3.eθ x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => Sec3.eθ y) = fun y : ℝ => Complex.I ^ k * Sec3.eθ y := by
        funext y
        exact ih y
      rw [hfun]
      have hθ := eθ_hasDerivAt x
      have hc := hθ.const_mul (Complex.I ^ k)
      have hv := hc.deriv
      rw [hv]
      rw [← mul_assoc]
      rw [← pow_succ]

lemma eθ2_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Sec3.eθ (2 * y)) (((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x)) x := by
  have hφ : HasDerivAt (fun y : ℝ => 2 * y) (2 : ℝ) x := by
    simpa using hasDerivAt_const_mul (x := x) (c := (2 : ℝ))
  have hθ := eθ_hasDerivAt (2 * x)
  have hc := hθ.scomp x hφ
  have hsmul : (2 : ℝ) • (Complex.I * Sec3.eθ (2 * x)) = ((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x) := by
    rw [Algebra.smul_def]
    change ((2 : ℝ) : ℂ) * (Complex.I * Sec3.eθ (2 * x)) = ((2 : ℂ) * Complex.I) * Sec3.eθ (2 * x)
    norm_num
    ring
  exact hc.congr_deriv hsmul

lemma iteratedDeriv_eθ2 (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Sec3.eθ (2 * y)) x = ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (fun y : ℝ => Sec3.eθ (2 * y)) =
          fun y : ℝ => ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * y) := by
        funext y
        exact ih y
      rw [hfun]
      have hθ := eθ2_hasDerivAt x
      have hc := hθ.const_mul (((2 : ℂ) * Complex.I) ^ k)
      have hv := hc.deriv
      rw [hv]
      rw [← mul_assoc]
      rw [← pow_succ]

/-- product eθ·α (first H term) -/
def FA (t : ℕ) : ℝ → ℂ := fun y => Sec3.eθ y * alpha t y
/-- product eθ(2·)·β (second H term) -/
def FB (t : ℕ) : ℝ → ℂ := fun y => Sec3.eθ (2 * y) * beta t y

lemma H_eq_FA_add_FB (t : ℕ) : H t = FA t + FB t := by
  funext x
  rfl

lemma iteratedDeriv_FA_sum (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FA t) x =
      ∑ i ∈ Finset.range (k + 1),
        (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x) := by
  have hf : ContDiffAt ℝ k (fun y : ℝ => Sec3.eθ y) x := (contDiff_eθ (n := k)).contDiffAt
  have hg : ContDiffAt ℝ k (alpha t) x := (contDiff_alpha (n := k) t).contDiffAt
  unfold FA
  change iteratedDeriv k ((fun y : ℝ => Sec3.eθ y) * alpha t) x =
      ∑ i ∈ Finset.range (k + 1), (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)
  rw [iteratedDeriv_mul hf hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_eθ i x]

lemma iteratedDeriv_FB_sum (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FB t) x =
      ∑ i ∈ Finset.range (k + 1),
        (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x) := by
  have hf : ContDiffAt ℝ k (fun y : ℝ => Sec3.eθ (2 * y)) x := (contDiff_eθ_mul (n := k) 2).contDiffAt
  have hg : ContDiffAt ℝ k (beta t) x := (contDiff_beta (n := k) t).contDiffAt
  unfold FB
  change iteratedDeriv k ((fun y : ℝ => Sec3.eθ (2 * y)) * beta t) x =
      ∑ i ∈ Finset.range (k + 1), (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)
  rw [iteratedDeriv_mul hf hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_eθ2 i x]

/-- cancellation: FA^k minus its leading term is a sum over i < k -/
lemma FA_sub_target (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)
      = ∑ i ∈ Finset.range k,
          (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x) := by
  rw [iteratedDeriv_FA_sum]
  rw [Finset.sum_range_succ]
  simp [Nat.choose_self]

/-- cancellation: FB^k minus leading term -/
lemma FB_sub_target (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)
      = ∑ i ∈ Finset.range k,
          (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x) := by
  rw [iteratedDeriv_FB_sum]
  rw [Finset.sum_range_succ]
  simp [Nat.choose_self]

lemma norm_mul_mul (a b c : ℂ) : ‖(a * b) * c‖ = ‖a‖ * ‖b‖ * ‖c‖ := by
  rw [norm_mul, norm_mul]

lemma norm_eθ_I_pow (i : ℕ) (x : ℝ) : ‖(Complex.I ^ i * Sec3.eθ x)‖ = 1 := by
  rw [norm_mul, norm_pow, Complex.norm_I, Sec3.norm_eθ]
  norm_num

lemma norm_eθ_2I_pow (i : ℕ) (x : ℝ) : ‖(((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))‖ = (2 : ℝ) ^ i := by
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, Sec3.norm_eθ]
  norm_num

lemma norm_choose_natCast (k i : ℕ) : ‖(k.choose i : ℂ)‖ = (k.choose i : ℝ) := by
  change ‖(((k.choose i : ℝ) : ℂ))‖ = (k.choose i : ℝ)
  rw [norm_of_real]
  rw [abs_of_nonneg (show 0 ≤ (k.choose i : ℝ) by exact_mod_cast (Nat.zero_le _))]

lemma alpha_deriv_bound (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (alpha t) x‖ ≤ 1 / (2 : ℝ) ^ (9 * k) := alpha_iter_deriv_le t hk1 hk4 x

lemma beta_deriv_bound (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (beta t) x‖ ≤ 1 / (2 : ℝ) ^ (9 * k) := beta_iter_deriv_le t hk1 hk4 x

lemma norm_FA_term_le (t : ℕ) {k : ℕ} {i : ℕ} (x : ℝ) (hki1 : 1 ≤ k - i) (hki4 : k - i ≤ 4) :
    ‖(((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)‖
      ≤ (k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))) := by
  have hnm := norm_mul_mul (k.choose i : ℂ) (Complex.I ^ i * Sec3.eθ x) (iteratedDeriv (k - i) (alpha t) x)
  rw [hnm]
  rw [norm_choose_natCast]
  rw [norm_eθ_I_pow]
  have hb := alpha_iter_deriv_le t hki1 hki4 x
  have hc0 : 0 ≤ (k.choose i : ℝ) := by exact_mod_cast (Nat.zero_le _)
  -- (choose:ℝ) * 1 * ‖w‖ ≤ choose * (1/2^(9(k-i)))
  calc
    (k.choose i : ℝ) * 1 * ‖iteratedDeriv (k - i) (alpha t) x‖
        = (k.choose i : ℝ) * ‖iteratedDeriv (k - i) (alpha t) x‖ := by ring
    _ ≤ (k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))) := mul_le_mul_of_nonneg_left hb hc0

lemma norm_FB_term_le (t : ℕ) {k : ℕ} {i : ℕ} (x : ℝ) (hki1 : 1 ≤ k - i) (hki4 : k - i ≤ 4) :
    ‖(((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)‖
      ≤ (k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i))) := by
  have hnm := norm_mul_mul (k.choose i : ℂ) (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x)) (iteratedDeriv (k - i) (beta t) x)
  rw [hnm]
  rw [norm_choose_natCast]
  rw [norm_eθ_2I_pow]
  have hb := beta_iter_deriv_le t hki1 hki4 x
  have hc0 : 0 ≤ (k.choose i : ℝ) := by exact_mod_cast (Nat.zero_le _)
  calc
    (k.choose i : ℝ) * (2 : ℝ) ^ i * ‖iteratedDeriv (k - i) (beta t) x‖
        ≤ (k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i))) := by
            exact mul_le_mul_of_nonneg_left hb (mul_nonneg hc0 (pow_nonneg (by norm_num) i))

lemma norm_FA_sub_target_le (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)‖
      ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
  rw [FA_sub_target]
  calc
    ‖∑ i ∈ Finset.range k, (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)‖
        ≤ ∑ i ∈ Finset.range k, ‖(((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hlt : i < k := Finset.mem_range.mp hi
        exact norm_FA_term_le t x (by omega) (by omega)

lemma norm_FB_sub_target_le (t : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)‖
      ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
  rw [FB_sub_target]
  calc
    ‖∑ i ∈ Finset.range k, (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)‖
        ≤ ∑ i ∈ Finset.range k, ‖(((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 : ℝ) ^ i * (1 / (2 : ℝ) ^ (9 * (k - i)))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hlt : i < k := Finset.mem_range.mp hi
        exact norm_FB_term_le t x (by omega) (by omega)

/-- auxiliary arithmetic bound for the H approximation -/
lemma H_bound_aux (k : ℕ) (hk : k ≤ 4) :
    (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
      (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) ≤ 1 / 8 := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num [Finset.sum_range_succ, show Nat.choose 1 0 = 1 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 2 0 = 1 by native_decide,
      show Nat.choose 2 1 = 2 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 3 0 = 1 by native_decide,
      show Nat.choose 3 1 = 3 by native_decide, show Nat.choose 3 2 = 3 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 4 0 = 1 by native_decide,
      show Nat.choose 4 1 = 4 by native_decide, show Nat.choose 4 2 = 6 by native_decide,
      show Nat.choose 4 3 = 4 by native_decide]



lemma H_iter_deriv_approx (t : ℕ) {k : ℕ} (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (H t) x -
        ((Complex.I ^ k) * Sec3.eθ x * alpha t x +
          ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)‖ ≤ 1 / 8 := by
  by_cases hk0 : k = 0
  · subst k
    simp [H]
  · have hk1 : 1 ≤ k := by omega
    have hFA : ContDiffAt ℝ k (FA t) x := by
      unfold FA
      exact ((contDiff_eθ (n := k)).contDiffAt.mul (contDiff_alpha (n := k) t).contDiffAt)
    have hFB : ContDiffAt ℝ k (FB t) x := by
      unfold FB
      exact ((contDiff_eθ_mul (n := k) 2).contDiffAt.mul (contDiff_beta (n := k) t).contDiffAt)
    rw [H_eq_FA_add_FB]
    have hadd := iteratedDeriv_add (n := k) (f := FA t) (g := FB t) hFA hFB
    rw [hadd]
    -- target split
    have htarget : (iteratedDeriv k (FA t) x + iteratedDeriv k (FB t) x) -
        ((Complex.I ^ k * Sec3.eθ x * alpha t x) + (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x))
        = (iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)) := by ring
    rw [htarget]
    have h1 := norm_FA_sub_target_le t hk1 hk4 x
    have h2 := norm_FB_sub_target_le t hk1 hk4 x
    calc
      ‖(iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)) +
          (iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x))‖
          ≤ ‖iteratedDeriv k (FA t) x - (Complex.I ^ k * Sec3.eθ x * alpha t x)‖ +
              ‖iteratedDeriv k (FB t) x - (((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x)‖ := norm_add_le _ _
      _ ≤ (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
            (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) := by
            exact add_le_add h1 h2
      _ ≤ 1 / 8 := H_bound_aux k hk4

lemma H_iter_deriv_norm_le (t : ℕ) {k : ℕ} (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (H t) x‖ ≤ (2 : ℝ) ^ k + 2 := by
  let T1 : ℂ := Complex.I ^ k * Sec3.eθ x * alpha t x
  let T2 : ℂ := ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x
  have hdiff : ‖iteratedDeriv k (H t) x - (T1 + T2)‖ ≤ 1 / 8 := by
    simpa [T1, T2] using (H_iter_deriv_approx t hk4 x)
  have hT1 : ‖T1‖ ≤ 1 := by
    unfold T1
    rw [norm_mul]
    rw [norm_eθ_I_pow k x]
    have hα : ‖alpha t x‖ ≤ 1 := norm_alpha_le t x
    nlinarith
  have hT2 : ‖T2‖ ≤ (2 : ℝ) ^ k := by
    unfold T2
    rw [norm_mul]
    rw [norm_eθ_2I_pow k x]
    have hβ : ‖beta t x‖ ≤ 1 := norm_beta_le t x
    have hp : 0 ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) k
    have hle : (2 : ℝ) ^ k * ‖beta t x‖ ≤ (2 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left hβ hp
    nlinarith
  have hTsum1 : ‖T1 + T2‖ ≤ ‖T1‖ + ‖T2‖ := norm_add_le T1 T2
  have hb : ‖iteratedDeriv k (H t) x‖ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := by
    calc
      ‖iteratedDeriv k (H t) x‖ = ‖(iteratedDeriv k (H t) x - (T1 + T2)) + (T1 + T2)‖ := by ring
      _ ≤ ‖iteratedDeriv k (H t) x - (T1 + T2)‖ + ‖T1 + T2‖ := norm_add_le _ _
      _ ≤ 1 / 8 + ‖T1 + T2‖ := by nlinarith [hdiff]
      _ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := by nlinarith [hTsum1]
  calc
    ‖iteratedDeriv k (H t) x‖ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := hb
    _ ≤ 1 / 8 + (1 + (2 : ℝ) ^ k) := by nlinarith [hT1, hT2]
    _ ≤ (2 : ℝ) ^ k + 2 := by nlinarith

lemma H_deriv_norm_le_four (t : ℕ) (x : ℝ) : ‖deriv (H t) x‖ ≤ 4 := by
  have h := H_iter_deriv_norm_le t (k := 1) (hk4 := by norm_num) x
  rw [iteratedDeriv_one] at h
  norm_num at h
  exact h

end Submission.Sec3H
