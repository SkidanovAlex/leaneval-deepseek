/-
# ZeroFreeTables — XY/Tf72FcClosed

`Tf72FcClosed`: the closed form of the Laplace transform `tf72Fc (4/3) z` of the test
function of Heath-Brown (1992), Lemma 7.2, with `λ = 4/3` (so that `x₀ = 3/2`):

  `tf72Fc (4/3) z = 64/45 / z - 512/81 / z³ + 1024/81 / z⁴ - 16384/729 / z⁶
     + e^{-3z/2} (1024/81 / z⁴ + 8192/243 / z⁵ + 16384/729 / z⁶)`.

On `[0, 3/2]` the integrand is `e^{-zt} P(t)` with the quintic `P = tf72poly (4/3)`
(with `P(0) = 64/45` and a triple zero at `3/2`, so that `P(3/2) = P'(3/2) = P''(3/2) = 0`),
whose primitive is `e^{-zt} W(t)`, with `W` the degree-5 polynomial (with `z`-dependent
coefficients) determined by `W' - z W = P`.  The boundary values `W(0)` and `W(3/2)`
produce the two groups of terms.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72Fc_decay

open MeasureTheory intervalIntegral
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- The quintic `tf72poly (4/3)`, as a complex polynomial in `w`. -/
private noncomputable def tf72Pc (w : ℂ) : ℂ :=
  ((4/3 : ℂ)/30) * (2 - (4/3 : ℂ)*w)^3 * (4 + 6*(4/3 : ℂ)*w + (4/3 : ℂ)^2*w^2)

/-- The complexification of `tf72poly (4/3)`. -/
private lemma tf72polyC_fourThirds (t : ℝ) : tf72polyC (4/3) t = tf72Pc (t : ℂ) := by
  simp only [tf72polyC, tf72poly, tf72Pc]
  push_cast
  ring

/-- The degree-five polynomial `W` (with coefficients depending on `z`) with `W' - z W = P`. -/
private noncomputable def tf72Q (z : ℂ) : Polynomial ℂ :=
  Polynomial.C ((16384/729 : ℂ)/z^6 - (1024/81 : ℂ)/z^4 + (512/81 : ℂ)/z^3 - (64/45 : ℂ)/z)
    + Polynomial.C ((16384/729 : ℂ)/z^5 - (1024/81 : ℂ)/z^3 + (512/81 : ℂ)/z^2) * Polynomial.X
    + Polynomial.C ((8192/729 : ℂ)/z^4 - (512/81 : ℂ)/z^2 + (256/81 : ℂ)/z) * Polynomial.X^2
    + Polynomial.C ((8192/2187 : ℂ)/z^3 - (512/243 : ℂ)/z) * Polynomial.X^3
    + Polynomial.C ((2048/2187 : ℂ)/z^2) * Polynomial.X^4
    + Polynomial.C ((2048/10935 : ℂ)/z) * Polynomial.X^5

private noncomputable def tf72W (z : ℂ) (w : ℂ) : ℂ := (tf72Q z).eval w

private noncomputable def tf72W' (z : ℂ) (w : ℂ) : ℂ := (tf72Q z).derivative.eval w

private lemma tf72W_hasDerivAt (z w : ℂ) : HasDerivAt (tf72W z) (tf72W' z w) w :=
  (tf72Q z).hasDerivAt w

private lemma tf72W_ident (z : ℂ) (hz : z ≠ 0) (w : ℂ) :
    tf72W' z w - z * tf72W z w = tf72Pc w := by
  simp only [tf72W, tf72W', tf72Q, tf72Pc]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_X_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_zero]
  field_simp
  ring

private lemma tf72W_at_zero (z : ℂ) :
    tf72W z 0 = (16384/729 : ℂ)/z^6 - (1024/81 : ℂ)/z^4 + (512/81 : ℂ)/z^3 - (64/45 : ℂ)/z := by
  simp only [tf72W, tf72Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

private lemma tf72W_at_b (z : ℂ) :
    tf72W z (3/2) = (1024/81 : ℂ)/z^4 + (8192/243 : ℂ)/z^5 + (16384/729 : ℂ)/z^6 := by
  simp only [tf72W, tf72Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem Tf72FcClosed (z : ℂ) (hz : z ≠ 0) :
    Work.ZeroFreeTables.tf72Fc (4/3) z =
      (64/45)/z - (512/81)/z^3 + (1024/81)/z^4 - (16384/729)/z^6
        + Complex.exp (-(3*z/2)) * ((1024/81)/z^4 + (8192/243)/z^5 + (16384/729)/z^6) := by
  have h23 : (2:ℝ)/(4/3) = 3/2 := by norm_num
  have hb : (0:ℝ) ≤ 3/2 := by norm_num
  -- Step 1: replace `tf72f` by the polynomial representative on the interval of integration
  have hcongr : tf72Fc (4/3) z
      = ∫ t in (0:ℝ)..(3/2), Complex.exp (-(z * (t:ℂ))) * tf72polyC (4/3) t := by
    unfold tf72Fc
    rw [h23]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hb] at ht
    have ht' : t ∈ Set.Icc (0:ℝ) (2/(4/3)) := by rw [h23]; exact ht
    simp only [tf72f_eq_tf72poly (4/3) (by norm_num) t ht', tf72polyC]
  -- Step 2: the primitive `t ↦ e^{-zt} W(t)`
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Complex.exp (-(z * (s:ℂ))) * tf72W z (s:ℂ))
        (Complex.exp (-(z * (t:ℂ))) * tf72polyC (4/3) t) t := by
    intro t
    have hlin1 : HasDerivAt (fun s : ℂ => s * (-z)) (-z) (t:ℂ) := hasDerivAt_mul_const (-z)
    have hlin : HasDerivAt (fun s : ℂ => -(z * s)) (-z) (t:ℂ) := by
      have he : (fun s : ℂ => s * (-z)) = fun s : ℂ => -(z * s) := by funext s; ring
      rw [he] at hlin1
      exact hlin1
    have hexpC : HasDerivAt (fun s : ℂ => Complex.exp (-(z * s)))
        (Complex.exp (-(z * (t:ℂ))) * (-z)) (t:ℂ) :=
      HasDerivAt.comp (t:ℂ) (Complex.hasDerivAt_exp (-(z * (t:ℂ)))) hlin
    have hexpR : HasDerivAt (fun s : ℝ => Complex.exp (-(z * (s:ℂ))))
        (Complex.exp (-(z * (t:ℂ))) * (-z)) t := hexpC.comp_ofReal
    have hWR : HasDerivAt (fun s : ℝ => tf72W z (s:ℂ)) (tf72W' z (t:ℂ)) t :=
      (tf72W_hasDerivAt z (t:ℂ)).comp_ofReal
    refine (hexpR.mul hWR).congr_deriv ?_
    rw [tf72polyC_fourThirds t, ← tf72W_ident z hz (t:ℂ)]
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z * (t:ℂ))) * tf72polyC (4/3) t) volume (0:ℝ) (3/2) :=
    (((Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).mul
      (tf72polyC_cont (4/3)))).intervalIntegrable (0:ℝ) (3/2)
  have hFTOC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  rw [hcongr, hFTOC]
  -- Step 3: evaluate the boundary values
  have hF0 : Complex.exp (-(z * (((0:ℝ)):ℂ))) * tf72W z (((0:ℝ)):ℂ)
      = (16384/729 : ℂ)/z^6 - (1024/81 : ℂ)/z^4 + (512/81 : ℂ)/z^3 - (64/45 : ℂ)/z := by
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
    exact tf72W_at_zero z
  have hcast : ((((3:ℝ)/2 : ℝ)) : ℂ) = (3/2 : ℂ) := by push_cast; ring
  have harg : -(z * ((((3:ℝ)/2 : ℝ)) : ℂ)) = -(3*z/2) := by
    rw [hcast]; ring
  have hFb : Complex.exp (-(z * ((((3:ℝ)/2 : ℝ)) : ℂ))) * tf72W z ((((3:ℝ)/2 : ℝ)) : ℂ)
      = Complex.exp (-(3*z/2))
        * ((1024/81 : ℂ)/z^4 + (8192/243 : ℂ)/z^5 + (16384/729 : ℂ)/z^6) := by
    rw [harg, hcast, tf72W_at_b z]
  change Complex.exp (-(z * ((((3:ℝ)/2 : ℝ)) : ℂ))) * tf72W z ((((3:ℝ)/2 : ℝ)) : ℂ)
      - Complex.exp (-(z * ((0:ℝ):ℂ))) * tf72W z ((0:ℝ):ℂ)
      = (64/45)/z - (512/81)/z^3 + (1024/81)/z^4 - (16384/729)/z^6
        + Complex.exp (-(3*z/2)) * ((1024/81)/z^4 + (8192/243)/z^5 + (16384/729)/z^6)
  rw [hFb, hF0]
  ring

end Work.ZeroFreeTables.XY
