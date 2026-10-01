/-
# ZeroFreeTables — tf72Phi_defs

The `λ`-free form of the Laplace transform of HB Lemma 7.2's optimal test
function, together with the moment function `tf72M` and the two rational
approximants `tf72PhiUB`, `tf72PhiLB` used by the Table-10 region certificates.

With `f_λ` the test function of HB Lemma 7.2 (support `[0, 2/λ]`, `f_λ(t) =
(λ/30)(2-λt)³(4+6λt+λ²t²)`) and `F_λ` its Laplace transform on the real axis,
the substitution `t = s/λ` gives

  `F_λ z = tf72Phi (z/λ)`,  `tf72Phi w = (1/30)∫₀² e^{-ws}(2-s)³(4+6s+s²) ds`.

Plainly `tf72Phi 0 = 8/9` and `tf72Phi` is antitone.  The Taylor expansion
`e^{±ws} = Σ_m (±ws)^m/m!` with `∫₀² s^m (2-s)³(4+6s+s²) ds = tf72M m` gives the
rational upper/lower approximants `tf72PhiUB`, `tf72PhiLB` (proved to bound
`tf72Phi` in `tf72Phi_bounds`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.tf72Fc_zero_re
import Submission.Work.ZeroFreeTables.tf72f_moment

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

/-- The polynomial body of HB Lemma 7.2's test function after the substitution
`t = s/λ`: `(2-s)³(4+6s+s²)`. -/
def tf72Body (s : ℝ) : ℝ := (2 - s) ^ 3 * (4 + 6 * s + s ^ 2)

/-- `F_λ z = tf72Phi (z/λ)`: the `λ`-free form of the Laplace transform of the
test function of HB Lemma 7.2. -/
def tf72Phi (w : ℝ) : ℝ :=
  (1/30) * ∫ s in (0:ℝ)..2, Real.exp (-(w * s)) * tf72Body s

/-- `F_λ` of HB Lemma 7.2's test function equals `tf72Phi ∘ (·/λ)`. -/
theorem tf72F_eq_Phi (lam : ℝ) (hl : 0 < lam) (z : ℝ) :
    (tf72T lam hl).F z = tf72Phi (z / lam) := by
  rw [TestFn_F_eq_integral]
  show (∫ t in (0:ℝ)..(2/lam), Real.exp (-(z * t)) * tf72f lam t) = tf72Phi (z/lam)
  have hpoly : (∫ t in (0:ℝ)..(2/lam), Real.exp (-(z * t)) * tf72f lam t)
      = ∫ t in (0:ℝ)..(2/lam),
          Real.exp (-(z * t)) * ((lam/30) * ((2 - lam*t)^3 * (4 + 6*(lam*t) + (lam*t)^2))) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 2/lam)] at ht
    rw [tf72f_eq_poly lam hl t ht]
    ring
  rw [hpoly]
  have hcongr : (∫ t in (0:ℝ)..(2/lam),
        Real.exp (-(z * t)) * ((lam/30) * ((2 - lam*t)^3 * (4 + 6*(lam*t) + (lam*t)^2))))
      = ∫ t in (0:ℝ)..(2/lam),
          (fun u : ℝ => Real.exp (-((z/lam) * u)) *
              ((lam/30) * ((2 - u)^3 * (4 + 6*u + u^2)))) (lam * t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only
    rw [show -(z * t) = -((z/lam) * (lam * t)) by field_simp]
  rw [hcongr]
  rw [intervalIntegral.integral_comp_mul_left
        (fun u : ℝ => Real.exp (-((z/lam) * u)) * ((lam/30) * ((2 - u)^3 * (4 + 6*u + u^2))))
        hl.ne']
  rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul]
  rw [tf72Phi]
  have hfac : (∫ u in (0:ℝ)..2, Real.exp (-((z/lam) * u)) *
        ((lam/30) * ((2 - u)^3 * (4 + 6*u + u^2))))
      = (lam/30) * ∫ u in (0:ℝ)..2, Real.exp (-((z/lam) * u)) * tf72Body u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [tf72Body]; ring
  rw [hfac]
  field_simp

/-- `tf72Phi 0 = 8/9`. -/
theorem tf72Phi_zero : tf72Phi 0 = 8 / 9 := by
  rw [tf72Phi]
  have h : (∫ s in (0:ℝ)..2, Real.exp (-((0:ℝ) * s)) * tf72Body s)
      = ∫ s in (0:ℝ)..2, tf72Body s := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp
  rw [h, show tf72Body = fun s : ℝ => (2 - s)^3 * (4 + 6*s + s^2) from rfl]
  rw [tf72_poly_integral]
  norm_num

/-- `tf72Phi` is antitone (the Laplace transform of a non-negative function on
the real axis is non-increasing). -/
theorem tf72Phi_antitone : Antitone tf72Phi := by
  intro x y hxy
  rw [tf72Phi]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/30)
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 2)
  · exact ((by unfold tf72Body; fun_prop : Continuous (fun s : ℝ => Real.exp (-(y * s)) * tf72Body s))).intervalIntegrable 0 2
  · exact ((by unfold tf72Body; fun_prop : Continuous (fun s : ℝ => Real.exp (-(x * s)) * tf72Body s))).intervalIntegrable 0 2
  · intro s hs
    rw [Set.mem_Icc] at hs
    have hs0 : 0 ≤ s := hs.1
    have hbody : 0 ≤ tf72Body s := by
      rw [tf72Body]
      have h1 : 0 ≤ (2 - s)^3 := by
        have : 0 ≤ 2 - s := by linarith [hs.2]
        positivity
      have h2 : 0 ≤ 4 + 6*s + s^2 := by nlinarith [sq_nonneg (s + 3)]
      positivity
    apply mul_le_mul_of_nonneg_right _ hbody
    apply Real.exp_le_exp.mpr
    nlinarith

/-- The moments `∫₀² s^m (2-s)³(4+6s+s²) ds` in closed form. -/
def tf72M (m : ℕ) : ℝ :=
  32 * (2:ℝ)^(m+1) / ((m:ℝ) + 1) - 40 * (2:ℝ)^(m+3) / ((m:ℝ) + 3)
    + 20 * (2:ℝ)^(m+4) / ((m:ℝ) + 4) - (2:ℝ)^(m+6) / ((m:ℝ) + 6)

/-- `tf72M m` is the `m`-th moment of the polynomial body on `[0,2]`. -/
theorem tf72M_eq_integral (m : ℕ) :
    (∫ s in (0:ℝ)..2, s^m * tf72Body s) = tf72M m := by
  have h : (∫ s in (0:ℝ)..2, s^m * tf72Body s)
      = ∫ s in (0:ℝ)..2, s^m * (32 + (-40)*s^2 + 20*s^3 + (-1)*s^5) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    congr 1
    rw [tf72Body]
    ring
  rw [h, tf72f_moment_lin]
  simp only [tf72M]
  ring

/-- Rational upper approximant of `tf72Phi (-x)`: the degree-`9` Taylor sum of
`e^{xs}` plus the two-sided remainder `2(xs)^9/9!`. -/
def tf72PhiUB (x : ℝ) : ℝ :=
  (1/30) * ((∑ m ∈ Finset.range 9, x^m * tf72M m / (m.factorial : ℝ))
    + 2 * x^9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ))

/-- Rational lower approximant of `tf72Phi y`. -/
def tf72PhiLB (y : ℝ) : ℝ :=
  (1/30) * ((∑ m ∈ Finset.range 9, (-y)^m * tf72M m / (m.factorial : ℝ))
    - 2 * y^9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ))

/-- Rational lower approximant of `tf72Phi (-x)` (`x ≥ 0`): the degree-`8`
Taylor sum of the everywhere-positive series `Σ_m (xs)^m/m!`, so no remainder
term is needed. -/
def tf72PhiLBneg (x : ℝ) : ℝ :=
  (1/30) * (∑ m ∈ Finset.range 9, x^m * tf72M m / (m.factorial : ℝ))

/-- Rational upper approximant of `tf72Phi y` (`y ≥ 0`): the alternating
degree-`8` Taylor sum plus the two-sided remainder `2 (ys)^9/9!`. -/
def tf72PhiUBpos (y : ℝ) : ℝ :=
  (1/30) * ((∑ m ∈ Finset.range 9, (-y)^m * tf72M m / (m.factorial : ℝ))
    + 2 * y^9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ))

end Work.ZeroFreeTables
