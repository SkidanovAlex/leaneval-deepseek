/-
# ZeroFreeTables/XY/SupYcTaylor

Upper bound for the oscillatory integral

  `Yc t = ∫_0^{3/2} x · cos(t x) · f(x) dx`   (`f = xyFf = tf72f (4/3)`),

namely `Yc t ≤ 12/35 - t²/14 + 9 t⁴/2112` for `|t| ≤ 3`.

On the support `[0, 3/2]` the test function `f` is the quintic `xyP`, whose moments
`xyM j = ∫_0^{3/2} x^j xyP x` are evaluated in `xyMainLt` (`xyP_moment`).  Since
`x ↦ x · xyP x` is non-negative on `[0, 3/2]`, integrating the pointwise Taylor bound

  `cos u ≤ 1 - u²/2 + u⁴/24`

gives the result, with the three coefficients `12/35`, `1/14`, `9/2112` coming from
`xyM 1 = 12/35`, `xyM 3 = 1/7`, `xyM 5 = 9/88`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData
import Submission.Work.ZeroFreeTables.XY.xyMainLt

open MeasureTheory intervalIntegral
noncomputable section
namespace Work.ZeroFreeTables.XY

/-- The degree-4 Taylor bound for `cos`: `cos y ≤ 1 - y²/2 + y⁴/24` whenever
`|y| ≤ 9/2`.  (Obtained from `sin u ≥ u - u³/6` at `u = y/2`, where the right-hand
side of that bound is non-negative.) -/
private lemma cos_le_taylor4_local (y : ℝ) (hy : |y| ≤ 9/2) :
    Real.cos y ≤ 1 - y^2/2 + y^4/24 := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 9/2 → Real.cos y ≤ 1 - y^2/2 + y^4/24 := by
    intro y hy0 hy
    have hu0 : 0 ≤ y/2 := by linarith
    have hu : y/2 ≤ 9/4 := by linarith
    have hsin : y/2 - (y/2)^3/6 ≤ Real.sin (y/2) := Real.sin_ge_sub_cube hu0
    have hnn : 0 ≤ y/2 - (y/2)^3/6 := by nlinarith [hu0, hu, sq_nonneg (y/2)]
    have hsinsq : (y/2 - (y/2)^3/6)^2 ≤ Real.sin (y/2)^2 := pow_le_pow_left₀ hnn hsin 2
    have hcos : Real.cos y = 1 - 2*Real.sin (y/2)^2 := by
      have h2 : y = 2*(y/2) := by ring
      conv_lhs => rw [h2]
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (y/2)]
    rw [hcos]
    have h6 : 0 ≤ (y/2)^6 := pow_nonneg hu0 6
    nlinarith [hsinsq, h6]
  rcases le_total 0 y with hy0 | hy0
  · exact key y hy0 (by linarith [(abs_le.mp hy).2])
  · have h := key (-y) (by linarith) (by have h' := (abs_le.mp hy).1; linarith)
    have e1 : (-y)^2 = y^2 := by ring
    have e2 : (-y)^4 = y^4 := by ring
    rw [Real.cos_neg, e1, e2] at h
    exact h

/-- `x ↦ x · cos(tx) · xyP x` is continuous. -/
private lemma cont_cos_xyP (t : ℝ) : Continuous (fun x : ℝ => x * Real.cos (t*x) * xyP x) := by
  have h : Continuous (fun x : ℝ => x * Real.cos (t*x) *
      ((64:ℝ)/45 - (256/81)*x^2 + (512/243)*x^3 - (2048/10935)*x^5)) := by fun_prop
  exact h.congr (fun x => by simp only [xyP])

/-- `x ↦ x · (1 - (tx)²/2 + (tx)⁴/24) · xyP x` is continuous. -/
private lemma cont_poly_xyP (t : ℝ) :
    Continuous (fun x : ℝ => x * (1 - (t*x)^2/2 + (t*x)^4/24) * xyP x) := by
  have h : Continuous (fun x : ℝ => x * (1 - (t*x)^2/2 + (t*x)^4/24) *
      ((64:ℝ)/45 - (256/81)*x^2 + (512/243)*x^3 - (2048/10935)*x^5)) := by fun_prop
  exact h.congr (fun x => by simp only [xyP])

/-- `x ↦ x^k · xyP x` is continuous. -/
private lemma cont_kP (k : ℕ) : Continuous (fun x : ℝ => x^k * xyP x) := by
  have h : Continuous (fun x : ℝ => x^k *
      ((64:ℝ)/45 - (256/81)*x^2 + (512/243)*x^3 - (2048/10935)*x^5)) := by fun_prop
  exact h.congr (fun x => by simp only [xyP])

/-- The integral of the degree-4 Taylor polynomial of `cos` against `x · xyP x`. -/
private lemma integral_taylor_poly (t : ℝ) :
    ∫ x in (0:ℝ)..(3/2), x * (1 - (t*x)^2/2 + (t*x)^4/24) * xyP x
      = 12/35 - t^2/14 + 9*t^4/2112 := by
  have hcongr : (∫ x in (0:ℝ)..(3/2), x * (1 - (t*x)^2/2 + (t*x)^4/24) * xyP x)
      = ∫ x in (0:ℝ)..(3/2),
          (x^1 * xyP x - (t^2/2) * (x^3 * xyP x) + (t^4/24) * (x^5 * xyP x)) := by
    apply intervalIntegral.integral_congr
    intro x hx; ring
  have hInt1 : IntervalIntegrable (fun x : ℝ => x^1 * xyP x) volume (0:ℝ) (3/2) :=
    (cont_kP 1).intervalIntegrable (0:ℝ) (3/2)
  have hInt3 : IntervalIntegrable (fun x : ℝ => x^3 * xyP x) volume (0:ℝ) (3/2) :=
    (cont_kP 3).intervalIntegrable (0:ℝ) (3/2)
  have hInt5 : IntervalIntegrable (fun x : ℝ => x^5 * xyP x) volume (0:ℝ) (3/2) :=
    (cont_kP 5).intervalIntegrable (0:ℝ) (3/2)
  have hc3 : Continuous (fun x : ℝ => (t^2/2) * (x^3 * xyP x)) := (cont_kP 3).const_mul (t^2/2)
  have hc5 : Continuous (fun x : ℝ => (t^4/24) * (x^5 * xyP x)) := (cont_kP 5).const_mul (t^4/24)
  have hIntc3 : IntervalIntegrable (fun x : ℝ => (t^2/2) * (x^3 * xyP x)) volume (0:ℝ) (3/2) :=
    hc3.intervalIntegrable (0:ℝ) (3/2)
  have hIntc5 : IntervalIntegrable (fun x : ℝ => (t^4/24) * (x^5 * xyP x)) volume (0:ℝ) (3/2) :=
    hc5.intervalIntegrable (0:ℝ) (3/2)
  have hlin : (∫ x in (0:ℝ)..(3/2),
        (x^1 * xyP x - (t^2/2) * (x^3 * xyP x) + (t^4/24) * (x^5 * xyP x)))
      = (∫ x in (0:ℝ)..(3/2), (x^1 * xyP x - (t^2/2) * (x^3 * xyP x)))
        + (∫ x in (0:ℝ)..(3/2), (t^4/24) * (x^5 * xyP x)) :=
    intervalIntegral.integral_add (hInt1.sub hIntc3) hIntc5
  have hlinA : (∫ x in (0:ℝ)..(3/2), (x^1 * xyP x - (t^2/2) * (x^3 * xyP x)))
      = (∫ x in (0:ℝ)..(3/2), x^1 * xyP x)
        - (∫ x in (0:ℝ)..(3/2), (t^2/2) * (x^3 * xyP x)) :=
    intervalIntegral.integral_sub hInt1 hIntc3
  have hcm3 : (∫ x in (0:ℝ)..(3/2), (t^2/2) * (x^3 * xyP x))
      = (t^2/2) * (∫ x in (0:ℝ)..(3/2), x^3 * xyP x) :=
    intervalIntegral.integral_const_mul (t^2/2) (fun x : ℝ => x^3 * xyP x)
  have hcm5 : (∫ x in (0:ℝ)..(3/2), (t^4/24) * (x^5 * xyP x))
      = (t^4/24) * (∫ x in (0:ℝ)..(3/2), x^5 * xyP x) :=
    intervalIntegral.integral_const_mul (t^4/24) (fun x : ℝ => x^5 * xyP x)
  have h1 : ∫ x in (0:ℝ)..(3/2), x^1 * xyP x = xyM 1 := xyP_moment 1
  have h3 : ∫ x in (0:ℝ)..(3/2), x^3 * xyP x = xyM 3 := xyP_moment 3
  have h5 : ∫ x in (0:ℝ)..(3/2), x^5 * xyP x = xyM 5 := xyP_moment 5
  rw [hcongr, hlin, hlinA, hcm3, hcm5, h1, h3, h5]
  norm_num [xyM]
  ring

theorem SupYcTaylor (t : ℝ) (h : |t| ≤ 3) :
    Work.ZeroFreeTables.XY.Yc t ≤ 12/35 - t^2/14 + 9*t^4/2112 := by
  have hYc : Yc t = ∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyP x := by
    change (∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyFf x)
        = (∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyP x)
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0:ℝ) (3/2) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at hx; exact hx
    have hxy : xyFf x = xyP x := by rw [xyFf]; exact tf72f43_eq x hx'
    simp only [hxy]
  rw [hYc]
  have hmono : ∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyP x
      ≤ ∫ x in (0:ℝ)..(3/2), x * (1 - (t*x)^2/2 + (t*x)^4/24) * xyP x := by
    have hintA : IntervalIntegrable (fun x : ℝ => x * Real.cos (t*x) * xyP x) volume (0:ℝ) (3/2) :=
      (cont_cos_xyP t).intervalIntegrable (0:ℝ) (3/2)
    have hintB :
        IntervalIntegrable (fun x : ℝ => x * (1 - (t*x)^2/2 + (t*x)^4/24) * xyP x) volume (0:ℝ) (3/2) :=
      (cont_poly_xyP t).intervalIntegrable (0:ℝ) (3/2)
    apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 3/2)
    · exact hintA
    · exact hintB
    · intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx15 : x ≤ 3/2 := hx.2
      have htx : |t*x| ≤ 9/2 := by
        rw [abs_mul, abs_of_nonneg hx0]
        nlinarith [abs_nonneg t, hx15, h]
      have hcos : Real.cos (t*x) ≤ 1 - (t*x)^2/2 + (t*x)^4/24 := cos_le_taylor4_local (t*x) htx
      have hxnn : 0 ≤ x * xyP x := mul_nonneg hx0 (xyP_nonneg x hx0 hx15)
      have e1 : x * Real.cos (t*x) * xyP x = (x*xyP x) * Real.cos (t*x) := by ring
      have e2 : x * (1 - (t*x)^2/2 + (t*x)^4/24) * xyP x
          = (x*xyP x) * (1 - (t*x)^2/2 + (t*x)^4/24) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hcos hxnn
  calc ∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyP x
      ≤ ∫ x in (0:ℝ)..(3/2), x * (1 - (t*x)^2/2 + (t*x)^4/24) * xyP x := hmono
    _ = 12/35 - t^2/14 + 9*t^4/2112 := integral_taylor_poly t

end Work.ZeroFreeTables.XY
