import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddCurve.LowSlope.radial_derivs_le_of_profile
import Submission.Work.OddVolterra.Free.rhoRelationsLocal
import Submission.Work.OddVolterra.Free.semicircleDeriv2Close
import Submission.Work.OddVolterra.Free.profileLeOneAddAbs

set_option maxHeartbeats 1600000

namespace Work.OddVolterra.Free

open Set Filter
open scoped Topology ContDiff

noncomputable section

/-! ## Two elementary absolute-value helpers -/

private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  simpa only [abs_neg, sub_eq_add_neg] using h

/-! ## An elementary consequence of `|A - s| ≤ ν` -/

/-- If `a * S = A`, `a ^ 2 - 1 = A ^ 2 - s ^ 2`, `A + s ≤ a + 1`, `A > 0`, `0 < a` and
`|A - s| ≤ ν`, then `|a - 1| ≤ ν`. -/
private lemma abs_sub_one_le_of_sq {a ν A s : ℝ} (ha : 0 < a) (hA : 0 < A) (hs : 0 ≤ s)
    (hkey : a ^ 2 - 1 = A ^ 2 - s ^ 2) (hclose : |A - s| ≤ ν)
    (hle : A + s ≤ a + 1) (hν : 0 ≤ ν) : |a - 1| ≤ ν := by
  have hAs : 0 < A + s := by linarith
  have ha1 : 0 < a + 1 := by linarith
  have h2 : |a - 1| * (a + 1) = |A - s| * (A + s) := by
    have h1 : |(a - 1) * (a + 1)| = |A - s| * (A + s) := by
      have h3 : (a - 1) * (a + 1) = (A - s) * (A + s) := by
        have e1 : (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
        have e2 : (A - s) * (A + s) = A ^ 2 - s ^ 2 := by ring
        rw [e1, e2, hkey]
      rw [h3, abs_mul, abs_of_pos hAs]
    rwa [abs_mul, abs_of_pos ha1] at h1
  have h3 : |A - s| * (A + s) ≤ ν * (a + 1) := by
    calc |A - s| * (A + s) ≤ ν * (A + s) := mul_le_mul_of_nonneg_right hclose hAs.le
      _ ≤ ν * (a + 1) := mul_le_mul_of_nonneg_left hle hν
  rw [← h2] at h3
  nlinarith only [h3, ha]

/-! ## The pure arithmetic core -/

/-- **Arithmetic core.**  Under the two relations coming from the radial identity and the
pointwise closeness of `A, A', A''` to the semicircle profile and its first two derivatives at
the shadow `a * u`, the radial data `a = ρ u`, `b = ρ' u`, `c = ρ'' u` are bounded by the relevant
polynomials in `ν`. -/
theorem radialBoundCore {u ν a b c A A' A'' : ℝ}
    (hν : 0 ≤ ν) (hu : |u| < 4 / 5) (ha : 0 < a) (hA : 0 < A) (hx : |a * u| ≤ 17 / 20)
    (hAle : A ≤ 1 + |a * u|)
    (hSA : a * Real.sqrt (1 - u ^ 2) = A)
    (hAclose : |A - Real.sqrt (1 - (a * u) ^ 2)| ≤ ν)
    (hA'close : |A' + (a * u) / Real.sqrt (1 - (a * u) ^ 2)| ≤ ν)
    (hA''close : |A'' + 1 / (Real.sqrt (1 - (a * u) ^ 2)) ^ 3| ≤ ν)
    (hspread : |1 / (Real.sqrt (1 - (a * u) ^ 2)) ^ 3 - 1 / (Real.sqrt (1 - u ^ 2)) ^ 3|
      ≤ 300 * (ν + ν ^ 2))
    (hsign : (0 < u → A' ≤ 0) ∧ (u < 0 → 0 ≤ A'))
    (hE2 : b * (A * (A - (a * u) * A')) = a ^ 2 * (a * u + A * A'))
    (hE3 : c * (A - (a * u) * A') =
        a * (2 * b * u / Real.sqrt (1 - u ^ 2) + a / (Real.sqrt (1 - u ^ 2)) ^ 3 +
          A'' * (b * u + a) ^ 2 + 2 * A' * b)) :
    |a - 1| ≤ 10 ^ 6 * (ν + ν ^ 2) ∧
      |b| ≤ 10 ^ 6 * (ν + ν ^ 2 + ν ^ 3) ∧
      |c| ≤ 10 ^ 6 * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) := by
  set x : ℝ := a * u with hxdef
  set S : ℝ := Real.sqrt (1 - u ^ 2) with hSdef
  set s : ℝ := Real.sqrt (1 - x ^ 2) with hsdef
  set K : ℝ := 2 * b * u / S + a / S ^ 3 + A'' * (b * u + a) ^ 2 + 2 * A' * b with hKdef
  have hu2 : 0 < 1 - u ^ 2 := by have h := abs_lt.mp hu; nlinarith only [h.1, h.2]
  have hx2 : 0 < 1 - x ^ 2 := by have h := abs_le.mp hx; nlinarith only [h.1, h.2]
  have hSsq : S ^ 2 = 1 - u ^ 2 := by rw [hSdef]; exact Real.sq_sqrt (le_of_lt hu2)
  have hssq : s ^ 2 = 1 - x ^ 2 := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt hx2)
  have hSpos : 0 < S := by rw [hSdef]; exact Real.sqrt_pos.2 hu2
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hx2
  have hSge : (3 : ℝ) / 5 ≤ S := by
    rw [hSdef, Real.le_sqrt (by norm_num) (le_of_lt hu2)]
    have h := abs_lt.mp hu
    nlinarith only [h.1, h.2]
  have hsge : (1 : ℝ) / 2 ≤ s := by
    rw [hsdef, Real.le_sqrt (by norm_num) (le_of_lt hx2)]
    have h := abs_le.mp hx
    nlinarith only [h.1, h.2]
  have hSle : S ≤ 1 := by
    rw [hSdef, Real.sqrt_le_one]
    nlinarith only [sq_nonneg u]
  have hsle : s ≤ 1 := by
    rw [hsdef, Real.sqrt_le_one]
    nlinarith only [sq_nonneg x]
  have hxlt : |x| < 1 := by
    have h := abs_le.mp hx
    rw [abs_lt]; constructor <;> linarith only [h.1, h.2]
  have hsignu : 0 ≤ -u * A' := by
    rcases lt_trichotomy u 0 with h | h | h
    · have h2 := hsign.2 h; nlinarith only [h, h2]
    · rw [h]; simp
    · have h2 := hsign.1 h; nlinarith only [h, h2]
  -- STEP 1: |a - 1| ≤ ν
  have hAeq : A = a * S := hSA.symm
  have ha1 : |a - 1| ≤ ν := by
    have hkey : (a - 1) * (a + 1) = (A - s) * (A + s) := by
      have h1 : a ^ 2 - 1 = A ^ 2 - s ^ 2 := by
        rw [← hSA, mul_pow, hSsq, hssq, hxdef]
        ring
      have e1 : (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      have e2 : (A - s) * (A + s) = A ^ 2 - s ^ 2 := by ring
      rw [e1, e2, h1]
    have h2 : |a - 1| * (a + 1) = |A - s| * (A + s) := by
      have h1 : |(a - 1) * (a + 1)| = |A - s| * (A + s) := by
        rw [hkey, abs_mul, abs_of_pos (by linarith only [hA, hspos] : (0:ℝ) < A + s)]
      rwa [abs_mul, abs_of_pos (by linarith only [ha] : (0:ℝ) < a + 1)] at h1
    have h3 : |A - s| * (A + s) ≤ ν * (a + 1) := by
      have h4 : |A - s| ≤ ν := hAclose
      have h5 : A + s ≤ a + 1 := by
        have h6 : A ≤ a := by nlinarith only [hAeq, hSle, ha]
        linarith only [h6, hsle]
      calc |A - s| * (A + s) ≤ ν * (A + s) :=
            mul_le_mul_of_nonneg_right h4 (by linarith only [hA, hspos])
        _ ≤ ν * (a + 1) := mul_le_mul_of_nonneg_left h5 hν
    rw [← h2] at h3
    nlinarith only [h3, ha]
  -- STEP 2: a ≤ 10/3
  have haub : a ≤ 10 / 3 := by
    have h1 : A ≤ 37 / 20 := by linarith only [hAle, hx]
    have h3 : a * (3/5) ≤ a * S := mul_le_mul_of_nonneg_left hSge ha.le
    nlinarith only [h1, h3, hAeq]
  -- division helpers
  have hdivS : ∀ X : ℝ, 0 ≤ X → X / S ≤ X * (5/3) := by
    intro X hX
    rw [div_le_iff₀ hSpos]
    nlinarith only [hSge, hX]
  have hdivS3 : ∀ X : ℝ, 0 ≤ X → X / S ^ 3 ≤ X * (125/27) := by
    intro X hX
    have hS3 : (0:ℝ) < S ^ 3 := by positivity
    rw [div_le_iff₀ hS3]
    have h27 : (27:ℝ)/125 ≤ S ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/5) hSge 3
      norm_num at h
      exact h
    nlinarith only [h27, hX]
  have hdivs : ∀ X : ℝ, 0 ≤ X → X / s ≤ X * 2 := by
    intro X hX
    rw [div_le_iff₀ hspos]
    nlinarith only [hsge, hX]
  -- STEP 3: |u + S * A'| ≤ 13/5 ν
  have hnum : |u + S * A'| ≤ 13 / 5 * ν := by
    have hsplit : u + S * A' = (u + S * (-x / s)) + S * (A' + x / s) := by
      have hsne : s ≠ 0 := ne_of_gt hspos
      field_simp
      ring
    rw [hsplit]
    have hb1 : |u + S * (-x / s)| ≤ 8 / 5 * ν := by
      have h1 : u + S * (-x / s) = u * (s - A) / s := by
        rw [hxdef, ← hSA]
        have hsne : s ≠ 0 := ne_of_gt hspos
        field_simp
        ring
      rw [h1, abs_div, abs_of_pos hspos]
      have h2 : |u * (s - A)| ≤ 4 / 5 * ν := by
        rw [abs_mul]
        have h3 : |s - A| ≤ ν := by rw [abs_sub_comm]; exact hAclose
        have hu4 : |u| ≤ 4 / 5 := le_of_lt hu
        nlinarith only [abs_nonneg u, abs_nonneg (s - A), hu4, h3]
      calc |u * (s - A)| / s ≤ (4/5*ν) / s := div_le_div_of_nonneg_right h2 hspos.le
        _ ≤ (4/5*ν) * 2 := hdivs (4/5*ν) (by positivity)
        _ = 8/5*ν := by ring
    have hb2 : |S * (A' + x / s)| ≤ ν := by
      rw [abs_mul, abs_of_pos hSpos]
      calc S * |A' + x / s| ≤ S * ν := mul_le_mul_of_nonneg_left hA'close hSpos.le
        _ ≤ ν := by nlinarith only [hSle, hν]
    calc |(u + S*(-x/s)) + S*(A' + x/s)| ≤ |u + S*(-x/s)| + |S*(A' + x/s)| := abs_add_le _ _
      _ ≤ 8/5*ν + ν := by linarith only [hb1, hb2]
      _ = 13/5*ν := by ring
  -- STEP 4: hE2 in normalised form
  have hE2' : b * (S * (S - u * A')) = a * (u + S * A') := by
    have h := hE2
    rw [hxdef] at h
    rw [← hSA] at h
    have h5 : a ^ 2 * (b * (S * (S - u * A'))) = a ^ 2 * (a * (u + S * A')) := by
      have h3 : a ^ 2 * (b * (S * (S - u * A'))) = b * (a * S * (a * S - a * u * A')) := by ring
      have h4 : a ^ 2 * (a * (u + S * A')) = a ^ 2 * (a * u + a * S * A') := by ring
      rw [h3, h4]
      exact h
    exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt ha)) h5
  -- STEP 5: |b| ≤ 25 ν
  have hb25 : |b| ≤ 25 * ν := by
    have hD2 : 0 < S - u * A' := by linarith only [hSge, hsignu]
    have hbabs : |b| * (S * (S - u * A')) = a * |u + S * A'| := by
      have h := congrArg (fun t : ℝ => |t|) hE2'
      rw [abs_mul, abs_mul, abs_of_pos hSpos, abs_of_pos hD2, abs_mul, abs_of_pos ha] at h
      exact h
    have h3 : (9 : ℝ) / 25 ≤ S * (S - u * A') := by
      have h2 : S ≤ S - u * A' := by linarith only [hsignu]
      nlinarith only [hSge, h2]
    have h5 : a * |u + S * A'| ≤ a * (13/5 * ν) := mul_le_mul_of_nonneg_left hnum ha.le
    have h6 : a * (13/5 * ν) ≤ 10/3 * (13/5*ν) := mul_le_mul_of_nonneg_right haub (by positivity)
    have h7 : |b| * (9/25) ≤ |b| * (S*(S - u*A')) := mul_le_mul_of_nonneg_left h3 (abs_nonneg b)
    have h8 : |b| * (9/25) ≤ (10/3)*(13/5)*ν := by linarith only [h7, hbabs, h5, h6]
    have h9 : (25/9) * (|b| * (9/25)) ≤ (25/9) * ((10/3)*(13/5)*ν) :=
      mul_le_mul_of_nonneg_left h8 (by norm_num)
    have e : (25:ℝ)/9 * (|b| * (9/25)) = |b| := by ring
    rw [e] at h9
    linarith only [h9, hν]
  -- STEP 6: auxiliary bounds
  have hxs : |x / s| ≤ 17 / 10 := by
    rw [abs_div, abs_of_pos hspos]
    have h1 : |x| / s ≤ (17/20) / s := div_le_div_of_nonneg_right hx hspos.le
    have h2 : (17/20) / s ≤ (17/20) * 2 := hdivs (17/20) (by norm_num)
    linarith only [h1, h2]
  have hA'abs : |A'| ≤ 2 + ν := by
    have h1 : |A'| ≤ |A' + x / s| + |x / s| := by
      have h2 : (A' + x / s) - (x / s) = A' := by ring
      simpa only [h2] using abs_sub_le_abs_add (A' + x / s) (x / s)
    linarith only [h1, hA'close, hxs]
  have hbu : |b * u| ≤ 20 * ν := by
    rw [abs_mul]
    have hu4 : |u| ≤ 4 / 5 := le_of_lt hu
    nlinarith only [hb25, hu4, abs_nonneg b, abs_nonneg u, hν]
  have hsq1 : |(b * u + a) ^ 2 - 1| ≤ 21 * ν * (20 * ν + 13 / 3) := by
    have h1 : (b*u+a)^2 - 1 = (b*u + a - 1) * (b*u + a + 1) := by ring
    rw [h1, abs_mul]
    have h2 : |b*u + a - 1| ≤ 21 * ν := by
      have h3 : b*u + a - 1 = b*u + (a-1) := by ring
      rw [h3]
      linarith only [abs_add_le (b*u) (a-1), hbu, ha1]
    have h4 : |b*u + a + 1| ≤ 20 * ν + 13/3 := by
      have h5 : |a + 1| ≤ 13/3 := by
        rw [abs_of_pos (by linarith only [ha] : (0:ℝ) < a + 1)]
        linarith only [haub]
      have h8 : b*u + a + 1 = b*u + (a+1) := by ring
      rw [h8]
      linarith only [abs_add_le (b*u) (a+1), hbu, h5]
    have h6 : 0 ≤ 21 * ν := by linarith only [hν]
    have h7 : 0 ≤ 20*ν + 13/3 := by linarith only [hν]
    calc |b*u+a-1| * |b*u+a+1| ≤ (21*ν) * (20*ν + 13/3) :=
          mul_le_mul h2 h4 (abs_nonneg _) h6
      _ = 21 * ν * (20*ν + 13/3) := by ring
  have hApp : |A'' + 1 / S ^ 3| ≤ 301 * (ν + ν ^ 2) := by
    have h1 : A'' + 1/S^3 = (A'' + 1/s^3) - (1/s^3 - 1/S^3) := by ring
    rw [h1]
    have hab : |(A'' + 1/s^3) - (1/s^3 - 1/S^3)| ≤ |A'' + 1/s^3| + |1/s^3 - 1/S^3| :=
      abs_sub_le_abs_add _ _
    calc |(A'' + 1/s^3) - (1/s^3 - 1/S^3)| ≤ |A'' + 1/s^3| + |1/s^3 - 1/S^3| := hab
      _ ≤ ν + 300*(ν+ν^2) := add_le_add hA''close hspread
      _ ≤ 301*(ν+ν^2) := by nlinarith only [hν]
  have hA''abs : |A''| ≤ 8 + ν := by
    have h8 : (1:ℝ)/8 ≤ s ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hsge 3
      norm_num at h
      exact h
    have h1 : |1/s^3| ≤ 8 := by
      rw [abs_of_pos (by positivity : (0:ℝ) < 1/s^3)]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < s ^ 3)]
      nlinarith only [h8]
    have h2 : A'' = (A'' + 1/s^3) - 1/s^3 := by ring
    rw [h2]
    have h3 : |(A'' + 1/s^3) - 1/s^3| ≤ |A'' + 1/s^3| + |1/s^3| :=
      abs_sub_le_abs_add _ _
    linarith only [h3, hA''close, h1]
  -- STEP 7: the K bound
  have hKsplit : K = (a - 1) / S^3 + (A'' + 1/S^3) + A'' * ((b*u+a)^2 - 1) + 2*b*u/S + 2*A'*b := by
    rw [hKdef]; ring
  have hKb : |K| ≤ 4000 * (ν + ν^2 + ν^3) := by
    have hT1 : |2 * b * u / S| ≤ 67 * ν := by
      have h1 : |2 * b * u / S| = 2 * |b| * |u| / S := by
        rw [abs_div, abs_of_pos hSpos, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [h1]
      have hu4 : |u| ≤ 4 / 5 := le_of_lt hu
      have h2 : 2 * |b| * |u| ≤ 40 * ν :=
        by nlinarith only [hb25, hu4, abs_nonneg b, abs_nonneg u, hν]
      calc 2 * |b| * |u| / S ≤ (2 * |b| * |u|) * (5/3) := hdivS _ (by positivity)
        _ ≤ (5/3) * (40*ν) := by linarith only [h2]
        _ ≤ 67 * ν := by linarith only [hν]
    have hT2 : |(a - 1) / S^3| ≤ 5 * ν := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < S^3)]
      calc |a - 1| / S^3 ≤ |a - 1| * (125/27) := hdivS3 _ (abs_nonneg _)
        _ ≤ (125/27) * ν := by linarith only [ha1]
        _ ≤ 5 * ν := by linarith only [hν]
    have hT4 : |A'' * ((b*u+a)^2 - 1)| ≤ (8+ν) * (21*ν*(20*ν+13/3)) := by
      rw [abs_mul]
      exact mul_le_mul hA''abs hsq1 (abs_nonneg _) (by linarith only [hν])
    have hT5 : |2 * A' * b| ≤ 2 * (2+ν) * (25*ν) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      nlinarith only [hA'abs, hb25, abs_nonneg A', abs_nonneg b, hν]
    rw [hKsplit]
    calc |(a-1)/S^3 + (A'' + 1/S^3) + A''*((b*u+a)^2-1) + 2*b*u/S + 2*A'*b|
        ≤ |(a-1)/S^3 + (A'' + 1/S^3) + A''*((b*u+a)^2-1) + 2*b*u/S| + |2*A'*b| := abs_add_le _ _
      _ ≤ (|(a-1)/S^3 + (A'' + 1/S^3) + A''*((b*u+a)^2-1)| + |2*b*u/S|) + |2*A'*b| := by
          linarith only [abs_add_le ((a-1)/S^3 + (A'' + 1/S^3) + A''*((b*u+a)^2-1)) (2*b*u/S)]
      _ ≤ ((|(a-1)/S^3 + (A'' + 1/S^3)| + |A''*((b*u+a)^2-1)|) + |2*b*u/S|) + |2*A'*b| := by
          linarith only [abs_add_le ((a-1)/S^3 + (A'' + 1/S^3)) (A''*((b*u+a)^2-1))]
      _ ≤ (((|(a-1)/S^3| + |A'' + 1/S^3|) + |A''*((b*u+a)^2-1)|) + |2*b*u/S|) + |2*A'*b| := by
          linarith only [abs_add_le ((a-1)/S^3) (A'' + 1/S^3)]
      _ ≤ (((5*ν + 301*(ν+ν^2)) + (8+ν)*(21*ν*(20*ν+13/3))) + 67*ν) + 2*(2+ν)*(25*ν) := by
          linarith only [hT1, hT2, hApp, hT4, hT5]
      _ ≤ 4000 * (ν + ν^2 + ν^3) := by nlinarith only [hν]
  -- STEP 8: |c| ≤ (5/3)|K|
  have hc_le : |c| ≤ 5 / 3 * |K| := by
    have hxA : 0 ≤ -(x * A') := by rw [hxdef]; nlinarith only [hsignu, ha]
    have hD2 : 0 < A - x * A' := by linarith only [hxA, hA]
    have h := congrArg (fun t : ℝ => |t|) hE3
    rw [abs_mul, abs_of_pos hD2, abs_mul, abs_of_pos ha] at h
    have h3 : (3/5) * a ≤ A - x * A' := by
      have h4 : A = a * S := hSA.symm
      nlinarith only [hSge, ha, h4, hxA]
    have h6 : |c| * ((3:ℝ)/5*a) ≤ |c| * (A - x*A') := mul_le_mul_of_nonneg_left h3 (abs_nonneg c)
    have h7 : |c| * ((3:ℝ)/5*a) ≤ a * |K| := by linarith only [h6, h]
    nlinarith only [h7, ha, abs_nonneg c]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [ha1, hν]
  · nlinarith only [hb25, hν]
  · nlinarith only [hc_le, hKb, hν]

/-! ## The target -/

theorem radialDevPolyBound :
    ∃ C : ℝ, 0 < C ∧ ∀ {f ρ : ℝ → ℝ} {u ν : ℝ},
      0 ≤ ν → |u| < 4 / 5 → u ≠ 0 →
      ContDiffOn ℝ 2 ρ (Set.Ioo (-1 : ℝ) 1) →
      ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) →
      |ρ u * u| ≤ 17 / 20 →
      0 < ρ u →
      0 < f (ρ u * u) →
      1 - |ρ u * u| ≤ f (ρ u * u) →
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f →
      f 1 = 0 → f (-1) = 0 → f 0 = 1 →
      (∀ t : ℝ, 0 < t → t < 1 → deriv f t ≤ 0) →
      (∀ t : ℝ, -1 < t → t < 0 → 0 ≤ deriv f t) →
      (∀ v ∈ Set.Ioo (-1 : ℝ) 1, ρ v * Real.sqrt (1 - v ^ 2) = f (ρ v * v)) →
      |f (ρ u * u) - Work.OddEnvelope.semicircle (ρ u * u)| ≤ ν →
      |deriv f (ρ u * u) - deriv Work.OddEnvelope.semicircle (ρ u * u)| ≤ ν →
      |deriv (deriv f) (ρ u * u) - deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u)| ≤ ν →
      |ρ u - 1| ≤ C * (ν + ν ^ 2) ∧
        |deriv ρ u| ≤ C * (ν + ν ^ 2 + ν ^ 3) ∧
        |deriv (deriv ρ) u| ≤ C * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) := by
  refine ⟨(10:ℝ) ^ 6, by norm_num, ?_⟩
  intro f ρ u ν hν hu85 hu0 hρ hf hx1720 hapos hApos hchord hconc hf1 hfm1 hf0 hdright hdleft
    hgraph hc1 hc2 hc3
  -- basic membership facts
  have hu1 : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    have h := abs_lt.mp hu85
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have huabs1 : |u| < 1 := by have h := abs_lt.mp hu85; rw [abs_lt]; exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have hxlt : |ρ u * u| < 1 := by
    have h := abs_le.mp hx1720
    rw [abs_lt]; exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have hu2pos : 0 < 1 - u ^ 2 := by have h := abs_lt.mp hu85; nlinarith only [h.1, h.2]
  have hx2pos : 0 < 1 - (ρ u * u) ^ 2 := by
    have h := abs_le.mp hx1720; nlinarith only [h.1, h.2]
  -- the profile upper bound (concavity)
  have hAle : f (ρ u * u) ≤ 1 + |ρ u * u| := profileLeOneAddAbs hconc hf0 hf1 hfm1 hxlt
  -- the radial identity at `u`
  have hSA : ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u) := hgraph u hu1
  -- semicircle bounds
  have hSle : Real.sqrt (1 - u ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith only [sq_nonneg u])
  have hsle : Real.sqrt (1 - (ρ u * u) ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith only [sq_nonneg (ρ u * u)])
  have hspos : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 hu2pos
  have hsnonneg : 0 ≤ Real.sqrt (1 - (ρ u * u) ^ 2) := Real.sqrt_nonneg _
  -- |ρ u - 1| ≤ ν
  have hkeyn : (ρ u) ^ 2 - 1 = (f (ρ u * u)) ^ 2 - (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 2 := by
    have hSu : (Real.sqrt (1 - u ^ 2)) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt hu2pos.le
    have hSx : (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 2 = 1 - (ρ u * u) ^ 2 := Real.sq_sqrt hx2pos.le
    have h1 : (ρ u) ^ 2 * (Real.sqrt (1 - u ^ 2)) ^ 2 = (f (ρ u * u)) ^ 2 := by
      rw [← mul_pow, hSA]
    rw [hSu] at h1
    rw [hSx]
    nlinarith only [h1]
  have hAle' : f (ρ u * u) + Real.sqrt (1 - (ρ u * u) ^ 2) ≤ ρ u + 1 := by
    have h1 : f (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) := hSA.symm
    nlinarith only [h1, hSle, hsle, hapos]
  have ha1 : |ρ u - 1| ≤ ν :=
    abs_sub_one_le_of_sq hapos hApos hsnonneg hkeyn hc1 hAle' hν
  -- the two relations
  obtain ⟨hE2, hE3⟩ := rhoRelationsLocal hρ hf huabs1 hxlt hgraph
  -- conversion of the closeness hypotheses
  have hAclose : |f (ρ u * u) - Real.sqrt (1 - (ρ u * u) ^ 2)| ≤ ν := hc1
  have hA'close : |deriv f (ρ u * u) + (ρ u * u) / Real.sqrt (1 - (ρ u * u) ^ 2)| ≤ ν := by
    have h := hc2
    have hd : deriv Work.OddEnvelope.semicircle (ρ u * u) =
        -(ρ u * u) / Real.sqrt (1 - (ρ u * u) ^ 2) := by
      change deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)) (ρ u * u) = _
      exact Work.OddCurve.LowSlope.radialAux_deriv_sqrt hxlt
    rw [hd] at h
    have he : deriv f (ρ u * u) - (-(ρ u * u) / Real.sqrt (1 - (ρ u * u) ^ 2)) =
        deriv f (ρ u * u) + (ρ u * u) / Real.sqrt (1 - (ρ u * u) ^ 2) := by ring
    rwa [he] at h
  have hA''close : |deriv (deriv f) (ρ u * u) + 1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3| ≤ ν := by
    have h := hc3
    have hd : deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u) =
        -1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 :=
      semicircle_deriv2_eq hxlt
    rw [hd] at h
    have he : deriv (deriv f) (ρ u * u) - (-1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3) =
        deriv (deriv f) (ρ u * u) + 1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 := by ring
    rwa [he] at h
  have hspread : |1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 - 1 / (Real.sqrt (1 - u ^ 2)) ^ 3|
      ≤ 300 * (ν + ν ^ 2) := by
    have h := semicircleDeriv2Close hν hu85 ha1 hx1720
    have h1 : deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u) =
        -1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 := semicircle_deriv2_eq hxlt
    have h2 : deriv (deriv Work.OddEnvelope.semicircle) u =
        -1 / (Real.sqrt (1 - u ^ 2)) ^ 3 := semicircle_deriv2_eq huabs1
    rw [h1, h2] at h
    rw [show (-1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3) - (-1 / (Real.sqrt (1 - u ^ 2)) ^ 3)
        = -(1 / (Real.sqrt (1 - (ρ u * u) ^ 2)) ^ 3 - 1 / (Real.sqrt (1 - u ^ 2)) ^ 3) from by ring,
      abs_neg] at h
    exact h
  -- the sign condition
  have hsign : (0 < u → deriv f (ρ u * u) ≤ 0) ∧ (u < 0 → 0 ≤ deriv f (ρ u * u)) := by
    constructor
    · intro hu
      have h1 : 0 < ρ u * u := mul_pos hapos hu
      have h2 : ρ u * u < 1 := by have h := abs_le.mp hx1720; linarith only [h.2]
      exact hdright (ρ u * u) h1 h2
    · intro hu
      have h1 : ρ u * u < 0 := mul_neg_of_pos_of_neg hapos hu
      have h2 : -1 < ρ u * u := by have h := abs_le.mp hx1720; linarith only [h.1]
      exact hdleft (ρ u * u) h2 h1
  exact radialBoundCore hν hu85 hapos hApos hx1720 hAle hSA hAclose hA'close hA''close hspread
    hsign hE2 hE3

end

end Work.OddVolterra.Free
