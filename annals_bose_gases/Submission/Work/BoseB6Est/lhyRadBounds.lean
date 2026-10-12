import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB6Est.lhyRadBounds`

Pointwise bounds and integrability for the radial Bogoliubov model bracket

  `lhyRad c r = (r²+c) − √((r²+c)²−c²) − c²/(2r²)`

at the model coupling `c = 8π` (FS `lem:BogIntegral`, the `β = 8π`, `τ̃ = r²`
case), together with the integrability of `r ↦ r²·lhyRad (8π) r` on `(0,∞)`.

The mathematics is one exact identity plus two elementary square-root bounds.
Since `(r²+c)² − c² = r²(r²+2c)`, for `r > 0`

  `√((r²+c)²−c²) = r√(r²+2c)`   and hence   `lhyRad c r = c²/W − c²/(2r²)`

with `W = r² + c + r√(r²+2c)`, using `(r²+c)² − (r√(r²+2c))² = c²`.  The two
square-root bounds are

  `r² < r√(r²+2c)   (c > 0)`   and   `r√(r²+2c) ≤ r² + c  (c ≥ 0)`,

the first giving `2r² < W` (so `lhyRad < 0` and `r²/W < 1/2`), the second
`W ≤ 2(r²+c)`, which is what turns `c²/(2r²) − c²/W` into `c³/(2r²(r²+c))`.

The estimates are proved for a general coupling `0 < c` and specialised at
`c = 8π` at the end, so the chapter can reuse them at other couplings.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

/-! ## 1. The square-root form of the radial bracket -/

/-- `√((r²+c)²−c²) = r√(r²+2c)` for `r > 0` (and arbitrary `c ≥ 0`). -/
lemma lhyRad_sqrt_eq {c r : ℝ} (hr : 0 < r) (_hc : 0 ≤ c) :
    Real.sqrt ((r ^ 2 + c) ^ 2 - c ^ 2) = r * Real.sqrt (r ^ 2 + 2 * c) := by
  have h1 : (r ^ 2 + c) ^ 2 - c ^ 2 = r ^ 2 * (r ^ 2 + 2 * c) := by ring
  rw [h1, Real.sqrt_mul (show (0 : ℝ) ≤ r ^ 2 from sq_nonneg r)]
  rw [Real.sqrt_sq hr.le]

/-- **The denominator form of the model bracket.**  For `r > 0`, `c ≥ 0`,

  `lhyRad c r = c²/(r²+c+r√(r²+2c)) − c²/(2r²)`.

This is the exact form all the estimates below are read off from. -/
lemma lhyRad_eq_sqrtForm {c r : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    Work.BoseB6.lhyRad c r
      = c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c)) - c ^ 2 / (2 * r ^ 2) := by
  have h2 : (0 : ℝ) ≤ r ^ 2 + 2 * c := by positivity
  have hd2 : (Real.sqrt (r ^ 2 + 2 * c)) ^ 2 = r ^ 2 + 2 * c := Real.sq_sqrt h2
  have hkey : (r ^ 2 + c) - r * Real.sqrt (r ^ 2 + 2 * c)
      = c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c)) := by
    have hpos : 0 < r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c) := by
      have h1 : 0 < r ^ 2 + c := by linarith [pow_pos hr 2, hc]
      have h3 : 0 ≤ r * Real.sqrt (r ^ 2 + 2 * c) :=
        mul_nonneg hr.le (Real.sqrt_nonneg _)
      linarith
    rw [eq_div_iff hpos.ne']
    calc ((r ^ 2 + c) - r * Real.sqrt (r ^ 2 + 2 * c))
          * (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c))
        = (r ^ 2 + c) ^ 2 - (r * Real.sqrt (r ^ 2 + 2 * c)) ^ 2 := by ring
      _ = c ^ 2 := by rw [mul_pow, hd2]; ring
  simp only [Work.BoseB6.lhyRad]
  rw [lhyRad_sqrt_eq hr hc, hkey]

/-! ## 2. The two elementary square-root bounds -/

/-- `r√(r²+2c) ≤ r² + c` for `r > 0`, `c ≥ 0` (both sides are nonnegative and
their squares compare by `c² ≥ 0`). -/
lemma lhyRad_rd_le {c r : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    r * Real.sqrt (r ^ 2 + 2 * c) ≤ r ^ 2 + c := by
  have h2 : (0 : ℝ) ≤ r ^ 2 + 2 * c := by positivity
  have hle : (r * Real.sqrt (r ^ 2 + 2 * c)) ^ 2 ≤ (r ^ 2 + c) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h2]
    nlinarith [sq_nonneg c]
  have h := sq_le_sq.mp hle
  rwa [abs_of_nonneg (mul_nonneg hr.le (Real.sqrt_nonneg _)),
       abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2 + c)] at h

/-- `r² < r√(r²+2c)` for `r > 0`, `c > 0` (equivalently `2r² < r²+c+r√(r²+2c)`,
i.e. the bracket `lhyRad c r` is negative). -/
lemma lhyRad_rd_gt {c r : ℝ} (hr : 0 < r) (hc : 0 < c) :
    r ^ 2 < r * Real.sqrt (r ^ 2 + 2 * c) := by
  have hlt : r < Real.sqrt (r ^ 2 + 2 * c) := by
    rw [Real.lt_sqrt hr.le]
    linarith
  calc r ^ 2 = r * r := by ring
    _ < r * Real.sqrt (r ^ 2 + 2 * c) := mul_lt_mul_of_pos_left hlt hr

/-! ## 3. The pointwise estimates at a general coupling -/

/-- **`lhyRad c r < 0`** for `r > 0`, `c > 0`. -/
lemma lhyRad_neg {c r : ℝ} (hr : 0 < r) (hc : 0 < c) : Work.BoseB6.lhyRad c r < 0 := by
  have hid := lhyRad_eq_sqrtForm hr hc.le
  have h2r : 0 < 2 * r ^ 2 := by positivity
  have hlt : 2 * r ^ 2 < r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c) := by
    have := lhyRad_rd_gt hr hc
    linarith
  have hdiv : c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c)) < c ^ 2 / (2 * r ^ 2) :=
    div_lt_div_of_pos_left (by positivity : (0 : ℝ) < c ^ 2) h2r hlt
  rw [hid]
  linarith

/-- **`−(lhyRad c r) ≤ c³/(2r⁴)`** for `r > 0`, `c > 0`: the sharp small-distance
decay of the model bracket. -/
lemma lhyRad_neg_le {c r : ℝ} (hr : 0 < r) (hc : 0 < c) :
    -(Work.BoseB6.lhyRad c r) ≤ c ^ 3 / (2 * r ^ 4) := by
  have hrd : r * Real.sqrt (r ^ 2 + 2 * c) ≤ r ^ 2 + c := lhyRad_rd_le hr hc.le
  have hs0 : 0 < r ^ 2 + c := by linarith [pow_pos hr 2, hc]
  have hWpos : 0 < r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c) := by
    have := mul_nonneg hr.le (Real.sqrt_nonneg (r ^ 2 + 2 * c))
    linarith
  have hWs : r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c) ≤ 2 * (r ^ 2 + c) := by linarith
  have hA : c ^ 2 / (2 * r ^ 2) - c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c))
      ≤ c ^ 3 / (2 * r ^ 2 * (r ^ 2 + c)) := by
    have hle : c ^ 2 / (2 * (r ^ 2 + c))
        ≤ c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c)) :=
      div_le_div_of_nonneg_left (sq_nonneg c) hWpos hWs
    have h3 : c ^ 2 / (2 * r ^ 2) - c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c))
        ≤ c ^ 2 / (2 * r ^ 2) - c ^ 2 / (2 * (r ^ 2 + c)) := by linarith
    have h4 : c ^ 2 / (2 * r ^ 2) - c ^ 2 / (2 * (r ^ 2 + c))
        = c ^ 3 / (2 * r ^ 2 * (r ^ 2 + c)) := by
      have hr2 : r ^ 2 ≠ 0 := by positivity
      have hs : r ^ 2 + c ≠ 0 := hs0.ne'
      field_simp
      ring
    rwa [h4] at h3
  have hB : c ^ 3 / (2 * r ^ 2 * (r ^ 2 + c)) ≤ c ^ 3 / (2 * r ^ 4) := by
    have hlt : 2 * r ^ 4 ≤ 2 * r ^ 2 * (r ^ 2 + c) := by nlinarith [hs0, hc, sq_nonneg r]
    exact div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ c ^ 3)
      (by positivity : (0 : ℝ) < 2 * r ^ 4) hlt
  rw [lhyRad_eq_sqrtForm hr hc.le]
  linarith [hA, hB]

/-- **`|lhyRad c r| ≤ c + c²/(2r²)`** for `r > 0`, `c > 0`: the large-distance
bound with the linear-in-`c` size of the bracket. -/
lemma lhyRad_abs_le {c r : ℝ} (hr : 0 < r) (hc : 0 < c) :
    |Work.BoseB6.lhyRad c r| ≤ c + c ^ 2 / (2 * r ^ 2) := by
  have hneg := lhyRad_neg hr hc
  have hWpos : 0 < r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c) := by
    have h1 : 0 < r ^ 2 + c := by linarith [pow_pos hr 2, hc]
    have h3 : 0 ≤ r * Real.sqrt (r ^ 2 + 2 * c) :=
      mul_nonneg hr.le (Real.sqrt_nonneg _)
    linarith
  rw [abs_of_neg hneg, lhyRad_eq_sqrtForm hr hc.le]
  have h1 : 0 ≤ c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c)) :=
    div_nonneg (sq_nonneg c) hWpos.le
  linarith [h1, hc]

/-- **`|lhyRad c r| ≤ c³/(2r⁴)`** for `r > 0`, `c > 0`. -/
lemma lhyRad_abs_le' {c r : ℝ} (hr : 0 < r) (hc : 0 < c) :
    |Work.BoseB6.lhyRad c r| ≤ c ^ 3 / (2 * r ^ 4) := by
  rw [abs_of_neg (lhyRad_neg hr hc)]
  exact lhyRad_neg_le hr hc

/-! ## 4. Integrability of `r ↦ r² lhyRad c r` on `(0,∞)` -/

/-- The function `r ↦ r²·lhyRad c r` is measurable (it is built from `√` and
total division, with no singular point after multiplication by `r²`). -/
lemma measurable_lhyRad_mul (c : ℝ) :
    Measurable (fun r : ℝ => r ^ 2 * Work.BoseB6.lhyRad c r) := by
  simp only [Work.BoseB6.lhyRad]
  fun_prop

/-- **Integrability.**  For `c > 0` the map `r ↦ r²·lhyRad c r` is integrable on
`(0,∞)`: on `(0,1]` it is bounded by `c²/2` (since `2r² < W` gives
`0 ≤ r²/W ≤ 1/2`), while on `(1,∞)` it is dominated by `c³/(2r²)`. -/
lemma integrableOn_lhyRad_mul {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => r ^ 2 * Work.BoseB6.lhyRad c r) (Set.Ioi 0) := by
  have hmeas := measurable_lhyRad_mul c
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · -- on `(0,1]`: constant bound `c²/2`
    refine IntegrableOn.of_bound (show volume (Set.Ioc (0 : ℝ) 1) < ⊤ from by simp)
      hmeas.aestronglyMeasurable.restrict (c ^ 2 / 2) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with r hr
    have hr0 : 0 < r := hr.1
    have hWpos : 0 < r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c) := by
      have h1 : 0 < r ^ 2 + c := by linarith [pow_pos hr0 2, hc]
      have h3 : 0 ≤ r * Real.sqrt (r ^ 2 + 2 * c) :=
        mul_nonneg hr0.le (Real.sqrt_nonneg _)
      linarith
    have hlo : 0 ≤ r ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c)) :=
      div_nonneg (sq_nonneg r) hWpos.le
    have hhi : r ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c)) ≤ 1 := by
      rw [div_le_one hWpos]
      linarith [mul_nonneg hr0.le (Real.sqrt_nonneg (r ^ 2 + 2 * c)), hc]
    have heq : r ^ 2 * Work.BoseB6.lhyRad c r
        = c ^ 2 * (r ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c))) - c ^ 2 / 2 := by
      rw [lhyRad_eq_sqrtForm hr0 hc.le]
      field_simp
    rw [Real.norm_eq_abs, heq, abs_le]
    constructor <;> nlinarith [hlo, hhi, sq_nonneg c, hc]
  · -- on `(1,∞)`: dominated by `c³/(2r²)`
    have hpow : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    have hpow' : IntegrableOn (fun r : ℝ => (r ^ 2)⁻¹) (Set.Ioi 1) :=
      hpow.congr_fun (fun x hx => by
        have hx1 : (1 : ℝ) < x := hx
        have hx0 : 0 < x := by linarith
        show x ^ (-2 : ℝ) = (x ^ 2)⁻¹
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le,
          Real.rpow_natCast]) measurableSet_Ioi
    have hg : Integrable (fun r : ℝ => (c ^ 3 / 2) * (r ^ 2)⁻¹)
        (volume.restrict (Set.Ioi 1)) :=
      (hpow' : Integrable (fun r : ℝ => (r ^ 2)⁻¹) (volume.restrict (Set.Ioi 1))).const_mul
        (c ^ 3 / 2)
    refine hg.mono' hmeas.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have hr1 : (1 : ℝ) < r := hr
    have hr0 : 0 < r := by linarith
    have h2 := lhyRad_abs_le' hr0 hc
    calc |r ^ 2 * Work.BoseB6.lhyRad c r| = r ^ 2 * |Work.BoseB6.lhyRad c r| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
      _ ≤ r ^ 2 * (c ^ 3 / (2 * r ^ 4)) := mul_le_mul_of_nonneg_left h2 (sq_nonneg r)
      _ = (c ^ 3 / 2) * (r ^ 2)⁻¹ := by field_simp

/-! ## 5. The target: the model coupling `c = 8π` -/

theorem lhyRadBounds :
    (∀ r : ℝ, 0 < r → Work.BoseB6.lhyRad (8 * Real.pi) r < 0) ∧
    (∀ r : ℝ, 0 < r → -(Work.BoseB6.lhyRad (8 * Real.pi) r)
      ≤ (8 * Real.pi) ^ 3 / (2 * r ^ 4)) ∧
    (∀ r : ℝ, 0 < r → |Work.BoseB6.lhyRad (8 * Real.pi) r|
      ≤ 8 * Real.pi + (8 * Real.pi) ^ 2 / (2 * r ^ 2)) ∧
    (∀ r : ℝ, 0 < r → |Work.BoseB6.lhyRad (8 * Real.pi) r|
      ≤ (8 * Real.pi) ^ 3 / (2 * r ^ 4)) ∧
    MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * Work.BoseB6.lhyRad (8 * Real.pi) r)
      (Set.Ioi 0) := by
  have hc : (0 : ℝ) < 8 * Real.pi := by positivity
  exact ⟨fun r hr => lhyRad_neg hr hc,
         fun r hr => lhyRad_neg_le hr hc,
         fun r hr => lhyRad_abs_le hr hc,
         fun r hr => lhyRad_abs_le' hr hc,
         integrableOn_lhyRad_mul hc⟩

end Work.BoseB6Est
