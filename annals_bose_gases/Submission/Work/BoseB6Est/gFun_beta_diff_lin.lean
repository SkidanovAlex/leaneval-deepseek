import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6Est.GFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the linear-in-`|b − b'|` estimate for the bracket at `τ = r²`

This module proves `gFun_beta_diff_lin`: for `b, b' ≥ 0` and `r > 0`,

  `|gFun r² b r − gFun r² b' r| ≤ (max b b') / r² * |b − b'|`.

At `τ = r²` the square root collapses, `√((r²+b)² − b²) = r √(r²+2b)`, so that the
increment is *exactly*

  `gFun r² b r − gFun r² b' r = (b − b') * K`,
  `K = 1 − 2r/(√(r²+2b) + √(r²+2b')) − (b+b')/(2r²)`,

and it remains to see that `|K| ≤ (max b b')/r²`.  Writing `u = √(r²+2b)`,
`v = √(r²+2b')`: from `u² = r² + 2b` we get `u − r = 2b/(u+r) ≤ b/r` (because
`u ≥ r`), whence

  `0 ≤ 1 − 2r/(u+v) = (u+v−2r)/(u+v) ≤ (b+b')/(2r²) ≤ (max b b')/r²`,

i.e. `K ≤ 0` and `−K ≤ (max b b')/r²`.  Together, `|K| ≤ (max b b')/r²`, and the
estimate follows.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6Est

/-- At `τ = r²` the bracket only involves the square root `√(r²+2b)`:
`gFun r² b r = r² + b − r √(r²+2b) − b²/(2r²)`. -/
lemma gFun_rsq_eq_sqrt (b r : ℝ) (hr : 0 < r) :
    gFun (r ^ 2) b r = r ^ 2 + b - r * Real.sqrt (r ^ 2 + 2 * b) - b ^ 2 / (2 * r ^ 2) := by
  rw [gFun]
  have h : (r ^ 2 + b) ^ 2 - b ^ 2 = r ^ 2 * (r ^ 2 + 2 * b) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]

/-- **Exact increment of the bracket at `τ = r²`.**  With `u = √(r²+2b)`,
`v = √(r²+2b')`:
`gFun r² b r − gFun r² b' r = (b − b')(1 − 2r/(u+v) − (b+b')/(2r²))`. -/
lemma gFun_beta_increment {b b' r : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') (hr : 0 < r) :
    gFun (r ^ 2) b r - gFun (r ^ 2) b' r
      = (b - b') * (1 - 2 * r / (Real.sqrt (r ^ 2 + 2 * b) + Real.sqrt (r ^ 2 + 2 * b'))
          - (b + b') / (2 * r ^ 2)) := by
  rw [gFun_rsq_eq_sqrt b r hr, gFun_rsq_eq_sqrt b' r hr]
  set u := Real.sqrt (r ^ 2 + 2 * b) with hu
  set v := Real.sqrt (r ^ 2 + 2 * b') with hv
  have hr2 : 0 ≤ r ^ 2 + 2 * b := by nlinarith [sq_nonneg r]
  have hr2' : 0 ≤ r ^ 2 + 2 * b' := by nlinarith [sq_nonneg r]
  have hu2 : u ^ 2 = r ^ 2 + 2 * b := by rw [hu, Real.sq_sqrt hr2]
  have hv2 : v ^ 2 = r ^ 2 + 2 * b' := by rw [hv, Real.sq_sqrt hr2']
  have huv : u + v ≠ 0 := by
    have h1 : 0 < u := by rw [hu, Real.sqrt_pos]; nlinarith [sq_pos_of_pos hr]
    have h2 : 0 < v := by rw [hv, Real.sqrt_pos]; nlinarith [sq_pos_of_pos hr]
    linarith
  have hkey : (u - v) * (u + v) = 2 * (b - b') := by nlinarith [hu2, hv2]
  have hdiff : u - v = 2 * (b - b') / (u + v) := by
    rw [eq_div_iff huv]; linarith [hkey]
  have step1 : r ^ 2 + b - r * u - b ^ 2 / (2 * r ^ 2)
        - (r ^ 2 + b' - r * v - b' ^ 2 / (2 * r ^ 2))
      = (b - b') - r * (u - v) - (b ^ 2 - b' ^ 2) / (2 * r ^ 2) := by ring
  have step2 : r * (u - v) = 2 * r * (b - b') / (u + v) := by rw [hdiff]; ring
  rw [step1, step2]
  field_simp
  ring

/-- **The kernel factor is bounded by `(max b b')/r²`.**  For `b, b' ≥ 0`, `r > 0`,
`|1 − 2r/(√(r²+2b) + √(r²+2b')) − (b+b')/(2r²)| ≤ (max b b')/r²`. -/
lemma gFun_beta_kernel_le {b b' r : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') (hr : 0 < r) :
    |1 - 2 * r / (Real.sqrt (r ^ 2 + 2 * b) + Real.sqrt (r ^ 2 + 2 * b'))
      - (b + b') / (2 * r ^ 2)| ≤ max b b' / r ^ 2 := by
  set u := Real.sqrt (r ^ 2 + 2 * b) with hu
  set v := Real.sqrt (r ^ 2 + 2 * b') with hv
  have hr2 : 0 ≤ r ^ 2 + 2 * b := by nlinarith [sq_nonneg r]
  have hr2' : 0 ≤ r ^ 2 + 2 * b' := by nlinarith [sq_nonneg r]
  have hu2 : u ^ 2 = r ^ 2 + 2 * b := by rw [hu, Real.sq_sqrt hr2]
  have hv2 : v ^ 2 = r ^ 2 + 2 * b' := by rw [hv, Real.sq_sqrt hr2']
  have hu_ge : r ≤ u := by
    rw [hu, Real.le_sqrt (le_of_lt hr) hr2]; nlinarith
  have hv_ge : r ≤ v := by
    rw [hv, Real.le_sqrt (le_of_lt hr) hr2']; nlinarith
  have hur : u + r ≠ 0 := by linarith
  have hvr : v + r ≠ 0 := by linarith
  have hur2 : u - r = 2 * b / (u + r) := by rw [eq_div_iff hur]; nlinarith [hu2]
  have hvr2 : v - r = 2 * b' / (v + r) := by rw [eq_div_iff hvr]; nlinarith [hv2]
  have hur_le : u - r ≤ b / r := by
    rw [hur2]
    have h1 : 2 * b / (u + r) ≤ 2 * b / (2 * r) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    have h2 : 2 * b / (2 * r) = b / r := by field_simp
    rw [h2] at h1; exact h1
  have hvr_le : v - r ≤ b' / r := by
    rw [hvr2]
    have h1 : 2 * b' / (v + r) ≤ 2 * b' / (2 * r) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    have h2 : 2 * b' / (2 * r) = b' / r := by field_simp
    rw [h2] at h1; exact h1
  have hsum_pos : 0 < u + v := by linarith
  -- `1 − 2r/(u+v) ≤ (b+b')/(2r²)`
  have hA : 1 - 2 * r / (u + v) ≤ (b + b') / (2 * r ^ 2) := by
    have h1 : 1 - 2 * r / (u + v) = (u + v - 2 * r) / (u + v) := by field_simp
    rw [h1]
    have hbb : b / r + b' / r = (b + b') / r := by rw [add_div]
    have hnum : u + v - 2 * r ≤ (b + b') / r := by linarith
    have hcb : 0 ≤ (b + b') / r := div_nonneg (by linarith) (le_of_lt hr)
    calc (u + v - 2 * r) / (u + v) ≤ ((b + b') / r) / (u + v) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hsum_pos)
      _ ≤ ((b + b') / r) / (2 * r) :=
          div_le_div_of_nonneg_left hcb (by linarith) (by linarith)
      _ = (b + b') / (2 * r ^ 2) := by field_simp
  have hK0 : 1 - 2 * r / (u + v) - (b + b') / (2 * r ^ 2) ≤ 0 := by linarith
  have hnn : 0 ≤ 1 - 2 * r / (u + v) := by
    have h2 : 2 * r / (u + v) ≤ 1 := by rw [div_le_one hsum_pos]; linarith
    linarith
  have hc2M : (b + b') / (2 * r ^ 2) ≤ max b b' / r ^ 2 := by
    have hhalf : (b + b') / 2 ≤ max b b' := by
      have := le_max_left b b'; have := le_max_right b b'; linarith
    have he : (b + b') / (2 * r ^ 2) = ((b + b') / 2) / r ^ 2 := by ring
    rw [he]
    exact div_le_div_of_nonneg_right hhalf (by positivity)
  have hM0 : 0 ≤ max b b' / r ^ 2 := div_nonneg (le_max_of_le_left hb) (by positivity)
  rw [abs_le]
  constructor <;> linarith

theorem gFun_beta_diff_lin {b b' r : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') (hr : 0 < r) :
    |gFun (r ^ 2) b r - gFun (r ^ 2) b' r| ≤ max b b' / r ^ 2 * |b - b'| := by
  have h := gFun_beta_kernel_le hb hb' hr
  calc |gFun (r ^ 2) b r - gFun (r ^ 2) b' r|
      = |b - b'| * |1 - 2 * r / (Real.sqrt (r ^ 2 + 2 * b) + Real.sqrt (r ^ 2 + 2 * b'))
          - (b + b') / (2 * r ^ 2)| := by rw [gFun_beta_increment hb hb' hr, abs_mul]
    _ ≤ |b - b'| * (max b b' / r ^ 2) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = max b b' / r ^ 2 * |b - b'| := by ring

end Work.BoseB6Est
