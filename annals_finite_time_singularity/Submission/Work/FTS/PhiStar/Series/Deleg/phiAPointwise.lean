/-
# `phiAPointwise` — the two pointwise decay regimes of `𝒜φ = phiA α`

`phiA α z = αz²φ''(z) + (5+α)zφ'(z)` with `φ = 2z/(1+z)²` is the separable radial source of the
`Φ_*` decomposition.  Its explicit form (`Work.FTS.PhiStar.phiA_eq`) is

  `phiA α z = 4αz²(z-2)/(1+z)⁴ + 2(5+α)z(1-z)/(1+z)³`,

from which the two *sharp* regimes used by the radial Green-function estimates follow, uniformly in
`α ∈ (0,1]`:

* `phiA_abs_le_small`  : `|phiA α z| ≤ 20 z`  for `0 < z ≤ 1`  (`𝒜φ` vanishes at `0` linearly);
* `phiA_abs_le_large`  : `|phiA α z| ≤ 24 / z` for `1 ≤ z`     (`𝒜φ → 0` like `(2α-10)/z`).

These are the pointwise inputs of the large-`z` bounds on the two Green pieces
`z^{-q}∫₀^z phiA α t t^{q-1}` and `z^{p}∫_{Ioi z} phiA α t t^{-p-1}`
(`Work.FTS.PhiStar.Series.Deleg.headPieceLargeZ`, `...tailPieceLargeZ`).
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.PhiStar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false

/-- **Small-`z` regime**: `|𝒜φ(α,z)| ≤ 20 z` for `0 < z ≤ 1`, `0 < α ≤ 1`. -/
theorem phiA_abs_le_small {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |Work.FTS.VocabO.phiA α z| ≤ 20 * z := by
  have hz : z ≠ -1 := by linarith
  rw [Work.FTS.PhiStar.phiA_eq α z hz]
  have hpos4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have hpos3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  have h2mz : (0 : ℝ) ≤ 2 - z := by linarith
  have h1mz : (0 : ℝ) ≤ 1 - z := by linarith
  have h1 : |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| ≤ 8 * z := by
    rw [abs_div, abs_of_pos hpos4, div_le_iff₀ hpos4]
    have habs : |4 * α * z ^ 2 * (z - 2)| = 4 * α * z ^ 2 * (2 - z) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg hz2, abs_of_nonpos (by linarith : z - 2 ≤ 0)]
      ring
    rw [habs]
    have hkey : z * (2 - z) ≤ 2 * (1 + z) ^ 4 := by
      have hzz : z * (2 - z) ≤ 1 := by nlinarith [sq_nonneg (z - 1)]
      have h4 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
      linarith
    have hnn : (0 : ℝ) ≤ z ^ 2 * (2 - z) := mul_nonneg hz2 h2mz
    nlinarith [hkey, hnn, hα, hα1, hz0]
  have h2 : |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| ≤ 12 * z := by
    rw [abs_div, abs_of_pos hpos3, div_le_iff₀ hpos3]
    have habs : |2 * (5 + α) * z * (1 - z)| = 2 * (5 + α) * z * (1 - z) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg hz0.le, abs_of_nonneg h1mz]
    rw [habs]
    have h4 : (1 : ℝ) ≤ (1 + z) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
    have hnn : (0 : ℝ) ≤ z * (1 - z) := mul_nonneg hz0.le h1mz
    have e1 : 2 * (5 + α) * z * (1 - z) ≤ 12 * z * (1 - z) := by
      have hc : 2 * (5 + α) ≤ 12 := by linarith
      have := mul_le_mul_of_nonneg_right hc hnn
      linarith [this]
    have e2 : 12 * z * (1 - z) ≤ 12 * z * (1 + z) ^ 3 := by
      have hle : (1 - z) ≤ (1 + z) ^ 3 := by linarith
      have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 12 * z)
      linarith [this]
    linarith [e1, e2]
  calc |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3|
      ≤ |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| + |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| :=
        abs_add_le _ _
    _ ≤ 8 * z + 12 * z := by linarith
    _ = 20 * z := by ring

/-- **Large-`z` regime**: `|𝒜φ(α,z)| ≤ 24 / z` for `1 ≤ z`, `0 < α ≤ 1`. -/
theorem phiA_abs_le_large {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz1 : 1 ≤ z) :
    |Work.FTS.VocabO.phiA α z| ≤ 24 / z := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz : z ≠ -1 := by linarith
  rw [Work.FTS.PhiStar.phiA_eq α z hz]
  have hpos4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have hpos3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hz4 : (0 : ℝ) < z ^ 4 := by positivity
  have h1 : |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| ≤ 12 / z := by
    have habs : |4 * α * z ^ 2 * (z - 2)| = 4 * α * z ^ 2 * |z - 2| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg (sq_nonneg z)]
    have hle : |z - 2| ≤ z + 2 := by rw [abs_le]; constructor <;> linarith
    have hA : 4 * α * z ^ 2 * |z - 2| ≤ 4 * z ^ 2 * (z + 2) := by
      have hnn : (0 : ℝ) ≤ z ^ 2 * |z - 2| := mul_nonneg (sq_nonneg z) (abs_nonneg _)
      have h2 : 4 * α * (z ^ 2 * |z - 2|) ≤ 4 * 1 * (z ^ 2 * (z + 2)) := by
        have hab : z ^ 2 * |z - 2| ≤ z ^ 2 * (z + 2) := mul_le_mul_of_nonneg_left hle (sq_nonneg z)
        nlinarith [hab, hnn, hα, hα1]
      linarith [h2]
    have hB : 4 * z ^ 2 * (z + 2) ≤ 12 * z ^ 3 := by nlinarith [hz1]
    have hD : z ^ 4 ≤ (1 + z) ^ 4 := by nlinarith [hz0]
    rw [abs_div, abs_of_pos hpos4, habs]
    have hstep1 : 4 * α * z ^ 2 * |z - 2| / (1 + z) ^ 4 ≤ 12 * z ^ 3 / (1 + z) ^ 4 :=
      div_le_div_of_nonneg_right (by linarith) hpos4.le
    have hstep2 : 12 * z ^ 3 / (1 + z) ^ 4 ≤ 12 * z ^ 3 / z ^ 4 :=
      div_le_div_of_nonneg_left (by positivity) hz4 hD
    have hstep3 : 12 * z ^ 3 / z ^ 4 = 12 / z := by field_simp
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  have h2 : |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| ≤ 12 / z := by
    have habs : |2 * (5 + α) * z * (1 - z)| = 2 * (5 + α) * z * |1 - z| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg hz0.le]
    have hle : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
    have hA : 2 * (5 + α) * z * |1 - z| ≤ 12 * z * (1 + z) := by
      have hab : z * |1 - z| ≤ z * (1 + z) := mul_le_mul_of_nonneg_left hle hz0.le
      have hnn : (0 : ℝ) ≤ z * |1 - z| := mul_nonneg hz0.le (abs_nonneg _)
      have h2 : 2 * (5 + α) * (z * |1 - z|) ≤ 12 * (z * (1 + z)) := by
        have hc : 2 * (5 + α) ≤ 12 := by linarith
        nlinarith [hab, hnn, hc]
      linarith [h2]
    rw [abs_div, abs_of_pos hpos3, habs]
    have hstep1 : 2 * (5 + α) * z * |1 - z| / (1 + z) ^ 3 ≤ 12 * z * (1 + z) / (1 + z) ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) hpos3.le
    have hstep2 : 12 * z * (1 + z) / (1 + z) ^ 3 ≤ 12 * z / z ^ 2 := by
      have he : 12 * z * (1 + z) / (1 + z) ^ 3 = 12 * z / (1 + z) ^ 2 := by field_simp
      rw [he]
      exact div_le_div_of_nonneg_left (by positivity) hz2 (by nlinarith [hz0])
    have hstep3 : 12 * z / z ^ 2 = 12 / z := by field_simp
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  calc |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3|
      ≤ |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| + |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| :=
        abs_add_le _ _
    _ ≤ 12 / z + 12 / z := by linarith
    _ = 24 / z := by ring

end Work.FTS.PhiStar.Series.Deleg
