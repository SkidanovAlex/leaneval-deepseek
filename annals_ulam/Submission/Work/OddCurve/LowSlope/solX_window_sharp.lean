import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogDefs
import Submission.Work.OddCurve.LowSlope.RadialLogConstruction
import Submission.Work.OddCurve.LowSlope.rpow_sub_ge_deriv

/-!
# The sharp window bound for the normalised first coordinate `x = solX`

For the odd-dimensional two-power system the normalised first `m`-th power
`x = R^m/(2+A)` is the unique point of `(0,1)` with

  `radH n x = B / (2+A)^θ`,      `radH n x = x^θ - (1-x)^θ`,   `θ = (2n+1)/(2n+2)`.

The right-hand side is at most `σ/(2-σ)^θ ≤ 5σ/8` when `|A|,|B| ≤ σ ≤ 1/8`; on the other hand
`radH n` grows at least like `(3/2)(x - 1/2)` away from `1/2` (because `radH n' (1/2) =
2θ·2^{1-θ} ≥ 3/2` for `θ ≥ 3/4`, and `radH n` is odd about `1/2`). Hence `|x - 1/2| ≤ 5σ/12`.

Everything is elementary: `rpow_sub_ge_deriv` is the concavity estimate for `t ↦ t^θ`, and the
only numerical input is `(15/8)^{3/4} ≥ 8/5` (i.e. `(15/8)^3 ≥ (8/5)^4`).
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.OddCurve.LowSlope

/-! ## Two elementary facts about `radH n` near `1/2` -/

/-- `radH n` is odd about `1/2`. -/
lemma radH_half_sub (n : ℕ) (t : ℝ) :
    radH n (1 / 2 - t) = -radH n (1 / 2 + t) := by
  rw [radH_apply, radH_apply,
    show (1 : ℝ) - (1 / 2 - t) = 1 / 2 + t by ring,
    show (1 : ℝ) - (1 / 2 + t) = 1 / 2 - t by ring]
  ring

/-- `radH n` grows at least like `(3/2) t` to the right of `1/2`, for `n ≥ 1`. -/
lemma radH_half_add_ge (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    (3 / 2) * t ≤ radH n (1 / 2 + t) := by
  have hθ0 : 0 < radTh n := radTh_pos n
  have hθ1 : radTh n ≤ 1 := radTh_le_one n
  have hθ34 : (3 / 4 : ℝ) ≤ radTh n := radTh_ge_three_quarters n hn
  have hbpos : 0 < (1 / 2 - t) := by linarith
  have hba : (1 / 2 - t) ≤ (1 / 2 + t) := by linarith
  have hkey := rpow_sub_ge_deriv (θ := radTh n) (x := 1 / 2 - t) (y := 1 / 2 + t)
    hθ0 hθ1 hbpos hba
  have hsub : (1 / 2 + t) - (1 / 2 - t) = 2 * t := by ring
  have hkey' : radTh n * (1 / 2 + t) ^ (radTh n - 1) * (2 * t)
      ≤ (1 / 2 + t) ^ (radTh n) - (1 / 2 - t) ^ (radTh n) := by
    have h := hkey
    rwa [hsub] at h
  have hpy : (1 : ℝ) ≤ (1 / 2 + t) ^ (radTh n - 1) := by
    have hapos : 0 < (1 / 2 + t) := by linarith
    have ha1 : (1 / 2 + t) ≤ 1 := by linarith
    have h := Real.rpow_le_rpow_of_exponent_ge hapos ha1 (show radTh n - 1 ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hmono : radTh n * 1 * (2 * t) ≤ radTh n * (1 / 2 + t) ^ (radTh n - 1) * (2 * t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpy hθ0.le) (by linarith)
  have hlow : (3 / 2) * t ≤ radTh n * 1 * (2 * t) := by nlinarith [hθ34, ht0]
  have hrh : radH n (1 / 2 + t)
      = (1 / 2 + t) ^ (radTh n) - (1 / 2 - t) ^ (radTh n) := by
    rw [radH_apply, show (1 : ℝ) - (1 / 2 + t) = 1 / 2 - t by ring]
  rw [hrh]
  linarith

/-! ## The numerical input -/

/-- `(15/8)^{3/4} ≥ 8/5`, since `(15/8)^3 = 3375/512 ≥ 4096/625 = (8/5)^4`. -/
lemma fifteen_eighths_rpow_three_quarters_le :
    (8 : ℝ) / 5 ≤ ((15 : ℝ) / 8) ^ (3 / 4 : ℝ) := by
  have h := le_rpow_quarter (a := (8 : ℝ) / 5) (q := ((15 : ℝ) / 8) ^ (3 : ℕ))
    (by norm_num) (by norm_num)
  rwa [rpow_nat_pow_quarter ((15 : ℝ) / 8) (by norm_num)] at h

/-! ## The window bound -/

theorem solX_window_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solX n A B α - 1 / 2| ≤ 5 * σ / 12 := by
  have hσ' : σ ≤ 1 / 2 := by linarith
  have hθ0 : 0 < radTh n := radTh_pos n
  have hmem := solX_mem hn hσ' hA hB hα
  have hu := solU_mem hσ' hA hα
  have hu0 : 0 < solU A α := by linarith [hu.1]
  have huθ0 : 0 < (solU A α) ^ (radTh n) := Real.rpow_pos_of_pos hu0 _
  have hwabs : |solW n A B α| < 1 := by
    have h := solW_abs_le hn hσ' hA hB hα
    linarith
  have hradH : radH n (solX n A B α) = solW n A B α := by
    rw [solX_apply]
    exact radH_radInv hwabs
  -- the size of the normalised datum: `u ≥ 2 - σ ≥ 15/8`
  have hu_ge : 2 - σ ≤ solU A α := by
    have h := neg_le_of_abs_le (hA α hα)
    rw [solU_apply]
    linarith
  have h8 : (8 : ℝ) / 5 ≤ (solU A α) ^ (radTh n) := by
    have h1 : ((15 : ℝ) / 8) ^ (radTh n) ≤ (solU A α) ^ (radTh n) :=
      Real.rpow_le_rpow (by norm_num) (by linarith) hθ0.le
    have h2 : ((15 : ℝ) / 8) ^ (3 / 4 : ℝ) ≤ ((15 : ℝ) / 8) ^ (radTh n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (radTh_ge_three_quarters n hn)
    exact le_trans (le_trans fifteen_eighths_rpow_three_quarters_le h2) h1
  -- step 1: `|w| ≤ 5σ/8`
  have hwle : |solW n A B α| ≤ 5 * σ / 8 := by
    have huθp : (0 : ℝ) < (2 + A α) ^ radTh n := by simpa [solU_apply] using huθ0
    have h8' : (8 : ℝ) / 5 ≤ (2 + A α) ^ radTh n := by simpa [solU_apply] using h8
    have hBle : |B α| ≤ σ := hB α hα
    rw [solW_apply, abs_div, abs_of_pos huθp]
    have h1 : |B α| / (2 + A α) ^ (radTh n) ≤ σ / (2 + A α) ^ (radTh n) :=
      div_le_div_of_nonneg_right hBle huθp.le
    have h2 : σ / (2 + A α) ^ (radTh n) ≤ σ / ((8 : ℝ) / 5) :=
      div_le_div_of_nonneg_left hσ.le (by norm_num) h8'
    have h3 : σ / ((8 : ℝ) / 5) = 5 * σ / 8 := by ring
    linarith
  -- step 2: `(3/2)|x - 1/2| ≤ |w|`
  have hcore : (3 / 2) * |solX n A B α - 1 / 2| ≤ |solW n A B α| := by
    rcases le_total (1 / 2 : ℝ) (solX n A B α) with hge | hle
    · have ht0 : 0 ≤ solX n A B α - 1 / 2 := by linarith
      have ht1 : solX n A B α - 1 / 2 ≤ 1 / 4 := by linarith [hmem.2]
      have h := radH_half_add_ge n hn ht0 ht1
      have heq : (1 : ℝ) / 2 + (solX n A B α - 1 / 2) = solX n A B α := by ring
      rw [heq, hradH] at h
      have hw0 : 0 ≤ solW n A B α := le_trans (by linarith) h
      rw [abs_of_nonneg ht0, abs_of_nonneg hw0]
      exact h
    · have ht0 : 0 ≤ 1 / 2 - solX n A B α := by linarith
      have ht1 : 1 / 2 - solX n A B α ≤ 1 / 4 := by linarith [hmem.1]
      have h := radH_half_add_ge n hn ht0 ht1
      have hodd := radH_half_sub n (1 / 2 - solX n A B α)
      have heq : (1 : ℝ) / 2 - (1 / 2 - solX n A B α) = solX n A B α := by ring
      rw [heq] at hodd
      have hw2 : solW n A B α = -radH n (1 / 2 + (1 / 2 - solX n A B α)) := by
        rw [← hradH, hodd]
      have hnn : solW n A B α ≤ 0 := by rw [hw2]; linarith
      have hxle : solX n A B α - 1 / 2 ≤ 0 := by linarith
      rw [abs_of_nonpos hxle, abs_of_nonpos hnn]
      linarith
  have hfin : (3 / 2) * |solX n A B α - 1 / 2| ≤ 5 * σ / 8 := le_trans hcore hwle
  linarith [abs_nonneg (solX n A B α - 1 / 2)]

end Work.OddCurve.LowSlope
