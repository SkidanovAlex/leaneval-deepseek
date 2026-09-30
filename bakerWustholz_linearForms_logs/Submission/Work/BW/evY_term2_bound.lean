import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numerical bound: `log 2432 ≤ 8`, proved from the exponential series. -/
private lemma log2432_le_eight : Real.log 2432 ≤ 8 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2432)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 15
  have hsum : (2432 : ℝ) ≤
      Finset.sum (Finset.range 15) (fun i => (8 : ℝ) ^ i / Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- The tangent-line bound for the logarithm: `log x ≤ log a - 1 + x/a`. -/
private lemma log_le_tangent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a - 1 + x / a := by
  have hxa : 0 < x / a := div_pos hx ha
  have h : a * (x / a) = x := by field_simp
  have hmul := Real.log_mul (ne_of_gt ha) (ne_of_gt hxa)
  rw [h] at hmul
  have h2 : Real.log (x / a) ≤ x / a - 1 := Real.log_le_sub_one_of_pos hxa
  linarith

theorem evY_term2_bound {S D u xi : ℝ} (hS : 608 ≤ S) (hD : 0 ≤ D) (hu : 1 ≤ u)
    (hxi : 0 < xi) (hxi2 : xi ≤ 0.732) :
    6.3 * xi * D * (2 * Real.log (4 * u * S) + 3) / u ≤ 0.15 * S * D := by
  have hu0 : 0 < u := by linarith
  have harg : 0 < 4 * u * S := by positivity
  -- bound `log (4 u S)` by the tangent line of `log` at `2432`
  have htang : Real.log (4 * u * S) ≤ Real.log 2432 - 1 + (4 * u * S) / 2432 :=
    log_le_tangent harg (by norm_num)
  have hAup : 2 * Real.log (4 * u * S) + 3 ≤ 17 + 8 * u * S / 2432 := by
    have := log2432_le_eight
    linarith
  -- divide by `u ≥ 1`
  have hnum : (2 * Real.log (4 * u * S) + 3) / u ≤ 17 + 8 * S / 2432 := by
    have h1 : (2 * Real.log (4 * u * S) + 3) / u ≤ (17 + 8 * u * S / 2432) / u :=
      div_le_div_of_nonneg_right hAup (le_of_lt hu0)
    have h2 : (17 + 8 * u * S / 2432) / u = 17 / u + 8 * S / 2432 := by
      field_simp
    have h3 : 17 / u ≤ 17 := by
      rw [div_le_iff₀ hu0]
      nlinarith
    linarith [h2 ▸ h1, h3]
  have hAnonneg : 0 ≤ (2 * Real.log (4 * u * S) + 3) / u := by
    have hlogpos : 0 ≤ Real.log (4 * u * S) := Real.log_nonneg (by nlinarith)
    positivity
  -- `6.3 xi A ≤ 6.3 * 0.732 * A ≤ ...`
  have hstep1 : 6.3 * xi * ((2 * Real.log (4 * u * S) + 3) / u) ≤
      6.3 * 0.732 * ((2 * Real.log (4 * u * S) + 3) / u) := by
    have := mul_le_mul_of_nonneg_right hxi2 hAnonneg
    nlinarith [this]
  have hstep2 : 6.3 * 0.732 * ((2 * Real.log (4 * u * S) + 3) / u) ≤
      (11529 / 2500 : ℝ) * (17 + 8 * S / 2432) := by
    have hc : (6.3 * 0.732 : ℝ) = 11529 / 2500 := by norm_num
    rw [hc]
    exact mul_le_mul_of_nonneg_left hnum (by norm_num)
  have hstep3 : (11529 / 2500 : ℝ) * (17 + 8 * S / 2432) ≤ 0.15 * S := by nlinarith
  have hmain : 6.3 * xi * ((2 * Real.log (4 * u * S) + 3) / u) ≤ 0.15 * S := by linarith
  -- multiply by `D ≥ 0`
  have hDmul := mul_le_mul_of_nonneg_right hmain hD
  calc 6.3 * xi * D * (2 * Real.log (4 * u * S) + 3) / u
      = 6.3 * xi * ((2 * Real.log (4 * u * S) + 3) / u) * D := by ring
    _ ≤ 0.15 * S * D := hDmul

end Work.BW
