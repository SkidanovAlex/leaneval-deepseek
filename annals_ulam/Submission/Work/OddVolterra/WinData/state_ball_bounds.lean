import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# The state ball of `baseState σ` lies well inside the positivity region

Every state `z` in the closed ball of radius `ρ ≤ 1/2` around the base state
`baseState σ = (profileX σ, profileX σ, (profileX)' σ, (profileX)' σ)` has

* positive first two coordinates, indeed `z 0, z 1 ≥ 1/5`;
* all four coordinates bounded by `2` in absolute value,

for every slope `σ ∈ [a,b] ⊆ (0,1]`.

The constants are far from sharp (`profileX σ ≥ 1/√2` on `|σ| ≤ 1` and
`|(profileX)' σ| ≤ 1` there), but they are the ones the rest of the window
construction quotes.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra

noncomputable section

/-- `1/√2 - 1/2 > 1/5`: the margin by which the first two coordinates of the
state ball stay positive. -/
private lemma one_div_sqrt_two_sub_half_gt_one_fifth :
    (1 / 5 : ℝ) < 1 / Real.sqrt 2 - 1 / 2 := by
  have h7 : (7 : ℝ) / 10 < 1 / Real.sqrt 2 := by
    rw [lt_div_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
    have hkey : (7 : ℝ) / 10 * Real.sqrt 2 < 1 ↔ Real.sqrt 2 < 10 / 7 := by
      rw [show (1 : ℝ) = (7 / 10) * (10 / 7) by norm_num,
        mul_lt_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 7 / 10)]
    rw [hkey]
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 10 / 7)).mpr (by norm_num)
  linarith

/-- `profileX` is bounded below by its value at `1` on `[0,1]`. -/
private lemma profileX_lower {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    1 / Real.sqrt 2 ≤ Commons.Geometry.Ulam.profileX σ := by
  have h := Commons.Geometry.Ulam.profileX_le_profileX' hσ0 hσ1
  have h1 : Commons.Geometry.Ulam.profileX 1 = 1 / Real.sqrt 2 := by
    simp only [Commons.Geometry.Ulam.profileX]; norm_num
  linarith [h, h1]

/-- `profileX` is bounded above by `1`. -/
private lemma profileX_le_one (σ : ℝ) : Commons.Geometry.Ulam.profileX σ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 + σ ^ 2) := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [sq_nonneg σ]
  simp only [Commons.Geometry.Ulam.profileX, one_div]
  exact inv_le_one_of_one_le₀ h1

/-- The derivative of `profileX` is bounded by `1` on `[0,1]`. -/
private lemma abs_deriv_profileX_le_one {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |deriv Commons.Geometry.Ulam.profileX σ| ≤ 1 := by
  rw [Commons.Geometry.Ulam.deriv_profileX_eq]
  have hp0 : 0 ≤ Commons.Geometry.Ulam.profileX σ := by
    simp only [Commons.Geometry.Ulam.profileX, one_div]
    positivity
  have hq0 : 0 ≤ σ / (1 + σ ^ 2) := by positivity
  have hq1 : σ / (1 + σ ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 1 + σ ^ 2)]
    nlinarith [sq_nonneg σ, hσ0, hσ1]
  rw [abs_mul, abs_neg, abs_of_nonneg hq0, abs_of_nonneg hp0]
  calc σ / (1 + σ ^ 2) * Commons.Geometry.Ulam.profileX σ ≤ 1 * 1 :=
        mul_le_mul hq1 (profileX_le_one σ) hp0 (by norm_num)
    _ = 1 := by norm_num

theorem state_ball_bounds {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) {σ : ℝ} (hσ : σ ∈ Set.Icc a b)
    {z : Work.OddVolterra.St} (hz : z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ) :
    (1 / 5 : ℝ) ≤ z 0 ∧ (1 / 5 : ℝ) ≤ z 1 ∧ (∀ i : Fin 4, |z i| ≤ 2) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le ha hσ.1
  have hσle1 : σ ≤ 1 := le_trans hσ.2 hb
  -- the coordinatewise bound supplied by the closed ball
  have hcoord : ∀ i : Fin 4, |z i - baseState σ i| ≤ ρ := by
    intro i
    have h := Metric.mem_closedBall.mp hz
    rw [dist_pi_le_iff (le_of_lt hρ0)] at h
    simpa [Real.dist_eq] using h i
  have hpx_lo : 1 / Real.sqrt 2 ≤ Commons.Geometry.Ulam.profileX σ :=
    profileX_lower (le_of_lt hσ0) hσle1
  have hpx_hi : Commons.Geometry.Ulam.profileX σ ≤ 1 := profileX_le_one σ
  have hd : |deriv Commons.Geometry.Ulam.profileX σ| ≤ 1 :=
    abs_deriv_profileX_le_one (le_of_lt hσ0) hσle1
  have h0 : |z 0 - Commons.Geometry.Ulam.profileX σ| ≤ ρ := by
    simpa [baseState] using hcoord 0
  have h1 : |z 1 - Commons.Geometry.Ulam.profileX σ| ≤ ρ := by
    simpa [baseState] using hcoord 1
  have h2 : |z 2 - deriv Commons.Geometry.Ulam.profileX σ| ≤ ρ := by
    simpa [baseState] using hcoord 2
  have h3 : |z 3 - deriv Commons.Geometry.Ulam.profileX σ| ≤ ρ := by
    simpa [baseState] using hcoord 3
  have h0' : -ρ ≤ z 0 - Commons.Geometry.Ulam.profileX σ := (abs_le.mp h0).1
  have h0'' : z 0 - Commons.Geometry.Ulam.profileX σ ≤ ρ := (abs_le.mp h0).2
  have h1' : -ρ ≤ z 1 - Commons.Geometry.Ulam.profileX σ := (abs_le.mp h1).1
  have h1'' : z 1 - Commons.Geometry.Ulam.profileX σ ≤ ρ := (abs_le.mp h1).2
  have hz0_lo : (1 / 5 : ℝ) ≤ z 0 := by
    have hm := one_div_sqrt_two_sub_half_gt_one_fifth
    linarith
  have hz1_lo : (1 / 5 : ℝ) ≤ z 1 := by
    have hm := one_div_sqrt_two_sub_half_gt_one_fifth
    linarith
  have hz0_hi : z 0 ≤ 2 := by linarith
  have hz1_hi : z 1 ≤ 2 := by linarith
  -- the two derivative coordinates: `|z j| ≤ |z j - (profileX)' σ| + |(profileX)' σ| ≤ ρ + 1`
  have h23 : ∀ j : Fin 4, (j = 2 ∨ j = 3) → |z j| ≤ 2 := by
    intro j hj
    have hb : |z j - deriv Commons.Geometry.Ulam.profileX σ| ≤ ρ := by
      rcases hj with h | h
      · subst h; exact h2
      · subst h; exact h3
    have hbd : |z j| ≤ ρ + 1 := by
      calc |z j| = |(z j - deriv Commons.Geometry.Ulam.profileX σ)
              + deriv Commons.Geometry.Ulam.profileX σ| := by ring_nf
        _ ≤ |z j - deriv Commons.Geometry.Ulam.profileX σ|
              + |deriv Commons.Geometry.Ulam.profileX σ| := abs_add_le _ _
        _ ≤ ρ + 1 := add_le_add hb hd
    linarith
  have hb0 : |z (0 : Fin 4)| ≤ 2 := by
    rw [abs_le]
    exact ⟨by linarith [hz0_lo], hz0_hi⟩
  have hb1 : |z (1 : Fin 4)| ≤ 2 := by
    rw [abs_le]
    exact ⟨by linarith [hz1_lo], hz1_hi⟩
  refine ⟨hz0_lo, hz1_lo, ?_⟩
  intro i
  fin_cases i
  · exact hb0
  · exact hb1
  · exact h23 2 (Or.inl rfl)
  · exact h23 3 (Or.inr rfl)

end

end Work.OddVolterra.WinData
