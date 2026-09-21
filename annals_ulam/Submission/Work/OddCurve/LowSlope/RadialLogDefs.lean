import Mathlib
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.OddRadon.radialMap_injOn

/-!
# The normalised two-power radial system: definitions

For the odd dimension `d = 2n+1` the paper's radial system
`R^{d+1} + r^{d+1} = Φ/cos²`, `R^d - r^d = Ψ/cos` becomes, after writing
`u = 2 + A`, `v = B` for the deviations of the data from the ball's data `(2, 0)`,

  `R^m + r^m = u`,  `R^k - r^k = v`,      `m = 2n+2`, `k = 2n+1`.

Writing `x = R^m / u ∈ (0,1)` (the normalised first `m`-th power) and `θ = k/m`, the second
equation becomes the *scalar* equation

  `radH n x = v / u^θ`,   `radH n x = x^θ - (1-x)^θ`,

because `R^k - r^k = (xu)^θ - ((1-x)u)^θ = u^θ (x^θ - (1-x)^θ)`.

The function `x ↦ x^θ - (1-x)^θ` is strictly increasing from `-1` to `1` on `[0,1]`, so it has
an inverse `radInv` on `(-1,1)`; the radial functions are then recovered as

  `R = (x u)^{1/m}`,  `r = ((1-x) u)^{1/m}`.

This file contains the definitions and the elementary order/monotonicity facts only.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.OddCurve.LowSlope

/-- The exponent `θ = (2n+1)/(2n+2) = k/m` of the odd-dimensional radial system. -/
def radTh (n : ℕ) : ℝ := ((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)

/-- The scalar function `x ↦ x^θ - (1-x)^θ` whose inverse normalises the radial system. -/
def radH (n : ℕ) (x : ℝ) : ℝ := x ^ (radTh n) - (1 - x) ^ (radTh n)

lemma radTh_pos (n : ℕ) : 0 < radTh n := by
  unfold radTh
  positivity

lemma radTh_lt_one (n : ℕ) : radTh n < 1 := by
  unfold radTh
  rw [div_lt_one (by positivity)]
  push_cast
  linarith

lemma radTh_le_one (n : ℕ) : radTh n ≤ 1 := le_of_lt (radTh_lt_one n)

lemma radTh_nonneg (n : ℕ) : 0 ≤ radTh n := le_of_lt (radTh_pos n)

lemma radTh_ge_half (n : ℕ) : 1 / 2 ≤ radTh n := by
  unfold radTh
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ))]
  push_cast
  nlinarith

lemma radTh_ge_three_quarters (n : ℕ) (hn : 1 ≤ n) : 3 / 4 ≤ radTh n := by
  unfold radTh
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ))]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at *
  nlinarith

lemma radTh_inv_le_two (n : ℕ) : (radTh n)⁻¹ ≤ 2 := by
  have hθ := radTh_pos n
  have h1 : (1 : ℝ) ≤ 2 * radTh n := by
    have := radTh_ge_half n
    linarith
  calc (radTh n)⁻¹ = 1 / radTh n := by rw [one_div]
    _ ≤ 2 := by
      rw [div_le_iff₀ hθ]
      linarith

lemma radH_apply (n : ℕ) (x : ℝ) : radH n x = x ^ (radTh n) - (1 - x) ^ (radTh n) := rfl

@[simp] lemma radH_zero (n : ℕ) : radH n 0 = -1 := by
  unfold radH
  rw [Real.zero_rpow (ne_of_gt (radTh_pos n)),
    show (1 : ℝ) - 0 = 1 by norm_num, Real.one_rpow]
  norm_num

@[simp] lemma radH_one (n : ℕ) : radH n 1 = 1 := by
  unfold radH
  rw [Real.one_rpow, show (1 : ℝ) - 1 = 0 by ring, Real.zero_rpow (ne_of_gt (radTh_pos n))]
  norm_num

@[simp] lemma radH_half (n : ℕ) : radH n (1 / 2) = 0 := by
  unfold radH
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  ring

lemma radH_strictMonoOn (n : ℕ) : StrictMonoOn (radH n) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hθ := radTh_pos n
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have h1 : x ^ (radTh n) < y ^ (radTh n) := Real.rpow_lt_rpow hx0 hxy hθ
  have h2 : (0 : ℝ) ≤ 1 - y := by linarith [hy.2]
  have h3 : 1 - y < 1 - x := by linarith
  have h4 : (1 - y) ^ (radTh n) < (1 - x) ^ (radTh n) := Real.rpow_lt_rpow h2 h3 hθ
  unfold radH
  linarith

lemma radH_injOn (n : ℕ) : Set.InjOn (radH n) (Set.Icc (0 : ℝ) 1) :=
  (radH_strictMonoOn n).injOn

lemma radH_continuousOn (n : ℕ) : ContinuousOn (radH n) (Set.Icc (0 : ℝ) 1) := by
  unfold radH
  refine ContinuousOn.sub ?_ ?_
  · exact continuous_id.continuousOn.rpow continuousOn_const
      (fun x _ => Or.inr (radTh_pos n))
  · refine ContinuousOn.rpow ?_ continuousOn_const (fun x _ => Or.inr (radTh_pos n))
    exact (continuous_const.sub continuous_id).continuousOn

lemma radH_mono_Icc (n : ℕ) {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hab : a ≤ b) : radH n a ≤ radH n b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact le_of_lt (radH_strictMonoOn n ha hb h)

/-- The inverse of `radH n` on `(-1,1)`, extended arbitrarily outside. -/
noncomputable def radInv (n : ℕ) (w : ℝ) : ℝ := by
  classical
  exact if h : ∃ x, x ∈ Set.Ioo (0 : ℝ) 1 ∧ radH n x = w then Classical.choose h else 1 / 2

/-- `radH n` takes every value in `(-1,1)` on `(0,1)`. -/
lemma radH_exists {n : ℕ} {w : ℝ} (hw1 : -1 < w) (hw2 : w < 1) :
    ∃ x, x ∈ Set.Ioo (0 : ℝ) 1 ∧ radH n x = w := by
  have hcont := radH_continuousOn n
  have hIcc : Set.Icc (radH n 0) (radH n 1) ⊆ radH n '' Set.Icc (0 : ℝ) 1 :=
    intermediate_value_Icc (by norm_num) hcont
  have hw : w ∈ Set.Icc (radH n 0) (radH n 1) := by
    rw [radH_zero, radH_one]
    exact ⟨le_of_lt hw1, le_of_lt hw2⟩
  obtain ⟨x, hx, hxw⟩ := hIcc hw
  refine ⟨x, ⟨?_, ?_⟩, hxw⟩
  · rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      rw [radH_zero] at hxw
      linarith
    · exact h
  · rcases eq_or_lt_of_le hx.2 with h | h
    · subst h
      rw [radH_one] at hxw
      linarith
    · exact h

lemma radInv_mem {n : ℕ} {w : ℝ} (hw : |w| < 1) : radInv n w ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 : -1 < w := (abs_lt.mp hw).1
  have h2 : w < 1 := (abs_lt.mp hw).2
  rw [radInv, dif_pos (radH_exists h1 h2)]
  exact (Classical.choose_spec (radH_exists h1 h2)).1

lemma radH_radInv {n : ℕ} {w : ℝ} (hw : |w| < 1) : radH n (radInv n w) = w := by
  have h1 : -1 < w := (abs_lt.mp hw).1
  have h2 : w < 1 := (abs_lt.mp hw).2
  rw [radInv, dif_pos (radH_exists h1 h2)]
  exact (Classical.choose_spec (radH_exists h1 h2)).2

/-- Uniqueness: any point of `(0,1)` where `radH n` takes the value `w` is `radInv n w`. -/
lemma radInv_eq_of {n : ℕ} {w x : ℝ} (hw : |w| < 1) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hxw : radH n x = w) : x = radInv n w := by
  have h1 : -1 < w := (abs_lt.mp hw).1
  have h2 : w < 1 := (abs_lt.mp hw).2
  refine radH_injOn n ?_ ?_ ?_
  · exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  · exact ⟨le_of_lt (radInv_mem hw).1, le_of_lt (radInv_mem hw).2⟩
  · rw [hxw, radH_radInv hw]

/-- The normalised first coordinate `x = x(w)`: a point of `(0,1)` with `radH n x = w`. -/
lemma radInv_spec_of {n : ℕ} {w : ℝ} (hw : |w| < 1) :
    radInv n w ∈ Set.Ioo (0 : ℝ) 1 ∧ radH n (radInv n w) = w :=
  ⟨radInv_mem hw, radH_radInv hw⟩

end Work.OddCurve.LowSlope
