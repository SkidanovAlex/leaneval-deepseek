import Mathlib.Analysis.Complex.Exponential
import Submission.Work.FTS.StrongEps.Weights

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-! ## The elementary `z`-algebra

`w z = (1 + z)²/z² = (1 + 1/z)²`, so under `z ↦ z e^{-p}` we have
`w (z e^{-p}) = (1 + (1/z) e^{p})²`: the whole shift bound is the statement that
`1 + (1/z) e^{p} ≤ e^{|p|} (1 + 1/z)`, which holds because `e^{p} ≤ e^{|p|}` and `1 ≤ e^{|p|}`. -/

private lemma w_mul_inv (z t : ℝ) (hz : z ≠ 0) (ht : t ≠ 0) :
    Work.Spaces.w (z * t) = (1 + (1 / z) * t⁻¹) ^ 2 := by
  rw [Work.Spaces.w]; field_simp; ring

/-- **The radial weight of the `ε`-scheme is shifted by `e^{O(|p|)}`.**  With
`wtZ z = w z ^ 2`, `w z = (1 + z) ^ 2 / z ^ 2` and `zShift z p = z * Real.exp (-p)`, there is a
universal constant `C > 0` (e.g. `C = 4`) with `wtZ (zShift z p) ≤ e^{C |p|} * wtZ z` for every
`z > 0`.  This is the `p₁`-half of the weight-shift bound `wtG α (zShift z p₁) (thShift θ p₂) ≤
e^{C(|p₁|+|p₂|)} wtG α z θ` used to make the log-coordinate mollifier `J_ε` bounded on the
weighted spaces `ℋ^k`. -/
theorem wtZ_shift_le : ∃ C : ℝ, 0 < C ∧ ∀ z p : ℝ, 0 < z →
    Work.FTS.StrongEps.wtZ (Work.FTS.StrongEps.zShift z p)
      ≤ Real.exp (C * |p|) * Work.FTS.StrongEps.wtZ z := by
  refine ⟨4, by norm_num, ?_⟩
  intro z p hz
  -- `w z = (1 + 1/z)^2` and `w (z e^{-p}) = (1 + (1/z) e^{p})^2`.
  have ha : 0 ≤ 1 / z := by positivity
  have hwz : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
    rw [Work.Spaces.w]; field_simp; ring
  have hwzt : Work.Spaces.w (zShift z p) = (1 + (1 / z) * Real.exp p) ^ 2 := by
    rw [zShift, w_mul_inv z (Real.exp (-p)) hz.ne' (Real.exp_ne_zero _), Real.exp_neg,
      inv_inv]
  -- The key inequality `1 + (1/z) e^{p} ≤ e^{|p|} (1 + 1/z)`.
  have hstep : 1 + (1 / z) * Real.exp p ≤ Real.exp |p| * (1 + 1 / z) := by
    have he : Real.exp p ≤ Real.exp |p| := Real.exp_le_exp.mpr (le_abs_self p)
    have h1 : (1 : ℝ) ≤ Real.exp |p| := Real.one_le_exp (abs_nonneg p)
    have h2 : (1 / z) * Real.exp p ≤ (1 / z) * Real.exp |p| :=
      mul_le_mul_of_nonneg_left he ha
    calc 1 + (1 / z) * Real.exp p ≤ Real.exp |p| + (1 / z) * Real.exp |p| := add_le_add h1 h2
      _ = Real.exp |p| * (1 + 1 / z) := by ring
  have hexp1 : (Real.exp |p|) ^ 2 = Real.exp (2 * |p|) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hsq : (1 + (1 / z) * Real.exp p) ^ 2 ≤ Real.exp (2 * |p|) * (1 + 1 / z) ^ 2 := by
    have hnn : 0 ≤ 1 + (1 / z) * Real.exp p := by positivity
    have h := pow_le_pow_left₀ hnn hstep 2
    rw [mul_pow, hexp1] at h
    exact h
  -- Square once for `w`, then a second time for `wtZ = w ^ 2`.
  have hw : Work.Spaces.w (zShift z p) ≤ Real.exp (2 * |p|) * Work.Spaces.w z := by
    rw [hwzt, hwz]; exact hsq
  have hexp2 : (Real.exp (2 * |p|)) ^ 2 = Real.exp (4 * |p|) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hfin := pow_le_pow_left₀ (by rw [hwzt]; positivity) hw 2
  rw [mul_pow, hexp2] at hfin
  simpa [wtZ] using hfin

end Work.FTS.StrongEps
