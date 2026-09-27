import Mathlib
import Submission.Work.Drive.endLevelObstruction

/-!
# The radial sweep passes through every level strictly above its truncation level

`Work.Drive.clampedSweep cj ψ P` is the radial chain of `Submission/Work/Drive/clampedSweep.lean`: at
the parameter `(y 0, y 1, t)` its projective class is that of the plane point `P y`, while its radial
coordinate ("level") interpolates between the truncation level `cj` at `t = 0` (`ψ 0 = 1`) and the
plane's own level `levelOf (P y)` at `t = 1` (`ψ 1 = 0`):

> `levelOf (clampedSweep cj ψ P (radVec y t))
>    = exp (ψ t · (log cj − log (levelOf (P y)))) · levelOf (P y)`.

For a truncation level `cj` strictly below a target level `c`, itself strictly below the plane's level,
this is continuous in `t` (only `ψ` enters — the plane is evaluated at the *fixed* point `y`, so no
regularity of `P` is needed) and it takes the values `cj < c` at `t = 0` and `levelOf (P y) > c` at
`t = 1`.  The intermediate value theorem therefore supplies `t ∈ (0,1)` at which the sweep meets the
level `c`; this is the input that lets the end contribution of the chain route be truncated at a
prescribed level strictly between `cj` and the plane's level.
-/

namespace Work.Drive

theorem exists_radial_level_eq_of_lt_level
    (c cj : ℝ) (hcj : 0 < cj) (hlt : cj < c)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2)) (hr : c < Work.Drive.levelOf (P y)) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      Work.Drive.levelOf (Work.Drive.clampedSweep cj ψ P (Work.Drive.radVec y t)) = c := by
  set r : ℝ := Work.Drive.levelOf (P y) with hr_def
  have hr_pos : 0 < r := Work.Drive.levelOf_pos _
  have hcr : c < r := by rw [hr_def]; exact hr
  -- The level of the sweep along the radial line `(y 0, y 1, t)` only depends on `ψ t` and on the
  -- (fixed) level `r` of the plane point `P y`.
  have hF : ∀ t : ℝ, Work.Drive.levelOf (Work.Drive.clampedSweep cj ψ P (Work.Drive.radVec y t))
      = Real.exp (ψ t * (Real.log cj - Real.log r)) * r := by
    intro t
    rw [Work.Drive.levelOf_clampedSweep, Work.Drive.clampScale, hr_def]
    simp only [Work.Drive.radVec_apply_zero, Work.Drive.radVec_apply_one,
      Work.Drive.radVec_apply_two]
    rw [Work.Drive.mk2_eta]
  have hcont' : ContinuousOn (fun t : ℝ => Real.exp (ψ t * (Real.log cj - Real.log r)) * r)
      (Set.Icc (0:ℝ) 1) :=
    (Real.continuous_exp.comp_continuousOn (hcont.mul continuousOn_const)).mul continuousOn_const
  -- At `t = 0` the level is the truncation level, at `t = 1` it is the plane's level.
  have h0 : Real.exp (ψ 0 * (Real.log cj - Real.log r)) * r = cj := by
    rw [hψ0, one_mul, Real.exp_sub, Real.exp_log hcj, Real.exp_log hr_pos,
      div_mul_cancel₀ cj (ne_of_gt hr_pos)]
  have h1 : Real.exp (ψ 1 * (Real.log cj - Real.log r)) * r = r := by
    rw [hψ1, zero_mul, Real.exp_zero, one_mul]
  have hmem : c ∈ Set.Ioo (Real.exp (ψ 0 * (Real.log cj - Real.log r)) * r)
      (Real.exp (ψ 1 * (Real.log cj - Real.log r)) * r) := by
    rw [h0, h1]
    exact ⟨hlt, hcr⟩
  obtain ⟨t, ht, hFt⟩ := intermediate_value_Ioo (show (0:ℝ) ≤ 1 by norm_num) hcont' hmem
  exact ⟨t, ht, by rw [hF t]; exact hFt⟩

end Work.Drive
