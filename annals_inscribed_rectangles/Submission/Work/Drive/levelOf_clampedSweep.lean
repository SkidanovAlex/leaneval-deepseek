import Mathlib
import Submission.Work.Drive.clampedSweep

/-!
# The level of the clamped radial sweep, as a function of the sweep parameter

`Work.Drive.clampedSweep c ψ P` (`Submission/Work/Drive/clampedSweep.lean`) is the radial chain whose
`x 2 = 1` face is the plane `P (·, ·)` and whose `x 2 = 0` face is the shadow of that plane on the
*level* `c`.  Its radial coordinate is

> `levelOf (clampedSweep c ψ P x) = clampScale c ψ P x * levelOf (P (x 0, x 1))`,
> `clampScale c ψ P x = exp (ψ (x 2) * (log c - log (levelOf (P (x 0, x 1)))))`,

so with `r = levelOf (P (x 0, x 1)) ≠ c` (the plane does not already lie in the level `c`) the level of
the sweep is

> `r * exp (ψ (x 2) · log (c / r))`,

which equals `c` exactly when `ψ (x 2) = 1`.  Since the cutoff satisfies `ψ 0 = 1` and `ψ t < 1` for
`t > 0`, this happens exactly at the bottom face `x 2 = 0`:

> `levelOf (clampedSweep c ψ P x) = c ↔ x 2 = 0`   (for `0 ≤ x 2`).

That is the statement below.  It is the "the bottom face really is the level `c` (and nothing else
is)" input of the end contribution of the chain route, and it is the counterpart, for the *clamped*
sweep, of `clampedSweep_face_zero`.

Note the two ingredients: `levelOf_clampedSweep_mul` (the level of the sweep is the plane's level
rescaled by `clampScale`, itself a `scaleCapping` computation) and the monotonicity data
`ψ 0 = 1`, `ψ t < 1` (`t > 0`) of the cutoff, which is what pins the level down to the single face.
-/

namespace Work.Drive

noncomputable section

/-- **The level of a radial dilation**: `scaleCapping` multiplies the level by the scale. -/
lemma levelOf_scaleCapping (A : Work.Drive.Pos) (p : CappingSpace) :
    levelOf (scaleCapping A p) = (A : ℝ) * levelOf p := by
  rw [levelOf, levelOf, CapSmooth.cappingSpaceHomeoProj_scaleCapping]

/-- **The level of the clamped radial sweep** is the level of the plane rescaled by `clampScale`. -/
lemma levelOf_clampedSweep_mul (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3)) :
    levelOf (clampedSweep c ψ P x)
      = clampScale c ψ P x * levelOf (P (mk2 (x 0) (x 1))) := by
  rw [clampedSweep_apply, levelOf_scaleCapping]
  rfl

/-- The level of the clamped radial sweep is the bottom level exactly at the bottom face. -/
theorem levelOf_clampedSweep_eq_bottom_iff (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1)
    (hψlt : ∀ t : ℝ, 0 < t → ψ t < 1)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : 0 ≤ x 2)
    (hrc : levelOf (P (mk2 (x 0) (x 1))) ≠ c) :
    levelOf (clampedSweep c ψ P x) = c ↔ x 2 = 0 := by
  constructor
  · -- Forward: if the sweep sits in the level `c`, then `ψ (x 2) = 1`, hence `x 2 = 0`.
    intro h
    set r : ℝ := levelOf (P (mk2 (x 0) (x 1))) with hr_def
    have hr : 0 < r := by rw [hr_def]; exact levelOf_pos _
    have hrne : r ≠ c := by rw [hr_def]; exact hrc
    -- the level of the sweep, explicitly, as a function of `ψ (x 2)`
    have hlev : levelOf (clampedSweep c ψ P x)
        = Real.exp (ψ (x 2) * (Real.log c - Real.log r)) * r := by
      rw [levelOf_clampedSweep_mul, clampScale, hr_def]
    -- so `exp (ψ (x 2) · log (c / r)) · r = c`
    have h1 : Real.exp (ψ (x 2) * (Real.log c - Real.log r)) * r = c := by
      rw [← hlev, h]
    -- while at `ψ = 1` one gets the same right hand side
    have h2 : Real.exp (Real.log c - Real.log r) * r = c := by
      rw [Real.exp_sub, Real.exp_log hc, Real.exp_log hr, div_mul_cancel₀ c (ne_of_gt hr)]
    -- cancelling `r > 0` and injectivity of `exp` give `ψ (x 2) · (log c - log r) = log c - log r`
    have hexp : Real.exp (ψ (x 2) * (Real.log c - Real.log r))
        = Real.exp (Real.log c - Real.log r) :=
      mul_right_cancel₀ (ne_of_gt hr) (h1.trans h2.symm)
    -- and `log c ≠ log r` since `r ≠ c`, so `ψ (x 2) = 1`
    have hlogne : Real.log c - Real.log r ≠ 0 := by
      intro h0
      have hcr : Real.log c = Real.log r := sub_eq_zero.mp h0
      exact hrne ((Real.log_injOn_pos (Set.mem_Ioi.mpr hc) (Set.mem_Ioi.mpr hr) hcr).symm)
    have hψ1 : ψ (x 2) = 1 := by
      have hx2 := Real.exp_eq_exp.mp hexp
      exact mul_right_cancel₀ hlogne (by rw [hx2, one_mul])
    -- `ψ t < 1` for `t > 0` excludes `x 2 > 0`, so with `0 ≤ x 2` we get `x 2 = 0`
    by_contra hxne
    exact absurd hψ1 (ne_of_lt (hψlt (x 2) (lt_of_le_of_ne hx (Ne.symm hxne))))
  · -- Backward: at the bottom face the scale is `c / r`, so the level is `c`.
    intro hx0
    have hr : 0 < levelOf (P (mk2 (x 0) (x 1))) := levelOf_pos _
    rw [levelOf_clampedSweep_mul, clampScale, hx0, hψ0, one_mul, Real.exp_sub,
      Real.exp_log hc, Real.exp_log hr, div_mul_cancel₀ c (ne_of_gt hr)]

end

end Work.Drive
