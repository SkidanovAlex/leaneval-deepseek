/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# Support of the invariant Beltrami coefficient `glueMu`

The invariant coefficient of the glued map is the pull-back of `0` along the orbit until the
first time the orbit reaches the far region `{‖z‖ ≥ R}`:

`glueMu F R z = (pullRev · F)^[n z] 0 z`, where `n z` is the first hitting time of `{‖z‖ ≥ R}`,
and `0` on the non-escaping set.

Its fundamental support property is that it vanishes *outside* the closed ball of radius `R`:
a point `z` with `‖z‖ > R` is already in the far region, so its first hitting time is `0` and
the coefficient is the pull-back of `0` by zero steps, i.e. `0`.  (In fact the support is
contained in the *open* ball of radius `R`; the statement below is the weaker closed-ball
version requested by the gluing assembly.)
-/
import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- The invariant coefficient `glueMu F R` vanishes at every point that already lies in the far
region `{‖z‖ ≥ R}`: such a point hits the region at time `0`. -/
theorem glueMu_eq_zero_of_le_norm {F : ℂ → ℂ} {R : ℝ} {z : ℂ} (hz : R ≤ ‖z‖) :
    glueMu F R z = 0 := by
  have hspec : R ≤ ‖(F^[0]) z‖ := by simpa using hz
  have h : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖ := ⟨0, hspec⟩
  rw [glueMu, dite_eq_left h, (Nat.find_eq_zero h).mpr hspec]
  simp [pullIter]

/-- The support of the invariant coefficient of the glued map is contained in the closed ball of
radius `R`. -/
theorem support_glueMu_subset {F : ℂ → ℂ} {R : ℝ} (hW : ∀ z : ℂ, R ≤ ‖z‖ → R ≤ ‖F z‖) :
    Function.support (Work.FBif.glueMu F R) ⊆ Metric.closedBall 0 R := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hle
  push Not at hle
  exact (Function.mem_support.mp hz) (glueMu_eq_zero_of_le_norm (le_of_lt hle))

end Work.FBif
