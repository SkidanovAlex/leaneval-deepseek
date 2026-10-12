import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `norm_ge_of_bsWin_ne_zero`: the moving window vanishes outside the radius of `z`

The moving window `bsWin ℓ u` is the bump `chiScale ℓ (x − ℓ•u)`, whose support is contained in
the ball of radius `ℓ/2` around `ℓ•u` (`Submission.BoseGases.chiScale_support_le`).  Hence if
`bsWin ℓ u z ≠ 0` then `‖z − ℓ•u‖ ≤ ℓ/2`, so by the reverse triangle inequality

    `‖z‖ ≥ ‖ℓ•u‖ − ‖z − ℓ•u‖ ≥ ℓ‖u‖ − ℓ/2 ≥ ℓ‖u‖ − ℓ ≥ Rψ`,

the last step being the hypothesis `Rψ + ℓ ≤ ℓ‖u‖`.  Thus the whole ball of radius `Rψ` around
the origin is contained in the set where the window vanishes. -/
namespace Work.BSKinetic.Decomp

open Submission.BoseGases

theorem norm_ge_of_bsWin_ne_zero {ℓ Rψ : ℝ} (hℓ : 0 < ℓ) {u z : EuclideanSpace ℝ (Fin 3)}
    (hu : Rψ + ℓ ≤ ℓ * ‖u‖) (hz : Work.BSKinetic.bsWin ℓ u z ≠ 0) :
    Rψ ≤ ‖z‖ := by
  -- The window factorises as `chiScale ℓ` applied to `z - ℓ•u`, so it vanishes off the ball of
  -- radius `ℓ/2` around `ℓ•u`.
  have hw : chiScale ℓ (z - ℓ • u) ≠ 0 := hz
  have hsupp : ‖z - ℓ • u‖ ≤ ℓ / 2 := chiScale_support_le hℓ hw
  -- `‖ℓ•u‖ = ℓ‖u‖`.
  have hnormu : ‖ℓ • u‖ = ℓ * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
  -- Reverse triangle inequality: `‖ℓ•u‖ ≤ ‖z‖ + ‖z - ℓ•u‖`.
  have htri : ‖ℓ • u‖ ≤ ‖z‖ + ‖z - ℓ • u‖ := by
    have h := norm_add_le z (ℓ • u - z)
    rw [add_sub_cancel] at h
    rwa [norm_sub_rev (ℓ • u) z] at h
  -- Hence `‖z‖ ≥ ℓ‖u‖ - ℓ/2`.
  have hzlb : ℓ * ‖u‖ - ℓ / 2 ≤ ‖z‖ := by
    have := htri
    rw [hnormu] at this
    linarith
  -- The hypothesis gives `Rψ ≤ ℓ‖u‖ - ℓ`, and `ℓ/2 ≤ ℓ`.
  have hu' : Rψ ≤ ℓ * ‖u‖ - ℓ := by linarith
  have hle : ℓ * ‖u‖ - ℓ ≤ ℓ * ‖u‖ - ℓ / 2 := by linarith
  linarith

end Work.BSKinetic.Decomp
