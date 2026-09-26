import Mathlib
import Submission.Work.SG.realize_defs

/-! # Coordinate bound for a lattice vector shifted by a motion

If the Euclidean motion `x ↦ (M A M⁻¹) x + M w` translated by an integral vector `M n`
moves `x` by at most `ε`, then the `j`-th coordinate of `M n` is controlled by `ε`
plus the `j`-th coordinate of the "defect" vector `M A M⁻¹ x + M w - x`.

This is the elementary estimate used to bound integral vectors by the distance of the
corresponding motion from a fixed point. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

theorem absCoord_le_of_dist_le (M : Work.SG.RMat) (A : Work.SG.IMat)
    (hO : Matrix.transpose (Work.SG.oConj M A) * (Work.SG.oConj M A) = 1)
    (w : Fin 3 → ℝ) (x : LeanEval.Geometry.SpaceGroupsProblem.E 3) (ε : ℝ)
    (n : Fin 3 → ℤ)
    (h : dist (Work.SG.gOf M A hO (w + Work.SG.intVec n) x) x ≤ ε) (j : Fin 3) :
    |(Matrix.mulVec M (Work.SG.intVec n)) j| ≤
      ε + |(Matrix.mulVec (Work.SG.oConj M A) x.ofLp + Matrix.mulVec M w - x.ofLp) j| := by
  -- the displacement `d = gOf ... x - x` is small
  set d : E 3 := Work.SG.gOf M A hO (w + Work.SG.intVec n) x - x with hd
  set v : Fin 3 → ℝ :=
    Matrix.mulVec (Work.SG.oConj M A) x.ofLp + Matrix.mulVec M w - x.ofLp with hv
  set c : Fin 3 → ℝ := Matrix.mulVec M (Work.SG.intVec n) with hc
  -- each coordinate of `d` is bounded by the norm of `d`, hence by `ε`
  have hdco : |d j| ≤ ε := by
    have h' : ‖Work.SG.gOf M A hO (w + Work.SG.intVec n) x - x‖ ≤ ε := by
      rwa [dist_eq_norm] at h
    have h1 : ‖d‖ ≤ ε := by rw [hd]; exact h'
    calc |d j| = ‖d j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖d‖ := PiLp.norm_apply_le d j
      _ ≤ ε := h1
  -- compute the `j`-th coordinate of the displacement
  have hdecomp : d j = v j + c j := by
    have hdLp : d.ofLp = Matrix.mulVec (Work.SG.oConj M A) x.ofLp
        + Matrix.mulVec M (w + Work.SG.intVec n) - x.ofLp := by
      rw [hd]
      simp only [Work.SG.gOf_apply, WithLp.ofLp_sub, WithLp.ofLp_add]
    show d.ofLp j = v j + c j
    rw [hdLp]
    simp only [v, c, Matrix.mulVec_add, Pi.add_apply, Pi.sub_apply]
    ring
  have hcj : c j = d j - v j := by
    rw [hdecomp]; ring
  calc |c j| = |d j - v j| := by rw [hcj]
    _ ≤ |d j| + |v j| := by
        have := abs_add_le (d j) (-(v j)); simpa [sub_eq_add_neg] using this
    _ ≤ ε + |v j| := add_le_add_left hdco _
    _ = ε + |(Matrix.mulVec (Work.SG.oConj M A) x.ofLp + Matrix.mulVec M w - x.ofLp) j| := by
        rw [hv]

end Work.SG
