import Mathlib
import Submission.Work.RPA3.InjectiveDefs
import Submission.Work.RPA3.theta_per

namespace Work.RPA3

/-- Upward step (valid for every `n : ℤ`): shifting the angle `t` by `2π` composes the tubular map
with `Tk 1`.  This is `theta_per` with `t` replaced by `t + 2πn`, together with
`2π(n+1) = 2πn + 2π`. -/
private lemma theta_shift (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) (n : ℤ) :
    theta L τ x (t + 2 * Real.pi * ((n : ℝ) + 1)) ξ
      = Tk 1 (theta L τ x (t + 2 * Real.pi * (n : ℝ)) ξ) := by
  have h := theta_per L τ x (t + 2 * Real.pi * (n : ℝ)) ξ
  have harg : (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi
      = t + 2 * Real.pi * ((n : ℝ) + 1) := by ring
  rw [← harg]
  exact h

/-- Downward step (valid for every `n : ℤ`): shifting the angle `t` by `-2π` composes the tubular
map with `Tk (-1)`.  It is the upward step at `n - 1` after applying `Tk (-1)` to both sides, using
`Tk (-1) (Tk 1 z) = z`. -/
private lemma theta_down (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) (n : ℤ) :
    theta L τ x (t + 2 * Real.pi * (((n - 1 : ℤ)) : ℝ)) ξ
      = Tk (-1) (theta L τ x (t + 2 * Real.pi * (n : ℝ)) ξ) := by
  have h := theta_shift L τ x t ξ (n - 1)
  rw [show (((n - 1 : ℤ)) : ℝ) + 1 = (n : ℝ) by push_cast; ring] at h
  have h2 : Tk (-1) (theta L τ x (t + 2 * Real.pi * (n : ℝ)) ξ)
      = theta L τ x (t + 2 * Real.pi * (((n - 1 : ℤ)) : ℝ)) ξ := by
    have hc := congrArg (Tk (-1)) h
    rwa [← Tk_add, show (-1 : ℤ) + 1 = 0 by ring, Tk_zero] at hc
  exact h2.symm

/-- The tubular map inherits the periodicity of the family in the angle `t` for arbitrary integer
multiples of `2π`: `θ(τ,x,t+2πk,ξ) = Tk k (θ(τ,x,t,ξ))`.  `theta_per` gives the case `k = 1`; this
extends it to all `k : ℤ` using `Tk_add` (`Tk (k+l) z = Tk k (Tk l z)`). -/
theorem theta_per_int (L : Work.RPA3.LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) (k : ℤ) :
    Work.RPA3.theta L τ x (t + 2 * Real.pi * k) ξ = Work.RPA3.Tk k (Work.RPA3.theta L τ x t ξ) := by
  -- Induct over `ℤ`, stepping from `0` both upwards (`n ↦ n+1`) and downwards (`n ↦ n-1`).
  refine @Int.induction_on
    (fun k => theta L τ x (t + 2 * Real.pi * (k : ℝ)) ξ = Tk k (theta L τ x t ξ)) k ?_ ?_ ?_
  · -- `k = 0`: the argument is unchanged and `Tk 0` is the identity.
    simp
  · -- `k = n + 1` (`n : ℕ`): the upward step turns the left-hand side into `Tk 1 (θ (t + 2πn))`,
    -- then the induction hypothesis and `Tk_add` identify it with `Tk (n+1) (θ t)`.
    intro i ih
    rw [Int.cast_add, Int.cast_one, theta_shift L τ x t ξ (↑i), ih, ← Tk_add]
    congr 1
    ring
  · -- `k = -n - 1` (`n : ℕ`): the downward step turns the left-hand side into
    -- `Tk (-1) (θ (t + 2π(-n)))`, then the induction hypothesis and `Tk_add` give `Tk (-n-1)`.
    intro i ih
    rw [theta_down L τ x t ξ (-(↑i : ℤ)), ih, ← Tk_add]
    congr 1
    ring

end Work.RPA3
