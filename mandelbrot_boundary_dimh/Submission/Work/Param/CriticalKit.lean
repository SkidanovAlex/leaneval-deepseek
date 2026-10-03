import Mathlib
import Submission.Work.Param.Basic

/-!
# PARAM: the basin of the attracting fixed point and local Koenigs solutions

This file fixes the vocabulary used by `Work.Param.critical_orbit` (the critical orbit of
`Q l x = l * x + x ^ 2` lies in the basin of `0` when `‖l‖ < 1`) and by its supporting lemmas.

* `Work.Param.Basin l y` says that the orbit of `y` under `Q l` converges to the fixed point `0`.
* `Work.Param.Good l r ψ` says that `ψ` is a normalized local solution of the Koenigs equation
  `Q l (ψ w) = ψ (l * w)` on the disc `Metric.ball 0 r` (`ψ 0 = 0`, `deriv ψ 0 = 1`).
-/

namespace Work.Param

open Filter Topology
open scoped Topology

noncomputable section

/-- The **basin of attraction of the fixed point `0`** of `Q l` (`Work.Param.Q`): the set of
points whose `Q l`-orbit converges to `0`. -/
def Basin (l : ℂ) (y : ℂ) : Prop :=
  Filter.Tendsto (fun n : ℕ => (Q l)^[n] y) Filter.atTop (nhds 0)

/-- A **normalized local solution of the Koenigs equation** for `Q l` on `Metric.ball 0 r`:
holomorphic there, fixing `0` with derivative `1`, and satisfying `Q l (ψ w) = ψ (l * w)`. -/
def Good (l : ℂ) (r : ℝ) (ψ : ℂ → ℂ) : Prop :=
  0 < r ∧ DifferentiableOn ℂ ψ (Metric.ball 0 r) ∧ ψ 0 = 0 ∧ deriv ψ 0 = 1 ∧
    (∀ w ∈ Metric.ball 0 r, Q l (ψ w) = ψ (l * w))

/-- `0` lies in the basin of `0` (the orbit of `0` is identically `0`). -/
theorem basin_zero (l : ℂ) : Basin l 0 := by
  rw [Basin]
  have h : (Q l) 0 = 0 := by simp [Q]
  simpa [Function.iterate_fixed h] using tendsto_const_nhds

/-- The basin of `0` is **backward invariant**: if `Q l x` lies in the basin, so does `x`. -/
theorem basin_of_basin_Q (l : ℂ) {x : ℂ} (h : Basin l (Q l x)) : Basin l x := by
  rw [Basin] at h ⊢
  have hshift : Filter.Tendsto (fun n : ℕ => (Q l)^[n.succ] x) Filter.atTop (nhds 0) := by
    simpa only [Function.iterate_succ_apply] using h
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (Q l)^[n] x) 1).mp (by
    simpa [Nat.succ_eq_add_one] using hshift)

end

end Work.Param
