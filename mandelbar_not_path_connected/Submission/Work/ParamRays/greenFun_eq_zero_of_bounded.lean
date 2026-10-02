/-
# The Green function vanishes on the filled Julia set

If the orbit of `w` under `T_c` is bounded then the normalized logarithms
`greenSeq c w n = 2^{-n} log⁺ ‖T_c^[n] w‖` are dominated by `2^{-n} log⁺ M`, where
`M` bounds the orbit.  The right-hand side tends to `0`, so the `limsup` defining
`greenFun` is `≤ 0`; since `greenFun` is nonnegative, it vanishes.

## Main result

* `Work.ParamRays.greenFun_eq_zero_of_bounded` : `BoundedOrbit c w → greenFun c w = 0`,
  i.e. the Green function vanishes exactly on the filled Julia set (this is the
  inclusion "filled Julia set ⊆ zero locus").
-/
import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology

namespace Work.ParamRays

/-- An a-priori bound for `greenSeq` in terms of a bound for the orbit: if
`‖orbit c w n‖ ≤ M` then `greenSeq c w n ≤ 2^{-n} log⁺ M`. -/
theorem greenSeq_le_of_norm_le {c w : ℂ} {M : ℝ} (n : ℕ)
    (hM : ‖orbit c w n‖ ≤ M) :
    greenSeq c w n ≤ ((2 : ℝ) ^ n)⁻¹ * log⁺ M := by
  rw [greenSeq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Real.posLog_le_posLog (by linarith [norm_nonneg (orbit c w n)]) hM

/-- The weights `2^{-n} log⁺ M` tend to zero. -/
theorem tendsto_inv_pow_two_mul (M : ℝ) :
    Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * log⁺ M) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => ((1 / 2 : ℝ)) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * log⁺ M) =
      fun n : ℕ => ((1 / 2 : ℝ)) ^ n * log⁺ M := by
    funext n; rw [← inv_pow]; norm_num
  rw [h2]; simpa using h1.mul_const (log⁺ M)

/-- **The Green function vanishes on bounded orbits.**  If the orbit of `w` under
`T_c` stays bounded then `greenFun c w = 0`.  Equivalently, the filled Julia set is
contained in the zero locus of the Green function. -/
theorem greenFun_eq_zero_of_bounded (c w : ℂ) (h : Work.ParamRays.BoundedOrbit c w) :
    Work.ParamRays.greenFun c w = 0 := by
  obtain ⟨M, hM⟩ := h
  refine le_antisymm ?_ (greenFun_nonneg c w)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have htend := tendsto_inv_pow_two_mul M
  have hev : ∀ᶠ n : ℕ in Filter.atTop, greenSeq c w n ≤ ε := by
    filter_upwards [htend.eventually_lt_const hε] with n hn
    have hle := greenSeq_le_of_norm_le n (hM n)
    linarith
  have := greenFun_le_of_eventually hev
  linarith

end Work.ParamRays
