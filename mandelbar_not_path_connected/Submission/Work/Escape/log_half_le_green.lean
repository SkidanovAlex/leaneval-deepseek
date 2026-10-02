import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.geom_le_norm_iterate
import Submission.Work.Escape.norm_le_norm_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Green function dominates `log (‖z‖ / 2)` on the escaping region

For a `MonicGrowth f d A` map with `d ≥ 2` and `z` in the escaping region `{max 2 A < ‖z‖}`, the
geometric lower bound `2 * (‖z‖ / 2) ^ d ^ n ≤ ‖(f^[n]) z‖` of `geom_le_norm_iterate` gives, after
taking logarithms,

`log (‖z‖ / 2) ≤ greenIter f d z n = d^{-n} log⁺ ‖(f^[n]) z‖`

for every `n` (the model is `≥ 2`, so `log⁺` is just `log` along the whole escaping orbit).  Passing
to the limit along `tendsto_greenIter` yields `log (‖z‖ / 2) ≤ green f d z`.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

theorem log_half_le_green (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} (hz : z ∈ escapeRegion A) : Real.log (‖z‖ / 2) ≤ green f d z := by
  have hnorm : 2 < ‖z‖ := two_lt_norm_of_mem_escapeRegion hz
  have hhalf : 1 < ‖z‖ / 2 := by linarith
  have key : ∀ n : ℕ, Real.log (‖z‖ / 2) ≤ greenIter f d z n := by
    intro n
    have hgeom := geom_le_norm_iterate f d A h hd hz n
    have hpow1 : (1 : ℝ) ≤ (‖z‖ / 2) ^ (d ^ n) := one_le_pow₀ hhalf.le
    have hmodel : (2 : ℝ) ≤ 2 * (‖z‖ / 2) ^ (d ^ n) := by nlinarith [hpow1]
    have hn1 : (1 : ℝ) ≤ ‖(f^[n]) z‖ := by linarith [hmodel, hgeom]
    have hpos : 0 < 2 * (‖z‖ / 2) ^ (d ^ n) := by linarith
    rw [greenIter_def, logPos_eq_log hn1]
    have hlog := Real.log_le_log hpos hgeom
    have hbase_ne : (‖z‖ / 2) ^ (d ^ n) ≠ 0 := pow_ne_zero _ (by linarith : (‖z‖/2) ≠ 0)
    have hlogeq : Real.log (2 * (‖z‖ / 2) ^ (d ^ n))
        = Real.log 2 + ((d : ℝ) ^ n) * Real.log (‖z‖ / 2) := by
      rw [Real.log_mul (by norm_num) hbase_ne, Real.log_pow]
      push_cast
      ring
    rw [hlogeq] at hlog
    have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hinv_nn : 0 ≤ ((d:ℝ)^n)⁻¹ := inv_nonneg.mpr (pow_nonneg hdpos.le n)
    have hdn : ((d:ℝ)^n) ≠ 0 := pow_ne_zero _ hdpos.ne'
    have hgoal_le := mul_le_mul_of_nonneg_left hlog hinv_nn
    have hsimp : ((d:ℝ)^n)⁻¹ * (Real.log 2 + ((d:ℝ)^n) * Real.log (‖z‖/2))
        = ((d:ℝ)^n)⁻¹ * Real.log 2 + Real.log (‖z‖/2) := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hdn, one_mul]
    rw [hsimp] at hgoal_le
    have hterm : 0 ≤ ((d:ℝ)^n)⁻¹ * Real.log 2 :=
      mul_nonneg hinv_nn (Real.log_nonneg (by norm_num))
    linarith [hgoal_le, hterm]
  exact ge_of_tendsto' (tendsto_greenIter f d A h hd z) key

end Work.Escape
