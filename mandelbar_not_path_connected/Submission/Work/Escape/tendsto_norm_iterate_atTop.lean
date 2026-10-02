import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Escaping orbits diverge to infinity

For a `MonicGrowth f d A` map with `d ≥ 2`, every point of the escaping region
`escapeRegion A = {w | max 2 A < ‖w‖}` has an orbit of norms that grows to infinity.  In fact we
prove the quantitative lower bound `(‖z‖ - 1) ^ n * ‖z‖ ≤ ‖(f^[n]) z‖`: once the norm exceeds
`max 2 A`, one step of `f` multiplies the norm by at least `‖z‖ - 1 > 1`.

This is the (norm-side) escape criterion needed for the Green-function chapter.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

variable {f : ℂ → ℂ} {d : ℕ} {A : ℝ} {z : ℂ} {n : ℕ}

/-- **Quantitative escape criterion.**  If `‖z‖ > max 2 A` then the norms of the iterates grow at
least geometrically with ratio `‖z‖ - 1`:

`(‖z‖ - 1) ^ n * ‖z‖ ≤ ‖(f^[n]) z‖`. -/
theorem norm_iterate_ge_geomGrowth (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {z : ℂ} (hz : z ∈ escapeRegion A) (n : ℕ) :
    (‖z‖ - 1) ^ n * ‖z‖ ≤ ‖(f^[n]) z‖ := by
  have hz2 : 2 < ‖z‖ := two_lt_norm_of_mem_escapeRegion hz
  have hzA : A < ‖z‖ := lt_norm_of_mem_escapeRegion hz
  have hB1 : 1 ≤ ‖z‖ - 1 := by linarith
  have hB0 : 0 ≤ ‖z‖ := norm_nonneg z
  -- One step of `f` multiplies the norm by at least `‖z‖ - 1`, as long as the norm is `≥ ‖z‖`.
  have key : ∀ w : ℂ, ‖z‖ ≤ ‖w‖ → ‖w‖ * (‖z‖ - 1) ≤ ‖f w‖ := by
    intro w hw
    have hwnorm : 2 ≤ ‖w‖ := le_trans hz2.le hw
    have hAw : A < ‖w‖ := lt_of_lt_of_le hzA hw
    have hpow : ‖w‖ ^ 2 ≤ ‖w‖ ^ d := pow_le_pow_right₀ (by linarith) hd
    have hle : ‖w‖ ^ d - A ≤ ‖f w‖ := h.le_norm w
    have hlt : ‖w‖ * (‖w‖ - 1) < ‖w‖ ^ 2 - A := by nlinarith
    have hmono : ‖w‖ * (‖z‖ - 1) ≤ ‖w‖ * (‖w‖ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg w)
    linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hB_le : ‖z‖ ≤ ‖(f^[n]) z‖ := by
      have h1 : (1 : ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ hB1
      calc ‖z‖ = 1 * ‖z‖ := (one_mul _).symm
        _ ≤ (‖z‖ - 1) ^ n * ‖z‖ := mul_le_mul_of_nonneg_right h1 hB0
        _ ≤ ‖(f^[n]) z‖ := ih
    have hstep : ‖(f^[n]) z‖ * (‖z‖ - 1) ≤ ‖f ((f^[n]) z)‖ := key _ hB_le
    rw [Function.iterate_succ_apply']
    calc (‖z‖ - 1) ^ (n + 1) * ‖z‖ = ((‖z‖ - 1) ^ n * ‖z‖) * (‖z‖ - 1) := by ring
      _ ≤ ‖(f^[n]) z‖ * (‖z‖ - 1) := mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ ‖f ((f^[n]) z)‖ := hstep

theorem tendsto_norm_iterate_atTop (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {z : ℂ} (hz : z ∈ escapeRegion A) :
    Filter.Tendsto (fun n : ℕ => ‖(f^[n]) z‖) Filter.atTop Filter.atTop := by
  have hz2 : 2 < ‖z‖ := two_lt_norm_of_mem_escapeRegion hz
  have hz0 : 0 < ‖z‖ := lt_trans zero_lt_two hz2
  have h1 : 1 < ‖z‖ - 1 := by linarith
  have hpow : Tendsto (fun n : ℕ => (‖z‖ - 1) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h1
  have hmul : Tendsto (fun n : ℕ => ‖z‖ * (‖z‖ - 1) ^ n) atTop atTop :=
    hpow.const_mul_atTop hz0
  refine tendsto_atTop_mono (fun n => ?_) hmul
  rw [mul_comm]
  exact norm_iterate_ge_geomGrowth f d A h hd hz n

end Work.Escape
