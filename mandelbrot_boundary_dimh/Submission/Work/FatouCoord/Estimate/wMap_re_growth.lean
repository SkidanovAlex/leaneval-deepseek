import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_sub_bound

/-!
# The orbit moves to the right: `Re ((wMap f)^[k] w) ≥ Re w + k/2`

The companion file `iterate_re_growth` proves the (weaker) statement
`N + k/2 ≤ Re ((wMap f)^[k] w)` for `Re w > N`.  That form is lossy: it forgets how far to
the right the orbit started, and it is therefore useless for a point `w` with `Re w ≫ N`
(for instance it does not show that the *first* iterate of such a point stays in a prescribed
half-plane, which is what all the downstream statements about `fatouCoordW` need).

Here we prove the sharp form.  From `wMap_sub_bound`,
`wMap f w = w + 1 + (1 - a)/w + O(1/w ^ 2)`; choosing the level `N` so large that
`‖1 - a‖ / ‖w‖ + C / ‖w‖ ^ 2 ≤ 1/2` there, the real part increases by at least `1/2` at every
step, and an induction gives `Re ((wMap f)^[k] w) ≥ Re w + k/2` for every `k`.
-/

namespace Work.FatouCoord.Estimate

open Work.FatouCoord
open scoped Topology
open Set Filter Metric

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-- **One step of the orbit moves `Re w` up by at least `1/2`.**  Past a large enough level
`M`, the chart dynamics satisfies `Re (wMap f v) ≥ Re v + 1/2`. -/
theorem wMap_re_step (hb : ParabolicBounds f h a r A A') :
    ∃ M : ℝ, 0 < M ∧ 1 / r < M ∧ ∀ v : ℂ, M < v.re → v.re + 1 / 2 ≤ (wMap f v).re := by
  obtain ⟨Nb, Cb, hNbpos, hCbnn, hrNb, hsub⟩ := wMap_sub_bound hb
  set M : ℝ := max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) + 2 with hMdef
  have hNbM : Nb < M := by
    rw [hMdef]
    have h1 : Nb ≤ max Nb (1 / r) := le_max_left _ _
    have h2 : max Nb (1 / r) ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) :=
      le_max_left _ _
    linarith
  have hrM : 1 / r < M := by
    rw [hMdef]
    have h1 : 1 / r ≤ max Nb (1 / r) := le_max_right _ _
    have h2 : max Nb (1 / r) ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) :=
      le_max_left _ _
    linarith
  have hM4Cb : 4 * Cb ≤ M := by
    rw [hMdef]
    have h1 : 4 * Cb ≤ max (4 * Cb) (4 * ‖(1 : ℂ) - a‖) := le_max_left _ _
    have h2 : max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)
        ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) := le_max_right _ _
    linarith
  have hM41a : 4 * ‖(1 : ℂ) - a‖ ≤ M := by
    rw [hMdef]
    have h1 : 4 * ‖(1 : ℂ) - a‖ ≤ max (4 * Cb) (4 * ‖(1 : ℂ) - a‖) := le_max_right _ _
    have h2 : max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)
        ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) := le_max_right _ _
    linarith
  have hM2 : (2 : ℝ) ≤ M := by
    rw [hMdef]
    have h1 : (0 : ℝ) ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) := by
      have h2 : Nb ≤ max Nb (1 / r) := le_max_left _ _
      have h3 : Nb ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) :=
        le_trans h2 (le_max_left _ _)
      linarith [hNbpos]
    linarith
  have hMpos : 0 < M := by linarith
  refine ⟨M, hMpos, hrM, ?_⟩
  intro v hv
  have hvM : M < ‖v‖ := lt_of_lt_of_le hv (Complex.re_le_norm v)
  have hvpos : 0 < ‖v‖ := lt_of_lt_of_le hMpos hvM.le
  have hb1 : ‖wMap f v - v - 1 - (1 - a) / v‖ ≤ Cb / ‖v‖ ^ 2 := hsub v (lt_trans hNbM hv)
  have hb2 : ‖(1 - a) / v‖ = ‖1 - a‖ / ‖v‖ := by rw [norm_div]
  have hden1 : Cb / ‖v‖ ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : 4 * Cb ≤ ‖v‖ ^ 2 := by
      have h1 : M ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith
      have h2 : 4 * Cb ≤ M ^ 2 := by nlinarith
      linarith
    linarith
  have hden2 : ‖1 - a‖ / ‖v‖ ≤ 1 / 4 := by
    rw [div_le_iff₀ hvpos]
    nlinarith
  have hsplit : wMap f v - v - 1 = (wMap f v - v - 1 - (1 - a) / v) + (1 - a) / v := by ring
  have hnorm : ‖wMap f v - v - 1‖ ≤ 1 / 2 := by
    rw [hsplit]
    calc ‖(wMap f v - v - 1 - (1 - a) / v) + (1 - a) / v‖
        ≤ ‖wMap f v - v - 1 - (1 - a) / v‖ + ‖(1 - a) / v‖ := norm_add_le _ _
      _ ≤ Cb / ‖v‖ ^ 2 + ‖1 - a‖ / ‖v‖ := by rw [hb2]; linarith
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hden1 hden2
      _ = 1 / 2 := by norm_num
  have hre : (wMap f v).re = v.re + 1 + (wMap f v - v - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]; ring
  have habs : -‖wMap f v - v - 1‖ ≤ (wMap f v - v - 1).re := by
    have h := Complex.abs_re_le_norm (wMap f v - v - 1)
    rw [abs_le] at h
    linarith [h.1]
  rw [hre]
  linarith

/-- **The chart orbit moves to the right at speed `1/2`.**  There is a level `N > 1/r > 0`
such that for `Re w > N` and every `k`, `Re ((wMap f)^[k] w) ≥ Re w + k/2`.

This is the sharp form of `Estimate.iterate_re_growth`. -/
theorem wMap_re_growth (hb : ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re → ∀ k : ℕ,
      w.re + k / 2 ≤ ((wMap f)^[k] w).re := by
  obtain ⟨M, hMpos, hrM, hstep⟩ := wMap_re_step hb
  refine ⟨M, hMpos, hrM, ?_⟩
  intro w hw k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hMk : M < ((wMap f)^[k] w).re := by
      have hk : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    have hstepk := hstep ((wMap f)^[k] w) hMk
    push_cast
    linarith

end

end Work.FatouCoord.Estimate
