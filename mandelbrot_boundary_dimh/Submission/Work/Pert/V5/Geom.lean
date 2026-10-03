import Mathlib
import Submission.Work.Pert.V5.Basics

/-!
# Geometry of the corridor used by the assembly of `Phi_dev_gate_lin_v5`

The assembly compares the deviation `D z = Φm z - z` at
* `z = x + i t` (band point: `x ∈ [-(Ξ+2^10+2M), -(Ξ+2^10)]`, `|t| ≥ 4 Rde`),
* `z₀ = x₀ + i y₀` (the pin, with `Φm z₀ = -M`, `‖z₀ + M‖ ≤ Kp (1 + log (2+M))`),

by the three-legged path

  `z --(vertical at abscissa x)--> (x, s*) --(horizontal at height s*)--> (x₀, s*)
     --(vertical at abscissa x₀)--> z₀`,

with the auxiliary height `s* = y₀ ± 2^10` (same sign as `y₀`).  This file proves that

* the two vertical legs and the horizontal corridor are contained in the gate `Qm Ξ α`;
* the corridor's two margins are bounded below by the explicit quantities the horizontal
  deviation bound `Work.Pert.V5.horiz_dev_le` needs.

All the work is done by `Work.Pert.V5.band_margins` (the band is in the gate with margins
`mgB ≥ 2^10`, `mgA ≥ 16M`) and `Work.Pert.V5.slice_interval` (gate slices are intervals).
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

noncomputable section

/-- The auxiliary height of the horizontal corridor: `y₀ + 2^10` if `0 ≤ y₀`, `y₀ - 2^10`
otherwise.  It has the sign of `y₀` and `|s* - y₀| = 2^10`. -/
def sStar (y₀ : ℝ) : ℝ := if 0 ≤ y₀ then y₀ + 2 ^ 10 else y₀ - 2 ^ 10

theorem sStar_sub (y₀ : ℝ) : |sStar y₀ - y₀| = 2 ^ 10 := by
  unfold sStar
  split_ifs with h
  · rw [add_sub_cancel_left, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2^10)]
  · rw [show y₀ - 2^10 - y₀ = -(2^10 : ℝ) by ring, abs_neg,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2^10)]

theorem abs_sStar (y₀ : ℝ) : |sStar y₀| = |y₀| + 2 ^ 10 := by
  unfold sStar
  split_ifs with h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y₀ + 2^10), abs_of_nonneg h]
  · rw [abs_of_nonpos (by linarith : y₀ - 2^10 ≤ 0), abs_of_neg (by linarith : y₀ < 0)]
    ring

theorem sStar_same_sign {y₀ : ℝ} (h : y₀ ≠ 0) : 0 < sStar y₀ * y₀ := by
  unfold sStar
  split_ifs with h0
  · have : 0 < y₀ := lt_of_le_of_ne h0 (Ne.symm h)
    nlinarith [show (0:ℝ) < 2^10 by norm_num]
  · have : y₀ < 0 := lt_of_not_ge h0
    nlinarith [show (0:ℝ) < 2^10 by norm_num]

/-- **The vertical leg at a band abscissa is in the gate.** -/
theorem vert_leg_band {Ξ M : ℝ} {α : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    {x : ℝ} (hx : -(Ξ + 2 ^ 10 + 2 * M) ≤ x) (hx' : x ≤ -(Ξ + 2 ^ 10)) :
    ∀ u : ℝ, (x + u * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α := fun u =>
  (band_margins hΞ hM hInF1 hα hQAdm x u hx hx').1

/-- **The horizontal corridor at height `s` from a band abscissa to the pin's abscissa lies in
the gate**, provided both endpoints do. -/
theorem corridor_mem {Ξ : ℝ} {α : ℂ} {s x x₀ : ℝ}
    (hx : (x + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hx₀ : (x₀ + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α) :
    ∀ u ∈ Set.Icc (min x x₀) (max x x₀), (u + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α :=
  fun u hu => slice_interval hx hx₀ hu

/-- **The band point of the corridor is in the gate with the band margins.** -/
theorem corridor_band_margins {Ξ M : ℝ} {α : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    {x s : ℝ} (hx : -(Ξ + 2 ^ 10 + 2 * M) ≤ x) (hx' : x ≤ -(Ξ + 2 ^ 10)) :
    (x + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α ∧
      2 ^ 10 ≤ mgB Ξ (x + s * Complex.I) ∧ 16 * M ≤ mgA Ξ α (x + s * Complex.I) :=
  band_margins hΞ hM hInF1 hα hQAdm x s hx hx'

end

end Work.Pert.V5
