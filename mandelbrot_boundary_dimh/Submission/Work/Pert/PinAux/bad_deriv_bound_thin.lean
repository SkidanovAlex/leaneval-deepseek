import Mathlib
import Submission.Work.Pert.PinAux.CollarDefs

set_option linter.unusedVariables false

namespace Work.Pert.PinAux

open MandelDim Complex Metric Set

noncomputable section

/-!
# `Work.Pert.PinAux.bad_deriv_bound_thin`

The derivative of a Fatou coordinate is bounded on the *thin* part of the gate, i.e. on the set of
points `w` of `Qm Ξ α` whose slice is narrow at the medial point,
`minmarg Ξ α (med Ξ α w.im) < √2 Rde`, and which carry a positive margin `ρ ≤ minmarg Ξ α w`.

The proof is a compactness argument, and it uses none of the Fatou apparatus beyond the
differentiability of `Φ` on the (open) gate: the hypothesis `ρ ≤ minmarg Ξ α w` (with `ρ > 0`)
puts `w` at distance `≥ ρ/√2` from the boundary of the gate, while the thinness hypothesis
`minmarg Ξ α (med Ξ α w.im) = width Ξ α w.im / 2 < √2 Rde` bounds the height `|w.im|`, hence the
whole slice.  So the admissible set is a bounded set whose closure lies in the open gate
`Qm Ξ α`, on which `deriv Φ` is continuous.
-/

/-- `minmarg Ξ α` is continuous. -/
lemma continuous_minmarg (Ξ : ℝ) (α : ℂ) :
    Continuous fun w : ℂ => minmarg Ξ α w := by
  unfold minmarg margA margB
  fun_prop

/-- `t ↦ minmarg Ξ α (med Ξ α t)` is continuous. -/
lemma continuous_minmarg_med (Ξ : ℝ) (α : ℂ) :
    Continuous fun t : ℝ => minmarg Ξ α (med Ξ α t) := by
  unfold minmarg margA margB med xMid sliceLo sliceHi
  fun_prop

theorem bad_deriv_bound_thin {F Φ : ℂ → ℂ} {α : ℂ} {Ξ c ρ Rde : ℝ}
    (hΞ : 0 < Ξ) (hc0 : 0 ≤ c) (hρ : 0 < ρ) (hRdepos : 0 < Rde)
    (hDE : MandelDim.FatouDerivEstimate)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α)) :
    ∃ D : ℝ, 0 < D ∧ ∀ w : ℂ, w ∈ Work.Pert.Qm Ξ α → ρ ≤ Work.Pert.PinAux.minmarg Ξ α w →
      Work.Pert.PinAux.minmarg Ξ α (Work.Pert.PinAux.med Ξ α w.im) < Real.sqrt 2 * Rde →
      ‖deriv Φ w - 1‖ ≤ D := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := Work.Pert.isOpen_Qm_ Ξ α
  -- `deriv Φ` is continuous on the gate (Φ is complex-differentiable there and the gate is open)
  have hcont : ContinuousOn (deriv Φ) (Work.Pert.Qm Ξ α) :=
    ((hΦ.1).contDiffOn hQopen).continuousOn_deriv_of_isOpen hQopen le_top
  -- the carrier of the admissible points
  set K : Set ℂ :=
    {w : ℂ | ρ ≤ minmarg Ξ α w ∧ minmarg Ξ α (med Ξ α w.im) ≤ Real.sqrt 2 * Rde} with hK
  -- `K` is closed
  have hKclosed : IsClosed K := by
    rw [hK]
    exact (isClosed_le continuous_const (continuous_minmarg Ξ α)).inter
      (isClosed_le ((continuous_minmarg_med Ξ α).comp Complex.continuous_im) continuous_const)
  -- `K` is bounded: the thinness condition bounds the height, the margin condition then
  -- bounds the real part
  set B : ℝ := 2 * (Real.sqrt 2 * Rde) - (1 / α).re + 2 * Ξ with hB
  set R : ℝ := |ρ + Ξ - (1 / α).re - B| + |B - Ξ - ρ| + |B| + 1 with hR
  have hKbdd : Bornology.IsBounded K := by
    refine Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R) |>.subset ?_
    intro w hw
    rw [hK] at hw
    obtain ⟨hmin, hthin⟩ := hw
    have hmA : ρ ≤ margA Ξ α w := le_trans hmin (minmarg_le_margA Ξ α w)
    have hmB : ρ ≤ margB Ξ α w := le_trans hmin (minmarg_le_margB Ξ α w)
    rw [margA] at hmA
    rw [margB] at hmB
    -- the slice width is small
    have hwidth : width Ξ α w.im ≤ 2 * (Real.sqrt 2 * Rde) := by
      have h := minmarg_med Ξ α w.im
      rw [h] at hthin
      linarith
    rw [width_eq] at hwidth
    -- the two summands of the width are bounded by `B`
    have hsum : |w.im| + |w.im + (1 / α).im| ≤ B := by
      rw [hB]; linarith
    have him1 : |w.im| ≤ B := by linarith [hsum, abs_nonneg (w.im + (1 / α).im)]
    have him2 : |w.im + (1 / α).im| ≤ B := by linarith [hsum, abs_nonneg (w.im)]
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre_ub : w.re ≤ B - Ξ - ρ := by linarith
    have hre_lb : ρ + Ξ - (1 / α).re - B ≤ w.re := by linarith
    have hre : |w.re| ≤ |ρ + Ξ - (1 / α).re - B| + |B - Ξ - ρ| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (ρ + Ξ - (1 / α).re - B), abs_nonneg (B - Ξ - ρ)]
      · linarith [le_abs_self (B - Ξ - ρ), abs_nonneg (ρ + Ξ - (1 / α).re - B)]
    have him : |w.im| ≤ |B| := le_trans him1 (le_abs_self B)
    have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    rw [hR]
    linarith
  have hKcpt : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hKbdd⟩
  -- `K` lies in the gate
  have hKQ : K ⊆ Work.Pert.Qm Ξ α := by
    intro w hw
    rw [hK] at hw
    exact mem_Qm_iff_minmarg_pos.mpr (lt_of_lt_of_le hρ hw.1)
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn (hcont.mono hKQ)
  refine ⟨max 1 (C + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro w _hw hρw hthin
  have hwK : w ∈ K := by
    rw [hK]
    exact ⟨hρw, le_of_lt hthin⟩
  have hb : ‖deriv Φ w‖ ≤ C := hC w hwK
  calc ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖deriv Φ w‖ + 1 := by simp
    _ ≤ C + 1 := by linarith
    _ ≤ max 1 (C + 1) := le_max_right _ _

end

end Work.Pert.PinAux
