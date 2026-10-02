import Mathlib
import Submission.Work.MRMT.QC.plane_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- The argument change (winding number, relative to the base point `0`) of the loop
`t ↦ γ t - w` is locally constant in the point `w`, as long as `w` does not lie on the loop.

Concretely: if `γ` is a closed loop on `[0,1]` avoiding `w`, then there is `δ > 0` such that for
every `w'` with `‖w' - w‖ < δ` the closed loops `t ↦ γ t - w'` and `t ↦ γ t - w` have the same
argument change (`2πk` with `k = 0` or not).

The proof takes `δ = m/2` where `m > 0` is the minimum of `t ↦ ‖γ t - w‖` on the compact interval
`[0,1]`; for such `w'` both loops are uniformly closer to each other than either is to `0`, so
`QC.hasArgChange_of_close` applies in both directions. -/
theorem hasArgChange_sub_iff_of_norm_lt {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hloop : γ 1 = γ 0) {w : ℂ} (hw : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t - w ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w' : ℂ, ‖w' - w‖ < δ →
      (Work.MRMT.QC.HasArgChange (fun t => γ t - w') 0 ↔
       Work.MRMT.QC.HasArgChange (fun t => γ t - w) 0) := by
  -- `t ↦ ‖γ t - w‖` attains a positive minimum `m` on the compact interval `[0,1]`.
  have hcont : ContinuousOn (fun t : ℝ => ‖γ t - w‖) (Set.Icc 0 1) :=
    (hγ.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hcont
  have hmpos : 0 < ‖γ t₀ - w‖ := norm_pos_iff.mpr (hw t₀ ht₀)
  refine ⟨‖γ t₀ - w‖ / 2, half_pos hmpos, ?_⟩
  intro w' hw'
  -- `w'` is still at distance `> 0` from the loop, and closer to each `γ t` than `w` is.
  have hlt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖w' - w‖ < ‖γ t - w‖ := by
    intro t ht
    have h1 : ‖γ t₀ - w‖ ≤ ‖γ t - w‖ := hmin ht
    linarith
  have hlt' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖w' - w‖ < ‖γ t - w'‖ := by
    intro t ht
    have h1 : ‖γ t₀ - w‖ ≤ ‖γ t - w‖ := hmin ht
    have h2 : ‖γ t - w‖ - ‖w' - w‖ ≤ ‖γ t - w'‖ := by
      have h3 := abs_norm_sub_norm_le (γ t - w) (w' - w)
      have heq : (γ t - w) - (w' - w) = γ t - w' := by ring
      rw [heq] at h3
      exact (abs_le.mp h3).2
    linarith
  constructor
  · intro hh
    refine Work.MRMT.QC.hasArgChange_of_close (γ := fun t => γ t - w') (γ' := fun t => γ t - w)
      hh ?_ ?_ (hγ.sub continuousOn_const) (hγ.sub continuousOn_const) ?_
    · rw [hloop]
    · rw [hloop]
    · intro t ht
      have h : (γ t - w) - (γ t - w') = w' - w := by ring
      rw [h]
      exact hlt' t ht
  · intro hh
    refine Work.MRMT.QC.hasArgChange_of_close (γ := fun t => γ t - w) (γ' := fun t => γ t - w')
      hh ?_ ?_ (hγ.sub continuousOn_const) (hγ.sub continuousOn_const) ?_
    · rw [hloop]
    · rw [hloop]
    · intro t ht
      have h : (γ t - w') - (γ t - w) = w - w' := by ring
      rw [h, norm_sub_rev]
      exact hlt t ht

end Work.MRMT.Found
