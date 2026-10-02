import Mathlib
import Submission.Work.MRMT.QC.plane_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- A continuous `F : ℂ → ℂ` with `F z - z = O(1/‖z‖)` at infinity is surjective.

`Work.MRMT.QC.surjective_of_tendsto_sub_id` (module `Submission.Work.MRMT.QC.plane_surjective`,
imported) says: a continuous `F : ℂ → ℂ` with `Tendsto (fun z => F z - z) (cocompact ℂ) (𝓝 0)` is
surjective.  The decay hypothesis gives exactly that limit: given `ε > 0`, for
`‖z‖ ≥ max R (C / ε + 1)` one has `‖F z - z‖ ≤ C / ‖z‖ < ε` (for `C < 0` use `C / ‖z‖ ≤ 0 < ε`),
and `{z | ‖z‖ ≥ M}` is a neighbourhood of `cocompact ℂ` (complement of a closed ball). -/
theorem surjective_of_decay {F : ℂ → ℂ} (hcont : Continuous F) {C R : ℝ}
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) : Function.Surjective F := by
  apply Work.MRMT.QC.surjective_of_tendsto_sub_id hcont
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_iff, Filter.mem_cocompact]
  set M : ℝ := max R (max (C / ε + 1) 1) with hMdef
  have hR_le : R ≤ M := le_max_left _ _
  have hCM : C / ε + 1 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have h1M : (1 : ℝ) ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Metric.closedBall (0 : ℂ) M, isCompact_closedBall 0 M, ?_⟩
  intro z hz
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hz
  have hzM : M < ‖z‖ := not_le.mp hz
  have hzpos : 0 < ‖z‖ := lt_trans (by linarith) hzM
  have hbound : ‖F z - z‖ ≤ C / ‖z‖ := hdec z (le_trans hR_le (le_of_lt hzM))
  have hlt : C / ‖z‖ < ε := by
    rw [div_lt_iff₀ hzpos]
    have h2 : ε * (C / ε + 1) = C + ε := by
      field_simp
    have h3 : ε * (C / ε + 1) ≤ ε * M :=
      mul_le_mul_of_nonneg_left hCM (le_of_lt hε)
    have h4 : ε * M < ε * ‖z‖ := mul_lt_mul_of_pos_left hzM hε
    linarith
  simp only [Set.mem_setOf_eq, dist_eq_norm, sub_zero]
  exact lt_of_le_of_lt hbound hlt

end Work.MRMT.Found
