import Mathlib
import Submission.Work.Sard.wp.Defs
import Submission.Work.Sard.rank_chart
import Submission.Work.Sard.submersion_local_form
import Submission.Work.Sard.slice_image_interior_eq_empty
import Submission.Work.Sard.block_fderiv_prodMk

namespace Work.Sard

open Set Filter
open scoped Topology ContDiff

/-- At a point where the derivative is surjective (`x` is a regular point), the critical points of a
`C^∞` map form a closed set not meeting a neighbourhood of `x`; hence their image is empty there. -/
theorem exists_open_notMem_crit_of_surjective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : E → F) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) {x : E}
    (hx : Function.Surjective (fderiv ℝ ρ x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      interior (ρ '' (V ∩ {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)})) = ∅ := by
  refine ⟨{z : E | Function.Surjective (fderiv ℝ ρ z)},
    (hρ.continuous_fderiv (by norm_num)).isOpen_preimage _
      (Work.Sard.isOpen_setOf_surjective_clm (E := E) (F := F)), hx, ?_⟩
  have hdisj : {z : E | Function.Surjective (fderiv ℝ ρ z)} ∩
      {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} = ∅ := by
    ext z; simp
  rw [hdisj, Set.image_empty, interior_empty]

theorem weakSardNonflatGlobal {m : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hE : Module.finrank ℝ E = m + 1) (hF : Module.finrank ℝ F = m)
    (IH : ∀ m' : ℕ, m' < m → Work.Sard.wp.WeakSardGlobal m')
    (ρ : E → F) (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) {x : E}
    (hx : fderiv ℝ ρ x ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      interior (ρ '' (V ∩ {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)})) = ∅ := by
  classical
  by_cases hsurj : Function.Surjective (fderiv ℝ ρ x)
  · exact exists_open_notMem_crit_of_surjective ρ hρ hsurj
  · -- `x` is a critical, non-flat point: use the chart lemma at the compact set `closedBall x 1`.
    obtain ⟨C, _hCcompact, hxC, hCint⟩ :=
      Work.Sard.rank_chart_aux (E := E) (F := F) hE hF
        (fun m' _ => Work.Sard.weakSardAt_all m') ρ hρ
        (Metric.closedBall x (1 : ℝ)) (isCompact_closedBall x (1 : ℝ)) x hsurj hx
    refine ⟨interior C ∩ interior (Metric.closedBall x (1 : ℝ)), isOpen_interior.inter isOpen_interior,
      ⟨hxC, ?_⟩, ?_⟩
    · exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (Metric.ball_mem_nhds x (by norm_num)) Metric.ball_subset_closedBall)
    · have hsub : (interior C ∩ interior (Metric.closedBall x (1 : ℝ))) ∩
          {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)}
          ⊆ ({z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} ∩ Metric.closedBall x (1 : ℝ)) ∩ C := by
        rintro z ⟨⟨hzC, hzK⟩, hzcrit⟩
        exact ⟨⟨hzcrit, interior_subset hzK⟩, interior_subset hzC⟩
      have hle : interior (ρ '' ((interior C ∩ interior (Metric.closedBall x (1 : ℝ))) ∩
            {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)}))
          ≤ interior (ρ '' (({z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} ∩
            Metric.closedBall x (1 : ℝ)) ∩ C)) := interior_mono (Set.image_mono hsub)
      rw [hCint] at hle
      exact le_bot_iff.mp hle

end Work.Sard
