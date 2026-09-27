import Submission.UnifDeps
import Submission.RiemannSurface
import Submission.Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero

/-!
# The strong maximum principle for subharmonic functions on a Riemann surface

If a subharmonic function on a preconnected Riemann surface attains its maximum, it is constant.
The proof is local: in a chart around a maximum point the pullback is a function with the circle
mean-value inequality that is bounded above by its value at the centre, so the mean-value inequality
forces it to be constant on small circles around the centre; the level set is therefore both open
and closed in `X`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section MaxPrinciple

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Strong maximum principle for subharmonic functions on `X`.** -/
theorem SubharmonicOnX.eq_of_isMaxOn {u : X → ℝ} (h : SubharmonicOnX u univ) {x₀ : X}
    (hmax : ∀ x : X, u x ≤ u x₀) : ∀ x : X, u x = u x₀ := by
  have hucont : Continuous u := continuousOn_univ.mp h.1
  set S : Set X := {x : X | u x = u x₀} with hSdef
  have hSclosed : IsClosed S := isClosed_eq hucont continuous_const
  have hSne : S.Nonempty := ⟨x₀, rfl⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hxS
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hchart : SubharmonicAtChart u (chartAt ℂ x) x :=
      (SubharmonicOnXAt_iff_chartAt hxsrc).mp (h.2 x (mem_univ x))
    rw [SubharmonicAtChart] at hchart
    obtain ⟨-, ρc, hρc, htgt, hcont, hmvp⟩ := hchart
    have hball_le : ∀ y ∈ chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρc, u y = u x₀ := by
      intro y hy
      have hyc : (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) ρc := hy.2
      by_cases hxy : (chartAt ℂ x) y = (chartAt ℂ x) x
      · have hxy' : y = x := by
          have h1 : (chartAt ℂ x).symm ((chartAt ℂ x) y)
              = (chartAt ℂ x).symm ((chartAt ℂ x) x) := by rw [hxy]
          rw [(chartAt ℂ x).left_inv hy.1, (chartAt ℂ x).left_inv hxsrc] at h1
          exact h1
        rw [hxy']; exact hxS
      · set r : ℝ := dist ((chartAt ℂ x) y) ((chartAt ℂ x) x) with hrdef
        have hr : 0 < r := by
          rw [hrdef, dist_pos]
          exact fun hc => hxy hc
        have hrlt : r < ρc := by
          rw [hrdef]
          exact Metric.mem_ball.mp hyc
        have hclosed : Metric.closedBall ((chartAt ℂ x) x) r ⊆ Metric.ball ((chartAt ℂ x) x) ρc :=
          fun z hz => Metric.mem_ball.mpr (by
            linarith [Metric.mem_closedBall.mp hz, hrlt])
        have hsphere_sub : Metric.sphere ((chartAt ℂ x) x) |r| ⊆ Metric.ball ((chartAt ℂ x) x) ρc := by
          rw [abs_of_pos hr]
          exact fun z hz => hclosed (Metric.sphere_subset_closedBall hz)
        have hcenter : (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = u x₀ := by
          simp only [Function.comp_apply]
          rw [(chartAt ℂ x).left_inv hxsrc]
          exact hxS
        have hmvp' := hmvp ((chartAt ℂ x) x) (Metric.mem_ball_self hρc) r hr hclosed
        rw [hcenter] at hmvp'
        have hle : Real.circleAverage (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) r ≤ u x₀ :=
          Real.circleAverage_mono_on_of_le_circle
            ((hcont.mono (fun z hz => hclosed (Metric.sphere_subset_closedBall hz))).circleIntegrable
              (le_of_lt hr))
            (fun z _ => hmax _)
        have havg : Real.circleAverage (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) r = u x₀ :=
          le_antisymm hle hmvp'
        have hcont_f : ContinuousOn (fun w : ℂ => u x₀ - (u ∘ (chartAt ℂ x).symm) w)
            (Metric.sphere ((chartAt ℂ x) x) |r|) :=
          continuousOn_const.sub (hcont.mono hsphere_sub)
        have hnonneg : ∀ z ∈ Metric.sphere ((chartAt ℂ x) x) |r|,
            0 ≤ u x₀ - (u ∘ (chartAt ℂ x).symm) z := fun z _ => sub_nonneg.mpr (hmax _)
        have havg0 : Real.circleAverage (fun w : ℂ => u x₀ - (u ∘ (chartAt ℂ x).symm) w)
            ((chartAt ℂ x) x) r = 0 := by
          have hI1 : CircleIntegrable (fun _ : ℂ => u x₀) ((chartAt ℂ x) x) r :=
            continuousOn_const.circleIntegrable (le_of_lt hr)
          have hI2 : CircleIntegrable (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) r :=
            (hcont.mono (fun z hz => hclosed (Metric.sphere_subset_closedBall hz))).circleIntegrable
              (le_of_lt hr)
          change Real.circleAverage ((fun _ : ℂ => u x₀) - (u ∘ (chartAt ℂ x).symm))
            ((chartAt ℂ x) x) r = 0
          rw [Real.circleAverage_sub hI1 hI2, Real.circleAverage_const, havg, sub_self]
        have hzero := Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero
          hcont_f hnonneg havg0
        have hy_mem : (chartAt ℂ x) y ∈ Metric.sphere ((chartAt ℂ x) x) |r| := by
          rw [Metric.mem_sphere, abs_of_pos hr, hrdef]
        have hthis := hzero ((chartAt ℂ x) y) hy_mem
        simp only [Function.comp_apply] at hthis
        rw [(chartAt ℂ x).left_inv hy.1] at hthis
        linarith
    exact Filter.mem_of_superset
      ((chartBall_isOpen (chartAt ℂ x) ((chartAt ℂ x) x) ρc).mem_nhds
        ⟨hxsrc, Metric.mem_ball_self hρc⟩)
      hball_le
  rcases (isClopen_iff.mp ⟨hSclosed, hSopen⟩) with h | h
  · exact absurd hSne (by rw [h]; exact Set.not_nonempty_empty)
  · intro x
    have : x ∈ S := by rw [h]; exact mem_univ x
    exact this

end MaxPrinciple

end Submission
