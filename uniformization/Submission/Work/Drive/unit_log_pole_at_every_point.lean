import Mathlib
import Submission.Work.Drive.weakcase_deps
import Submission.Work.Drive.extremal_zero_factorization
import Submission.Work.Drive.unitPoleMember

/-!
# A unit logarithmic pole at every point of the extremal family

`Work.Drive.unit_log_pole_at_every_point`: if the extremal family at `y` contains a non-zero member
then there is a positive harmonic function on `X \ {y}` with a *unit* logarithmic pole at `y`.

The proof splits in three steps.

* `Work.Drive.extremal_zero_factorization` (local data at the zero): the member `h` vanishes at `y`
  to a finite order `k ≥ 1`, and in the preferred chart at `y` one has
  `h ∘ c.symm = (· - a)^k · ψ` on a chart ball `B(a,r)`, with `m ≤ ‖ψ‖ ≤ M` there; shrinking the
  barrier radius `ρ ≤ r` so that `M ρ^k ≤ 1` makes `-(1/k) log ‖h‖` dominate the clamped
  logarithmic barrier.
* `Work.Drive.unitPoleMember` (the sweep member with a unit pole): the function obtained by
  clamping `-(1/k) log ‖h‖` away from `y` is a member of the sweep family of `greenBarrier y ρ` and
  is bounded by `log (1/‖c · - a‖) + C` near `y`.
* the sweep `E := sweep (greenBarrier y ρ) (univ \ {y})` itself is then positive, harmonic off `y`
  (`sweep_greenBarrier_pos`, `sweep_harmonic`) and its pole has coefficient exactly one: it
  dominates the barrier (`E ≥ log ρ + log (1/‖c · - a‖)`) and is dominated by the member above.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Filter Set Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

theorem unit_log_pole_at_every_point {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {y : X} {h : X → ℂ}
    (hh : h ∈ Submission.extremalFamily y) (hne : ∃ x : X, h x ≠ 0) :
    ∃ E : X → ℝ, (∀ x : X, x ≠ y → 0 < E x) ∧
      Submission.HarmonicOnX E (Set.univ \ {y}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {y}) y E := by
  obtain ⟨ρ, r, k, ψ, M, m, hρ, hρr, hk, hM, hm, hmM, hsubr, hMρ, hfac, hψ⟩ :=
    extremal_zero_factorization (y := y) (h := h) hh hne
  have hsubρ : Metric.closedBall ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target :=
    (Metric.closedBall_subset_closedBall hρr).trans hsubr
  obtain ⟨v, C₁, hv, hvbound⟩ :=
    unitPoleMember (y := y) (h := h) hh.1 hh.2.1 hh.2.2 hρ hρr hk hM hm hmM hsubr hMρ hfac hψ
  have hneSF : (Submission.sweepFamily (Submission.greenBarrier y ρ) (Set.univ \ {y})).Nonempty :=
    Work.SimplyConnected.ABS.sweepFamily_greenBarrier_nonempty hρ hsubρ hh hne
  refine ⟨Submission.sweep (Submission.greenBarrier y ρ) (Set.univ \ {y}), ?_, ?_, ?_⟩
  · intro x hx
    exact Submission.sweep_greenBarrier_pos hρ hsubρ hneSF x ⟨mem_univ x, hx⟩
  · exact Submission.sweep_harmonic (Submission.isOpen_univ_diff_singleton y)
      (Submission.subharmonicOnX_greenBarrier hρ hsubρ) hneSF
  · refine ⟨max |Real.log ρ| |C₁|,
      Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ,
      Submission.chartBall_greenBarrier_mem_nhds hρ, ?_⟩
    intro x hxV _ hxne
    have hxsrc : x ∈ (chartAt ℂ y).source := hxV.1
    have hxball : ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖ < ρ := by
      have h := hxV.2
      simp only [Set.mem_preimage] at h
      rwa [Metric.mem_ball, dist_eq_norm] at h
    have hcx_ne : (chartAt ℂ y) x ≠ (chartAt ℂ y) y := by
      intro hcon
      exact hxne ((chartAt ℂ y).injOn hxsrc (mem_chart_source ℂ y) hcon)
    have hnormpos : 0 < ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hcx_ne)
    have hxU : x ∈ (Set.univ \ {y} : Set X) := ⟨mem_univ x, hxne⟩
    have hGval : Submission.greenBarrier y ρ x
        = Real.log (ρ / ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖) := by
      rw [Submission.greenBarrier_apply, Submission.chartLogClamp_of_mem hxV]
    have hle : Submission.sweep (Submission.greenBarrier y ρ) (Set.univ \ {y}) x ≤ v x :=
      Submission.sweep_le_of_mem hv hxU
    have hge : Submission.greenBarrier y ρ x
        ≤ Submission.sweep (Submission.greenBarrier y ρ) (Set.univ \ {y}) x :=
      Submission.barrier_le_sweep hneSF hxU
    have hlow : Real.log ρ
        ≤ Submission.sweep (Submission.greenBarrier y ρ) (Set.univ \ {y}) x
          + Real.log ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖ := by
      have hlog : Real.log (ρ / ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖)
          = Real.log ρ - Real.log ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖ :=
        Real.log_div (ne_of_gt hρ) (ne_of_gt hnormpos)
      rw [hGval, hlog] at hge
      linarith
    have hup : Submission.sweep (Submission.greenBarrier y ρ) (Set.univ \ {y}) x
        + Real.log ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖ ≤ C₁ := by
      have hb := hvbound x hxV hxne
      linarith
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : |Real.log ρ| ≤ max |Real.log ρ| |C₁| := le_max_left _ _
      have h2 : -(|Real.log ρ|) ≤ Real.log ρ := neg_abs_le _
      linarith
    · have h1 : C₁ ≤ |C₁| := le_abs_self _
      have h2 : |C₁| ≤ max |Real.log ρ| |C₁| := le_max_right _ _
      linarith

end Work.Drive
