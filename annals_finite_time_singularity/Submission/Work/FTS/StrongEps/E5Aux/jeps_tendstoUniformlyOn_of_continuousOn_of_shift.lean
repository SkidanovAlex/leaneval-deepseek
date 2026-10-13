/-
Copyright: work module for the Elgindi finite-time singularity project.

# `J_ε X → X` *uniformly on compact subsets of the quadrant*

`Jeps ρ ε X` is the log-coordinate mollifier of `X` (`StrongEps/Basic.lean`); at a point
`(z,θ) ∈ Quad` it is the average of `X ∘ sPhi (z,θ)` against the rescaled kernel `Jker ρ ε`,
whose support is the ball of radius `ε`.

The pointwise statement `Jeps_tendsto` / `tendsto_Jeps_of_continuousOn` says that
`Jeps ρ (ε n) X z θ → X z θ` when `X` is continuous on the quadrant.  The content of this file is
that the convergence is **uniform on every compact `K ⊆ Quad`**:

* on a compact set, `X` is uniformly continuous (`IsCompact.uniformContinuousOn_of_continuous`
  applied to a compact halo `L = cthickening d K ⊆ Quad` of `K`, which exists because `Quad` is
  open: `IsCompact.exists_cthickening_subset_open`);
* the hypothesis `hshift` is exactly the statement that the shift `sPhi p q` is close to `p`
  *uniformly for `p ∈ K`* as soon as `‖q‖` is small;
* combining the two, the peak estimate `abs_Jeps_sub_le_of_bound_of_continuousOn` (which needs the
  profile to be within `η` of its value at the base point on the whole ball `‖q‖ ≤ ε n`) gives the
  bound `|Jeps ρ (ε n) X p - X p| ≤ η/2` for every `p ∈ K`, as soon as `ε n` is below the shift
  threshold.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.Thickening
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps_tendsto
import Submission.Work.FTS.StrongEps.Jeps_tendsto
import Submission.Work.FTS.StrongEps.E5Aux.exists_dist_sPhi_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

open scoped Real Topology
open MeasureTheory Set Filter

theorem jeps_tendstoUniformlyOn_of_continuousOn_of_shift {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {X : ℝ → ℝ → ℝ} {ε : ℕ → ℝ}
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Work.FTS.StrongEps.Quad)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.StrongEps.Quad)
    (hshift : ∀ η > 0, ∃ δ > 0, ∀ p ∈ K, ∀ q : ℝ × ℝ, ‖q‖ ≤ δ →
      dist (Work.FTS.StrongEps.sPhi p.1 p.2 q) p ≤ η) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ (ε n) X p.1 p.2)
      (fun p : ℝ × ℝ => X p.1 p.2) Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hη2 : (0 : ℝ) < η / 2 := by linarith
  -- ## A compact halo of `K` inside the open quadrant
  obtain ⟨r₁, hr₁, hL₁⟩ := hK.exists_cthickening_subset_open isOpen_Quad hKQ
  obtain ⟨r₂, hr₂, hcomp₂⟩ := hK.exists_isCompact_cthickening
  set d : ℝ := min r₁ r₂ with hddef
  have hdpos : 0 < d := by rw [hddef]; exact lt_min hr₁ hr₂
  have hdle₁ : d ≤ r₁ := by rw [hddef]; exact min_le_left _ _
  have hdle₂ : d ≤ r₂ := by rw [hddef]; exact min_le_right _ _
  have hLsub : Metric.cthickening d K ⊆ Quad :=
    (Metric.cthickening_mono hdle₁ K).trans hL₁
  have hLcomp : IsCompact (Metric.cthickening d K) :=
    hcomp₂.of_isClosed_subset Metric.isClosed_cthickening (Metric.cthickening_mono hdle₂ K)
  -- ## `X` is uniformly continuous on the halo
  obtain ⟨δc, hδcpos, hδc⟩ := Metric.uniformContinuousOn_iff.mp
    (hLcomp.uniformContinuousOn_of_continuous (hXc.mono hLsub)) (η / 2) hη2
  -- ## The shift threshold, small compared with `η/2`, `δc` and the halo radius
  set η₁ : ℝ := min (min (η / 2) δc) d / 2 with hη₁def
  have hη₁pos : 0 < η₁ := by
    rw [hη₁def]
    have h : 0 < min (min (η / 2) δc) d := lt_min (lt_min hη2 hδcpos) hdpos
    linarith
  have hη₁η : η₁ ≤ η / 2 := by
    rw [hη₁def]
    have h : min (min (η / 2) δc) d ≤ η / 2 :=
      (min_le_left (min (η / 2) δc) d).trans (min_le_left (η / 2) δc)
    linarith
  have hη₁δc : η₁ < δc := by
    rw [hη₁def]
    have h₁ : min (min (η / 2) δc) d ≤ min (η / 2) δc := min_le_left _ _
    have h₂ : min (η / 2) δc ≤ δc := min_le_right _ _
    linarith
  have hη₁d : η₁ < d := by
    rw [hη₁def]
    have h : min (min (η / 2) δc) d ≤ d := min_le_right _ _
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := hshift η₁ hη₁pos
  -- ## Eventually `ε n ≤ δ`
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ δ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hε0 δ hδpos
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos n)] at h
    exact h.le
  filter_upwards [hev] with n hεn p hp
  have hpQ : 0 < p.1 ∧ p.2 ∈ Set.Ioo 0 (π / 2) := hKQ hp
  -- ## On the ball of radius `ε n`, the shifted profile is within `η/2` of `X p`
  have hbound : ∀ q : ℝ × ℝ, ‖q‖ ≤ ε n →
      |X (Work.FTS.StrongEps.zShift p.1 q.1) (Work.FTS.StrongEps.thShift p.2 q.2)
        - X p.1 p.2| ≤ η / 2 := by
    intro q hq
    have hqδ : ‖q‖ ≤ δ := hq.trans hεn
    have hdist : dist (sPhi p.1 p.2 q) p ≤ η₁ := hδ p hp q hqδ
    have hmem : sPhi p.1 p.2 q ∈ Metric.cthickening d K :=
      Metric.mem_cthickening_of_dist_le _ p d K hp (le_of_lt (lt_of_le_of_lt hdist hη₁d))
    have hpL : p ∈ Metric.cthickening d K :=
      Metric.mem_cthickening_of_dist_le p p d K hp (by rw [dist_self]; exact hdpos.le)
    have hclose := hδc _ hmem _ hpL (lt_of_le_of_lt hdist hη₁δc)
    rw [Real.dist_eq] at hclose
    exact le_of_lt (by simpa only [sPhi, zShift, thShift] using hclose)
  -- ## The peak estimate
  have hpeak :=
    abs_Jeps_sub_le_of_bound_of_continuousOn ρ hρ hpQ.1 hpQ.2 (hεpos n) hXc hbound
  rw [Real.dist_eq, abs_sub_comm]
  linarith

end Work.FTS.StrongEps.E5Aux
