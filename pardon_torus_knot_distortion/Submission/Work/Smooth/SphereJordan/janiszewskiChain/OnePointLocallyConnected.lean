import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.janiszewskiChain.SphereDisjoint
/-! # Copy of `Submission/Work/JordanSeparation/onePoint_locallyConnected.lean` under the namespace `Work.Smooth.SphereJordan.Chain`

Duplicate of the team module `Submission/Work/JordanSeparation/onePoint_locallyConnected.lean`, with the import of
`Submission.Work.Smooth.SphereJordan.janiszewskiConnectedInter` replaced by the
namespace-local `...janiszewskiChain.DisjointPlane`, so that the chain can be imported
by `janiszewskiConnectedInter.lean` itself without an import cycle. -/


/-!
# Local connectedness of the Riemann sphere

The one-point compactification `OnePoint ℂ = RiemannSphere` is locally connected: neighbourhoods
of a finite point contain balls, neighbourhoods of `∞` contain complements of (compact) closed
balls, which are preconnected because they are obtained from the preconnected set
`{z | R < ‖z‖}` by adjoining a point of its closure.
-/

namespace Work.Smooth.SphereJordan.Chain

open Set Filter
open scoped OnePoint _root_.Topology

/-- Adjoining a point of the closure of a preconnected set keeps it preconnected. -/
theorem isPreconnected_insert_of_mem_closure {α : Type*} [TopologicalSpace α] {S : Set α} {x : α}
    (hS : IsPreconnected S) (hx : x ∈ closure S) : IsPreconnected (insert x S) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv hdisj
  have hSuv : S ⊆ u ∪ v := (subset_insert x S).trans huv
  have hSdisj : S ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem] at hdisj ⊢
    intro y hy
    exact hdisj y ⟨Or.inr hy.1, hy.2⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hS) u v hu hv hSuv hSdisj with h | h
  · left
    rw [insert_subset_iff]
    exact ⟨hu.closure_eq ▸ closure_mono h hx, h⟩
  · right
    rw [insert_subset_iff]
    exact ⟨hv.closure_eq ▸ closure_mono h hx, h⟩

/-- For every real `r` there is a complex number of norm greater than `r`. -/
theorem exists_norm_gt_complex (r : ℝ) : ∃ w : ℂ, r < ‖w‖ := by
  refine ⟨((|r| + 1 : ℝ) : ℂ), ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith [le_abs_self r]

/-- **The Riemann sphere is locally connected.** -/
instance locallyConnectedSpace_onePoint : LocallyConnectedSpace (OnePoint ℂ) := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  by_cases hx : x = ∞
  · subst hx
    obtain ⟨s, ⟨hsc, hsk⟩, hsU⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hU
    obtain ⟨R₀, hR₀⟩ := hsk.isBounded.subset_closedBall (0 : ℂ)
    set R : ℝ := max R₀ 0 with hRdef
    have hRge : R₀ ≤ R := le_max_left _ _
    have hRnn : 0 ≤ R := le_max_right _ _
    have hpre : IsPreconnected (OnePoint.some '' ({z : ℂ | R < ‖z‖} : Set ℂ)) :=
      (Work.Smooth.SphereJordan.Chain.isPreconnected_lt_norm R hRnn).image OnePoint.some
        OnePoint.continuous_coe.continuousOn
    have hcl : (∞ : OnePoint ℂ) ∈ closure (OnePoint.some '' ({z : ℂ | R < ‖z‖} : Set ℂ)) := by
      rw [mem_closure_iff]
      intro O hO hOinf
      obtain ⟨s', ⟨hs'c, hs'k⟩, hs'O⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp (hO.mem_nhds hOinf)
      obtain ⟨R₁, hR₁⟩ := hs'k.isBounded.subset_closedBall (0 : ℂ)
      obtain ⟨w, hw⟩ := exists_norm_gt_complex (max (max R R₁) 0)
      refine ⟨(w : OnePoint ℂ), hs'O (Or.inl ⟨w, ?_, rfl⟩), ⟨w, ?_, rfl⟩⟩
      · simp only [Set.mem_compl_iff]
        intro hws'
        have h1 : w ∈ Metric.closedBall (0 : ℂ) R₁ := hR₁ hws'
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        linarith [le_trans (le_max_right R R₁) (le_max_left (max R R₁) 0), h1, hw]
      · exact lt_of_le_of_lt (le_trans (le_max_left R R₁) (le_max_left (max R R₁) 0)) hw
    set V : Set (OnePoint ℂ) := insert ∞ (OnePoint.some '' ({z : ℂ | R < ‖z‖} : Set ℂ)) with hVdef
    have hVmem : V ∈ 𝓝 ∞ := by
      rw [hVdef]
      refine Filter.mem_of_superset
        (x := OnePoint.some '' (Metric.closedBall (0 : ℂ) R)ᶜ ∪ {∞}) ?_ ?_
      · exact OnePoint.hasBasis_nhds_infty.mem_iff.mpr
          ⟨Metric.closedBall (0 : ℂ) R,
            ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩, subset_rfl⟩
      · rintro w (hw | rfl)
        · rcases hw with ⟨u, hu, rfl⟩
          refine Or.inr ⟨u, ?_, rfl⟩
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hu
          exact hu
        · exact Or.inl rfl
    refine ⟨V, hVmem, ?_, ?_⟩
    · rw [hVdef]
      exact isPreconnected_insert_of_mem_closure hpre hcl
    · intro w hw
      rw [hVdef] at hw
      rcases hw with rfl | ⟨u, hu, rfl⟩
      · exact hsU (Or.inr rfl)
      · refine hsU (Or.inl ⟨u, ?_, rfl⟩)
        simp only [Set.mem_compl_iff]
        intro hus
        have h1 : u ∈ Metric.closedBall (0 : ℂ) R₀ := hR₀ hus
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : R < ‖u‖ := hu
        linarith
  · obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hx
    have hW : (OnePoint.some ⁻¹' U) ∈ 𝓝 z := by
      rw [OnePoint.nhds_coe_eq] at hU
      exact Filter.mem_map.mp hU
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
    refine ⟨OnePoint.some '' Metric.ball z ε, ?_, ?_, ?_⟩
    · rw [OnePoint.nhds_coe_eq, Filter.mem_map]
      exact Filter.mem_of_superset (Metric.ball_mem_nhds z hε)
        (by rintro u hu; exact ⟨u, hu, rfl⟩)
    · exact (convex_ball z ε).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    · rintro w ⟨u, hu, rfl⟩
      exact hεW hu

end Work.Smooth.SphereJordan.Chain
