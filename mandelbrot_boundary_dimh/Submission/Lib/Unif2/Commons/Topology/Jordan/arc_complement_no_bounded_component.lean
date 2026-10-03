import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Connected.frontier_component_compl_range
import Submission.Lib.Unif2.Commons.Topology.Brouwer.brouwer_fixed_point_closedBall

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

noncomputable section

/-- **The complement of a Jordan arc has no bounded component.**

If `β : [0,1] → ℂ` is injective (an arc) and `C` is a nonempty bounded open
preconnected set disjoint from the arc whose frontier is contained in the arc,
then contradiction: a bounded "domain" cannot be bounded by an arc alone.

The proof is the Maehara/Brouwer argument, reusing the retraction of the plane
onto an arc (`exists_retraction_of_arc`) and the Brouwer fixed point theorem on
the closed ball. -/
theorem arc_complement_no_bounded_component (β : C(Set.Icc (0:ℝ) 1, ℂ))
    (hβ : Function.Injective β)
    {C : Set ℂ} (hCop : IsOpen C) (hCne : C.Nonempty) (hCbdd : Bornology.IsBounded C)
    (hCpre : IsPreconnected C) (hsub : frontier C ⊆ Set.range β)
    (hdisj : Disjoint C (Set.range β)) : False := by
  classical
  obtain ⟨x, hxC⟩ := hCne
  have hxrng : x ∉ Set.range β := Set.disjoint_left.mp hdisj hxC
  obtain ⟨r, hrβ, hrrange⟩ := Commons.Topology.Connected.exists_retraction_of_arc hβ
  have hr_on : ∀ a ∈ Set.range β, r a = a := by
    rintro a ⟨t, rfl⟩
    exact hrβ t
  have hKrng : IsCompact (Set.range β) := isCompact_range β.continuous
  have hclbdd : Bornology.IsBounded (closure C) := hCbdd.closure
  obtain ⟨R1, hR1⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hclbdd
  obtain ⟨R2, hR2⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hKrng.isBounded
  have hR1nonneg : 0 ≤ R1 := by
    have h1 := hR1 (subset_closure hxC)
    rw [Metric.mem_closedBall, dist_self] at h1
    exact h1
  set R : ℝ := max R1 R2 + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith [le_max_left R1 R2]
  have hcl_ball : closure C ⊆ Metric.ball x R := by
    intro z hz
    have h1 := hR1 hz
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    calc dist z x ≤ R1 := h1
      _ < R := by rw [hRdef]; linarith [le_max_left R1 R2]
  have hK_ball : Set.range β ⊆ Metric.closedBall x R := by
    intro z hz
    have h1 := hR2 hz
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_closedBall]
    calc dist z x ≤ R2 := h1
      _ ≤ R := by rw [hRdef]; linarith [le_max_right R1 R2]
  set D : Set ℂ := Metric.closedBall x R
  have hcontpiece : Continuous (fun z : ℂ => if z ∈ closure C then r z else z) := by
    apply continuous_if
    · intro a ha
      exact hr_on a (hsub (frontier_closure_subset ha))
    · exact r.continuous.continuousOn
    · exact continuous_id.continuousOn
  set fp : C(ℂ, ℂ) := ⟨fun z => if z ∈ closure C then r z else z, hcontpiece⟩ with hfpdef
  set fD : C(D, ℂ) := fp.restrict D with hfDdef
  have hneD : ∀ z : D, fD z ≠ x := by
    intro z
    have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
      rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
    rw [hzval]
    by_cases hzC : z.1 ∈ closure C
    · rw [if_pos hzC]
      intro heq
      have : r z.1 ∈ Set.range β := hrrange ⟨z.1, rfl⟩
      rw [heq] at this
      exact hxrng this
    · rw [if_neg hzC]
      intro heq
      exact hzC (heq ▸ subset_closure hxC)
  have hinD : ∀ z : D, fD z ∈ D := by
    intro z
    have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
      rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
    rw [hzval]
    by_cases hzC : z.1 ∈ closure C
    · rw [if_pos hzC]
      exact hK_ball (hrrange ⟨z.1, rfl⟩)
    · rw [if_neg hzC]
      exact z.2
  have hnormne : ∀ z : D, ‖fD z - x‖ ≠ 0 :=
    fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hneD z))
  set w : D → ℂ := fun z => x + (R / ‖fD z - x‖) • (fD z - x) with hwdef
  have hwcont : Continuous w := by
    have hnorm : Continuous fun z : D => ‖fD z - x‖ := (fD.continuous.sub continuous_const).norm
    exact continuous_const.add ((continuous_const.div hnorm hnormne).smul
      (fD.continuous.sub continuous_const))
  have hw_sphere : ∀ z : D, ‖w z - x‖ = R := by
    intro z
    have heq : w z - x = (R / ‖fD z - x‖) • (fD z - x) := by rw [hwdef]; ring
    rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hRpos.le (norm_nonneg _))]
    rw [div_mul_cancel₀ _ (hnormne z)]
  have hGmem : ∀ z : D, (2 * x - w z) ∈ D := fun z => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h2 : (2 * x - w z) - x = -(w z - x) := by ring
    rw [h2, norm_neg, hw_sphere z]
  set G : C(D, D) := ⟨fun z => ⟨2 * x - w z, hGmem z⟩,
    Continuous.subtype_mk (continuous_const.sub hwcont) hGmem⟩
  obtain ⟨z, hzfix⟩ := Commons.Topology.Brouwer.brouwer_fixed_point_closedBall x hRpos G
  have hz1 : 2 * x - w z = z.1 := Subtype.ext_iff.mp hzfix
  have hwz : w z = 2 * x - z.1 := by rw [← hz1]; ring
  have hspz : ‖z.1 - x‖ = R := by
    have := hw_sphere z
    rw [hwz] at this
    rw [show (2 * x - z.1) - x = -(z.1 - x) from by ring, norm_neg] at this
    exact this
  have hz1notC : z.1 ∉ closure C := by
    intro hzc
    have h1 := hcl_ball hzc
    rw [Metric.mem_ball, dist_eq_norm, hspz] at h1
    linarith
  have hz_fd : fD z = z.1 := by
    have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
      rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
    rw [hzval, if_neg hz1notC]
  have hdir : (R / ‖z.1 - x‖) • (z.1 - x) = -(z.1 - x) := by
    have hwdef' : w z = x + (R / ‖fD z - x‖) • (fD z - x) := rfl
    have hone : (R / ‖fD z - x‖) • (fD z - x) = -(z.1 - x) := by
      have h1 : x + (R / ‖fD z - x‖) • (fD z - x) = 2 * x - z.1 := by rw [← hwdef']; exact hwz
      have h2 : (R / ‖fD z - x‖) • (fD z - x) = (2 * x - z.1) - x := by
        linear_combination h1
      rw [h2]; ring
    rw [hz_fd, hspz, div_self (ne_of_gt hRpos), one_smul] at hone
    rw [hspz, div_self (ne_of_gt hRpos), one_smul]
    exact hone
  exact Commons.Topology.Connected.smul_sub_eq_neg_false hRpos hspz hdir

end

end Commons.Topology.Jordan
