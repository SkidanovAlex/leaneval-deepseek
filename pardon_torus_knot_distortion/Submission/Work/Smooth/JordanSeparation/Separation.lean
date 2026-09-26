import Mathlib
import Submission.Work.Smooth.JordanSeparation.AtMostTwo
import Submission.Work.Smooth.JordanSeparation.Jump
import Submission.Work.Smooth.JordanSeparation.Index
import Submission.Work.Smooth.JordanSeparation.nonempty_planeSeparation

/-!
# Jordan separation for a simple immersed closed plane curve

This file assembles the two halves of the Jordan curve theorem for a `C¹` immersed simple closed
plane curve `c : SmoothPlaneCurve` (`c.IsImmersion`, `c.toPlaneCurve.IsSimple`):

* **at most two components**: `atMostTwo_connectedComponentIn` (`AtMostTwo.lean`);
* **at least two components**: `exists_two_components`, because the index `ind c` takes different
  values at the two points `c.γ 0 ± s·normalField c 0` for small `s > 0` (`ind_jump`), hence these
  two points lie in different connected components of `c.traceᶜ` (`ind_const_on_preconnected`).

The main results are

* `exists_two_components`;
* `jordanSeparation` — `Nonempty (PlaneSeparation c.toPlaneCurve)`, i.e. the hypothesis
  `Work.Smooth.Jordan.JordanInput` for `c.toPlaneCurve` (up to the immersion hypothesis);
* `ind_eq_zero_of_mem_U` — the index vanishes on the unbounded side;
* `ind_abs_eq_one_of_mem_V` — the index has modulus `1` on the bounded side.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **At least two components.**  For a `C¹` immersed simple closed plane curve there are two
points off the curve lying in different connected components of the complement of the trace. -/
theorem exists_two_components (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) :
    ∃ x y : ℂ, x ∉ c.trace ∧ y ∉ c.trace ∧
      connectedComponentIn c.traceᶜ x ≠ connectedComponentIn c.traceᶜ y := by
  obtain ⟨δ, hδ, hjump⟩ := ind_jump c himm hs
  set s : ℝ := δ / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsd : s < δ := by rw [hsdef]; linarith
  obtain ⟨hpos, hneg, hsub⟩ := hjump s hs0 hsd
  refine ⟨c.γ 0 + (s : ℂ) * normalField c 0, c.γ 0 - (s : ℂ) * normalField c 0, hpos, hneg, ?_⟩
  intro heq
  have hpre : IsPreconnected (connectedComponentIn c.traceᶜ (c.γ 0 + (s : ℂ) * normalField c 0)) :=
    isPreconnected_connectedComponentIn
  have hsub' : connectedComponentIn c.traceᶜ (c.γ 0 + (s : ℂ) * normalField c 0) ⊆ c.traceᶜ :=
    connectedComponentIn_subset _ _
  have hmem1 : c.γ 0 + (s : ℂ) * normalField c 0 ∈
      connectedComponentIn c.traceᶜ (c.γ 0 + (s : ℂ) * normalField c 0) :=
    mem_connectedComponentIn hpos
  have hmem2 : c.γ 0 - (s : ℂ) * normalField c 0 ∈
      connectedComponentIn c.traceᶜ (c.γ 0 + (s : ℂ) * normalField c 0) := by
    rw [heq]
    exact mem_connectedComponentIn hneg
  have hc := ind_const_on_preconnected c hpre hsub' hmem1 hmem2
  rw [hc] at hsub
  linarith

/-- A point off the trace of arbitrarily large norm. -/
theorem exists_norm_gt_of_notMem_trace (c : PlaneCurve) (R : ℝ) :
    ∃ x : ℂ, x ∉ c.trace ∧ R < ‖x‖ := by
  obtain ⟨M, hM⟩ := c.isCompact_trace.isBounded.exists_norm_le
  set A : ℝ := max (max M R) 0 + 1 with hA
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hnorm : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := by
    intro r; rw [Complex.norm_real, Real.norm_eq_abs]
  refine ⟨((A : ℝ) : ℂ), ?_, ?_⟩
  · intro hmem
    have h1 : ‖(((A : ℝ) : ℂ))‖ ≤ M := hM _ hmem
    rw [hnorm, abs_of_nonneg hA0] at h1
    have : M ≤ A - 1 := by
      rw [hA]; linarith [le_max_left M R, le_max_left (max M R) (0:ℝ)]
    linarith
  · rw [hnorm, abs_of_nonneg hA0]
    have : R ≤ A - 1 := by
      rw [hA]; linarith [le_max_right M R, le_max_left (max M R) (0:ℝ)]
    linarith

/-- **Jordan separation for a simple immersed closed plane curve.**

`Work.Smooth.Jordan.JordanInput c.toPlaneCurve` holds for a `C¹` curve `c` which is an immersion
and simple: the complement of its trace is the disjoint union of two non-empty preconnected open
sets, one of them bounded. -/
theorem jordanSeparation (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) : Nonempty (PlaneSeparation c.toPlaneCurve) :=
  nonempty_planeSeparation c.toPlaneCurve hs
    (fun x y z hx hy hz => atMostTwo_connectedComponentIn c himm hs hx hy hz)
    (exists_two_components c himm hs)

/-- **The index vanishes on the unbounded side.**  For any Jordan separation `S` of a simple
immersed closed plane curve, the index is `0` on the unbounded side `S.U`. -/
theorem ind_eq_zero_of_mem_U (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} {x : ℂ} (hx : x ∈ S.U) :
    ind c x = 0 := by
  refine ind_eq_zero_of_unbounded c S.preconn_U ?_ ?_ x hx
  · intro z hz
    rw [← S.union_eq]
    exact Or.inl hz
  · intro R
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp S.bounded_V
    obtain ⟨z, hz, hzR⟩ := exists_norm_gt_of_notMem_trace c.toPlaneCurve (max R r)
    have hz' : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hz
    rcases hz' with h | h
    · exact absurd hzR (not_lt.mpr (le_trans (hcon z h) (le_max_left R r)))
    · have := hr h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact absurd hzR (not_lt.mpr (le_trans this (le_max_right R r)))

/-- **The index has modulus `1` on the bounded side.**  For any Jordan separation `S` of a simple
immersed closed plane curve, the index at a point of the bounded side `S.V` is `±1`. -/
theorem ind_abs_eq_one_of_mem_V (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} {y : ℂ} (hy : y ∈ S.V) :
    |ind c y| = 1 := by
  obtain ⟨δ, hδ, hjump⟩ := ind_jump c himm hs
  set s : ℝ := δ / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsd : s < δ := by rw [hsdef]; linarith
  obtain ⟨hpos, hneg, hsub⟩ := hjump s hs0 hsd
  have hmem : ∀ z : ℂ, z ∉ c.trace → z ∈ S.U ∪ S.V := fun z hz => by
    rw [S.union_eq]; exact hz
  have hzero : ∀ z ∈ S.U, ind c z = 0 := fun z hz => ind_eq_zero_of_mem_U c himm hs hz
  have hconstV : ∀ z₁ ∈ S.V, ∀ z₂ ∈ S.V, ind c z₁ = ind c z₂ :=
    fun z₁ h₁ z₂ h₂ => ind_const_on_preconnected c S.preconn_V (fun w hw => by
      rw [← S.union_eq]; exact Or.inr hw) h₁ h₂
  have hne : ind c (c.γ 0 + (s : ℂ) * normalField c 0) ≠
      ind c (c.γ 0 - (s : ℂ) * normalField c 0) := by
    intro heq
    rw [heq] at hsub
    linarith
  have key : ind c y = 1 ∨ ind c y = -1 := by
    have hnotbothV : ¬ (c.γ 0 + (s : ℂ) * normalField c 0 ∈ S.V ∧
        c.γ 0 - (s : ℂ) * normalField c 0 ∈ S.V) := by
      rintro ⟨h1, h2⟩
      exact hne (hconstV _ h1 _ h2)
    have hnotbothU : ¬ (c.γ 0 + (s : ℂ) * normalField c 0 ∈ S.U ∧
        c.γ 0 - (s : ℂ) * normalField c 0 ∈ S.U) := by
      rintro ⟨h1, h2⟩
      exact hne (by rw [hzero _ h1, hzero _ h2])
    have h1 := hmem _ hpos
    have h2 := hmem _ hneg
    rcases h1 with h1U | h1V
    · have h2V : c.γ 0 - (s : ℂ) * normalField c 0 ∈ S.V := by
        rcases h2 with h | h
        · exact absurd ⟨h1U, h⟩ hnotbothU
        · exact h
      have hxneg : ind c (c.γ 0 - (s : ℂ) * normalField c 0) = -1 := by
        have hx0 : ind c (c.γ 0 + (s : ℂ) * normalField c 0) = 0 := hzero _ h1U
        rw [hx0] at hsub
        omega
      rw [hconstV y hy _ h2V, hxneg]
      exact Or.inr rfl
    · have h2U : c.γ 0 - (s : ℂ) * normalField c 0 ∈ S.U := by
        rcases h2 with h | h
        · exact h
        · exact absurd ⟨h1V, h⟩ hnotbothV
      have hxpos : ind c (c.γ 0 + (s : ℂ) * normalField c 0) = 1 := by
        have hx0 : ind c (c.γ 0 - (s : ℂ) * normalField c 0) = 0 := hzero _ h2U
        rw [hx0] at hsub
        omega
      rw [hconstV y hy _ h1V, hxpos]
      exact Or.inl rfl
  rcases key with h | h <;> rw [h] <;> norm_num

end

end Work.Smooth.JordanSeparation
