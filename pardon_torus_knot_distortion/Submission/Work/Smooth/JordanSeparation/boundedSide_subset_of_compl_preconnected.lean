import Mathlib
import Submission.Work.Smooth.Jordan.Separation

/-!
# The bounded side of a simple closed curve is contained in any open set with connected complement

Let `β : ℝ → ℂ` be a simple closed plane curve (continuous, `2π`-periodic, injective on one
period) and `S : PlaneSeparation ⟨β, hβ, hper⟩` a Jordan separation of its trace, with unbounded
side `S.U` and bounded side `S.V`.  If `U ∋ range β` is an open set whose complement, together with
the point at infinity, is preconnected in the one-point compactification `OnePoint ℂ`, then the
whole bounded side `S.V` lies in `U`.

The point is that, inside the sphere `OnePoint ℂ`, the set

`A = (↑) '' Uᶜ ∪ {∞}`

is a preconnected subset of `S² ∖ (↑ '' trace) = (↑ '' S.U) ∪ (↑ '' S.V) ∪ {∞}` that contains `∞`.
The two sides of the curve give a partition of the complement of the trace into two open pieces
(openness of `(↑ '' S.U) ∪ {∞}` uses that `S.V ∪ trace` is closed and bounded, hence compact),
so a preconnected set must lie entirely on one of them; as `A ∋ ∞ ∉ (↑ '' S.V)`, it lies in
`(↑ '' S.U) ∪ {∞}`.  Hence `Uᶜ ⊆ S.U`, and since `S.U` is disjoint from `S.V`, we get `S.V ⊆ U`.
-/

namespace Work.Smooth.JordanSeparation

open Set

set_option linter.unusedVariables false in
theorem boundedSide_subset_of_compl_preconnected
    {β : ℝ → ℂ} (hβ : Continuous β) (hper : Function.Periodic β (2 * Real.pi))
    (hinj : Set.InjOn β (Set.Ico 0 (2 * Real.pi)))
    (S : Work.Smooth.Jordan.PlaneSeparation ⟨β, hβ, hper⟩)
    {U : Set ℂ} (hUo : IsOpen U) (hβU : Set.range β ⊆ U)
    (hpre : IsPreconnected (((fun z : ℂ => (z : OnePoint ℂ)) '' Uᶜ) ∪ {OnePoint.infty})) :
    S.V ⊆ U := by
  -- The two sides partition the complement of the trace.
  have hUV : S.U ∪ S.V = (Set.range β)ᶜ := S.union_eq
  -- The complement of `U` is disjoint from the trace.
  have hUc_sub : Uᶜ ⊆ (Set.range β)ᶜ := by
    intro z hz hzr
    exact hz (hβU hzr)
  have hTc_closed : IsClosed (Set.range β) :=
    (⟨β, hβ, hper⟩ : Work.Smooth.Jordan.PlaneCurve).isClosed_trace
  have hTc_compact : IsCompact (Set.range β) :=
    (⟨β, hβ, hper⟩ : Work.Smooth.Jordan.PlaneCurve).isCompact_trace
  -- The two sides of the curve, as subsets of the one-point compactification.
  set C₁ : Set (OnePoint ℂ) := (↑) '' S.V with hC1
  set C₂ : Set (OnePoint ℂ) := (↑) '' S.U ∪ {OnePoint.infty} with hC2
  -- `C₁` is open: it is the image of the open set `S.V`.
  have hC1_open : IsOpen C₁ := by
    rw [hC1]; exact OnePoint.isOpen_image_coe.mpr S.isOpen_V
  -- The bounded side accumulates only on itself and the trace.
  have hcl : closure S.V ⊆ S.V ∪ Set.range β := by
    intro z hz
    by_cases hzT : z ∈ Set.range β
    · exact Or.inr hzT
    · refine Or.inl ?_
      by_contra hzV
      have hzU : z ∈ S.U := by
        have hz_union : z ∈ S.U ∪ S.V := by rw [hUV]; exact hzT
        rcases hz_union with h | h
        · exact h
        · exact absurd h hzV
      obtain ⟨w, hwU, hwV⟩ := mem_closure_iff.mp hz S.U S.isOpen_U hzU
      exact Set.disjoint_left.mp S.disjoint_UV hwU hwV
  -- `S.V ∪ trace` is closed and bounded, hence compact.
  have hclosed : IsClosed (S.V ∪ Set.range β) := by
    apply closure_subset_iff_isClosed.mp
    rw [closure_union, hTc_closed.closure_eq]
    exact union_subset hcl (fun y hy => Or.inr hy)
  have hcompact : IsCompact (S.V ∪ Set.range β) := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨hclosed, Bornology.IsBounded.union S.bounded_V hTc_compact.isBounded⟩
  -- Its complement inside the sphere is `C₂`.
  have hcompl : (S.V ∪ Set.range β)ᶜ = S.U := by
    ext z
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · rintro ⟨hzV, hzT⟩
      have hz_union : z ∈ S.U ∪ S.V := by rw [hUV]; exact hzT
      rcases hz_union with h | h
      · exact h
      · exact absurd h hzV
    · intro hzU
      refine ⟨?_, ?_⟩
      · intro hzV; exact Set.disjoint_left.mp S.disjoint_UV hzU hzV
      · intro hzT
        have : z ∈ (Set.range β)ᶜ := by rw [← hUV]; exact Or.inl hzU
        exact this hzT
  have hC2_eq : C₂ = ((↑) '' (S.V ∪ Set.range β) : Set (OnePoint ℂ))ᶜ := by
    rw [hC2, OnePoint.compl_image_coe, hcompl]
  -- Hence `C₂` is open too.
  have hC2_open : IsOpen C₂ := by
    rw [hC2_eq]
    exact OnePoint.isOpen_compl_image_coe.mpr ⟨hclosed, hcompact⟩
  -- The preconnected set `A` is covered by the two open pieces.
  have hA_sub : ((↑) '' Uᶜ ∪ {OnePoint.infty} : Set (OnePoint ℂ)) ⊆ C₁ ∪ C₂ := by
    intro z hz
    rcases hz with hz1 | hz2
    · obtain ⟨x, hxUc, hxz⟩ := hz1
      subst hxz
      have hx : x ∈ S.U ∪ S.V := by rw [hUV]; exact hUc_sub hxUc
      rcases hx with h | h
      · exact Or.inr (by rw [hC2]; exact Or.inl ⟨x, h, rfl⟩)
      · exact Or.inl (by rw [hC1]; exact ⟨x, h, rfl⟩)
    · rw [Set.mem_singleton_iff] at hz2
      subst hz2
      exact Or.inr (by rw [hC2]; exact Or.inr rfl)
  -- The two pieces are disjoint.
  have hdisjC : Disjoint C₁ C₂ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [hC1] at hz1
    rw [hC2] at hz2
    obtain ⟨x, hxV, hxz⟩ := hz1
    rcases hz2 with ⟨y, hyU, hyz⟩ | hzinf
    · have hxy : y = x := OnePoint.coe_injective (hyz.trans hxz.symm)
      exact Set.disjoint_left.mp S.disjoint_UV (hxy ▸ hyU) hxV
    · rw [Set.mem_singleton_iff] at hzinf
      rw [← hxz] at hzinf
      exact OnePoint.coe_ne_infty x hzinf
  -- Preconnectedness forces `A` onto the side of `∞`, i.e. into `C₂`.
  rcases IsPreconnected.subset_or_subset hC1_open hC2_open hdisjC hA_sub hpre with hA1 | hA2
  · -- `A` contains `∞`, which is not in `C₁`.
    exfalso
    have hinfA : (OnePoint.infty : OnePoint ℂ) ∈ (↑) '' Uᶜ ∪ {OnePoint.infty} := Or.inr rfl
    have hmem := hA1 hinfA
    rw [hC1] at hmem
    exact OnePoint.infty_notMem_image_coe hmem
  · have hUcSU : Uᶜ ⊆ S.U := by
      intro x hx
      have hxA : (x : OnePoint ℂ) ∈ (↑) '' Uᶜ ∪ {OnePoint.infty} := Or.inl ⟨x, hx, rfl⟩
      have hx2 := hA2 hxA
      rw [hC2] at hx2
      rcases hx2 with ⟨y, hyU, hyx⟩ | hxinf
      · exact (OnePoint.coe_injective hyx.symm) ▸ hyU
      · rw [Set.mem_singleton_iff] at hxinf
        exact absurd hxinf (OnePoint.coe_ne_infty x)
    intro z hz
    by_contra hzU
    exact Set.disjoint_left.mp S.disjoint_UV (hUcSU hzU) hz

end Work.Smooth.JordanSeparation
