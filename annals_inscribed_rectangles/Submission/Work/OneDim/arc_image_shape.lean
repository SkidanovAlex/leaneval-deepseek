import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.ArcDefs
import Submission.Work.OneDim.interval_surj
import Submission.Work.OneDim.reparam_arc
import Submission.Work.OneDim.end_behavior_injective
import Submission.Work.OneDim.OneDimShapeTools
import Submission.Work.OneDim.chain_union

/-!
# The image of a maximal arc parametrisation

Whitney's strong embedding theorem in dimension `2n` rests on the classification of connected
smooth `1`-manifolds: a maximal arc in such a manifold is everything, or everything minus one
point.  Here we deduce that statement from a maximal *arc parametrisation* `(s, γ)` at a point `p`
(the dichotomy `Work.OneDim.arc_image_shape`).

The support for the argument lives in `Work.OneDim.OneDimShapeTools`.
-/

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

/-- **Existence of a maximal arc** above a given one. -/
theorem exists_maximal_arc [T2Space C] [SecondCountableTopology C]
    (A₀ : Set C) (hA₀ : IsOpenArc A₀) :
    ∃ A, IsOpenArc A ∧ A₀ ⊆ A ∧ ∀ B, IsOpenArc B → A ⊆ B → B ⊆ A := by
  obtain ⟨A, hA₀A, hAmax⟩ := zorn_subset_nonempty {A | IsOpenArc A}
    (fun c hc' hchain hne => ⟨⋃₀ c, chain_union (fun A hA => hc' hA) hchain hne,
      fun s hs => subset_sUnion_of_mem hs⟩) A₀ hA₀
  exact ⟨A, hAmax.1, hA₀A, fun B hB hAB => hAmax.2 hB hAB⟩

theorem arc_image_shape {C : Type*} [TopologicalSpace C] [ChartedSpace Work.OneDim.E1 C]
    [IsManifold Work.OneDim.I1 Work.OneDim.sm C] [T2Space C] [SecondCountableTopology C]
    [ConnectedSpace C]
    (hend : ∀ (γ : ℝ → C), Continuous γ → Function.Injective γ → ∀ x : C,
      (∀ U : Set C, IsOpen U → x ∈ U →
        Filter.Frequently (fun t : ℝ => γ t ∈ U) Filter.atTop) →
      Filter.Tendsto γ Filter.atTop (nhds x))
    {p : C} {s : Set ℝ} {γ : ℝ → C} (harc : Work.OneDim.IsArcParam p s γ)
    (hmax : ∀ s' γ', Work.OneDim.IsArcParam p s' γ' → s ⊆ s' → Set.EqOn γ γ' s → s' ⊆ s) :
    (∃ φ : ℝ → C, Function.Bijective φ ∧
        IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm φ) ∨
      (∃ (q : C) (φ : ℝ → C), Function.Injective φ ∧
        IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm φ ∧
        Set.range φ = Set.compl ({q} : Set C) ∧ Filter.Tendsto φ Filter.atTop (nhds q) ∧
        Filter.Tendsto φ Filter.atBot (nhds q)) := by
  -- a starting arc, obtained from the given arc parametrisation
  have h0s : (0 : ℝ) ∈ s := harc.zero_mem
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.mp harc.isOpen 0 h0s
  have hsub : Set.Ioo (-ε) ε ⊆ s := by
    intro t ht
    apply hεs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIconn : IsPreconnected (Set.Ioo (-ε) ε) := isPreconnected_Ioo (a := -ε) (b := ε)
  have hIne : (Set.Ioo (-ε) ε).Nonempty := ⟨0, by simp [hε]⟩
  obtain ⟨g, hginj, hgld, hgrange⟩ :=
    reparam_arc isOpen_Ioo hIconn hIne
      (fun x hx y hy hxy => harc.injOn (hsub hx) (hsub hy) hxy)
      (fun x => harc.isLocalDiffeomorphOn ⟨x.1, hsub x.2⟩)
  have hA₀ : IsOpenArc (γ '' Set.Ioo (-ε) ε) := ⟨g, hginj, hgld, hgrange.symm⟩
  obtain ⟨A, hArest⟩ := exists_maximal_arc (γ '' Set.Ioo (-ε) ε) hA₀
  obtain ⟨g', hg'inj, hg'ld, hg'range⟩ := hArest.1
  have hg'r : Set.range g' = A := hg'range.symm
  rcases maximal_arc_shape hArest.1 hArest.2.2 hg'inj hg'ld hg'r with hu | ⟨q, hq, htop, hbot⟩
  · left
    refine ⟨g', ⟨hg'inj, ?_⟩, hg'ld⟩
    intro y
    show y ∈ Set.range g'
    rw [hg'r, hu]
    exact trivial
  · right
    exact ⟨q, g', hg'inj, hg'ld, hg'r.trans hq, htop, hbot⟩

end Work.OneDim
