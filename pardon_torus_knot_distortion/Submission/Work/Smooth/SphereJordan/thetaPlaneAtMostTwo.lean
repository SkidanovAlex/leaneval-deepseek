import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.thetaSides
import Submission.Work.Smooth.SphereJordan.disc_complement_preconnected

namespace Work.Smooth.SphereJordan

open Set

/-- **The at-most-two-components statement for the plane theta graph.**

Two disjoint embedded discs `D₁`, `D₂` joined by two arcs `α`, `β` whose interiors avoid the discs
and each other: of any three points off the union, two lie in the same connected component.

The proof is the one through the side determination `thetaSideDetermination`, which exhibits two
preconnected open sets `S₁.V`, `S₂.U` that avoid the theta graph and tile its complement; the general
tool `atMostTwo_components_of_neighbourhood` then bounds the number of components by two.

(An alternative derivation, through the `ThetaAtMostTwo` input of
`Submission/Work/Smooth/SphereJordan/planeArcComponentsCore.lean` and the two classical "bump
removal" inputs, is recorded as `thetaPlaneAtMostTwoViaSides` and in
`Submission/Work/Smooth/SphereJordan/thetaAtMostTwoOfBumps.lean`.) -/
theorem thetaPlaneAtMostTwo
    {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩)
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    ∀ x y z : ℂ, x ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      y ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      z ∉ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β →
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ x =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ y ∨
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ x =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ z ∨
      connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ y =
        connectedComponentIn (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ z := by
  obtain ⟨J₁, J₂, S₁, S₂, hJ₁, hJ₂, hsub₁, hsub₂, hα₁, hβ₁, hα₂, hβ₂, hAV, hAU, hdj, hun⟩ :=
    Work.Smooth.SphereJordan.thetaSideDetermination h hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀
      hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  obtain ⟨f, hf, hfr⟩ := hD₁
  obtain ⟨g, hg, hgr⟩ := hD₂
  have hMclosed : IsClosed (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) := by
    rw [← hfr, ← hgr]
    exact (((isCompact_range f.continuous).union (isCompact_range g.continuous)).union
      (isCompact_range α.continuous)).union (isCompact_range β.continuous) |>.isClosed
  have hMne : (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β).Nonempty := by
    refine ⟨f ⟨0, by norm_num⟩, Or.inl (Or.inl (Or.inl ?_))⟩
    rw [← hfr]
    exact ⟨⟨0, by norm_num⟩, rfl⟩
  have hPsub : S₁.V ⊆ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzM
    exact (Set.eq_empty_iff_forall_notMem.mp hAV z) ⟨hzM, hz⟩
  have hQsub : S₂.U ⊆ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzM
    exact (Set.eq_empty_iff_forall_notMem.mp hAU z) ⟨hzM, hz⟩
  have hcov : Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ⊆ S₁.V ∪ S₂.U := by
    rw [show Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) =
      (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ from by ext z; simp, ← hun]
  exact atMostTwo_components_of_neighbourhood hMne hMclosed (Set.subset_univ _) isOpen_univ
    S₁.preconn_V S₂.preconn_U S₁.nonempty_V S₂.nonempty_U hPsub hQsub hcov

end Work.Smooth.SphereJordan
