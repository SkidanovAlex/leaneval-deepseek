import Mathlib

/-!
# A preconnected set minus a closed set has at most two components, from two germs

This file generalises the "one germ" criterion
`Work.Smooth.SphereJordan.isPreconnected_sdiff_of_germ` (a *single* preconnected germ covering the
local picture at every point of the removed closed set forces `X \ Z` to be preconnected) to the
case of **two** germs:

> If `X` is preconnected, `Z ⊆ X` is closed, `G₁, G₂ ⊆ X \ Z` are nonempty preconnected, and at
> every point of `X ∩ Z` the *whole* local picture `(X \ Z) ∩ B(x, ρ)` is contained in `G₁ ∪ G₂`,
> then `X \ Z` has at most two components.

The proof is the same separation argument: the set
`W := {x | (∃ y ∈ G₁ ∪ G₂, x ∈ componentIn (X\Z) y)} ∪ (X ∩ Z)`
is open and closed in the preconnected `X`, hence all of `X`; therefore every component of `X \ Z`
meets `G₁ ∪ G₂`, and since each `G_i` is preconnected it is contained in a single component.  So the
components of `X \ Z` are exactly the components of `G₁` and of `G₂` (at most two).

**This is exactly the shape of the crosscut theorem**: with `X := D`, `Z := range γ` (the crosscut)
the local picture of `D \ range γ` at an interior point of the arc consists of the two local sides,
so two germs suffice *if* they can be chosen coherently along the whole arc — which is the global
two-sidedness content of the crosscut theorem itself.
-/

namespace Work.Spike

open Set

noncomputable section

/-- **Two germs bound the number of components by two.** -/
theorem sdiff_atMostTwo_of_twoGerms {X Z G₁ G₂ : Set ℂ} (hX : IsPreconnected X) (hZ : IsClosed Z)
    (hG₁ : IsPreconnected G₁) (hG₂ : IsPreconnected G₂)
    (hG₁sub : G₁ ⊆ X \ Z) (hG₂sub : G₂ ⊆ X \ Z) (hG₁ne : G₁.Nonempty) (hG₂ne : G₂.Nonempty)
    (hloc : ∀ x ∈ X \ Z, ∃ ρ : ℝ, 0 < ρ ∧ IsPreconnected ((X \ Z) ∩ Metric.ball x ρ))
    (hgerm : ∀ x ∈ X ∩ Z, ∃ ρ : ℝ, 0 < ρ ∧ (X \ Z) ∩ Metric.ball x ρ ⊆ G₁ ∪ G₂) :
    ∀ a b c : ℂ, a ∈ X \ Z → b ∈ X \ Z → c ∈ X \ Z →
      connectedComponentIn (X \ Z) a = connectedComponentIn (X \ Z) b ∨
      connectedComponentIn (X \ Z) a = connectedComponentIn (X \ Z) c ∨
      connectedComponentIn (X \ Z) b = connectedComponentIn (X \ Z) c := by
  set Y : Set ℂ := X \ Z with hYdef
  set G : Set ℂ := G₁ ∪ G₂ with hGdef
  have hGsub : G ⊆ X \ Z := Set.union_subset hG₁sub hG₂sub
  have hGne : G.Nonempty := hG₁ne.mono (Set.subset_union_left)
  set W : Set ℂ := {x : ℂ | (∃ y ∈ G, x ∈ connectedComponentIn Y y) ∨ x ∈ X ∩ Z} with hWdef
  have hWX : W ⊆ X := by
    rintro x (⟨y, hy, hxy⟩ | hxXZ)
    · exact (connectedComponentIn_subset Y y hxy).1
    · exact hxXZ.1
  have hGW : G ⊆ W := fun g hg => Or.inl ⟨g, hg, mem_connectedComponentIn (hGsub hg)⟩
  -- openness of `W` inside `X`
  have hopen : ∀ x : ℂ, ∃ ρ : ℝ, x ∈ X ∩ W → 0 < ρ ∧ Metric.ball x ρ ∩ X ⊆ W := by
    intro x
    by_cases hx : x ∈ X ∩ W
    · rcases hx.2 with ⟨y, hy, hxy⟩ | hxXZ
      · have hxY : x ∈ Y := connectedComponentIn_subset Y y hxy
        obtain ⟨ρ, hρ, hpre⟩ := hloc x hxY
        refine ⟨ρ, fun _ => ⟨hρ, fun z hz => ?_⟩⟩
        by_cases hzZ : z ∈ Z
        · exact Or.inr ⟨hz.2, hzZ⟩
        · have hzY : z ∈ Y := ⟨hz.2, hzZ⟩
          have hsub : Y ∩ Metric.ball x ρ ⊆ connectedComponentIn Y x :=
            hpre.subset_connectedComponentIn ⟨hxY, Metric.mem_ball_self hρ⟩ (fun w hw => hw.1)
          have hzcomp : z ∈ connectedComponentIn Y x := hsub ⟨hzY, hz.1⟩
          have heq : connectedComponentIn Y x = connectedComponentIn Y y :=
            (connectedComponentIn_eq hxy).symm
          exact Or.inl ⟨y, hy, heq ▸ hzcomp⟩
      · obtain ⟨ρ, hρ, hρG⟩ := hgerm x ⟨hx.1, hxXZ.2⟩
        refine ⟨ρ, fun _ => ⟨hρ, fun z hz => ?_⟩⟩
        by_cases hzZ : z ∈ Z
        · exact Or.inr ⟨hz.2, hzZ⟩
        · exact Or.inl ⟨z, hρG ⟨⟨hz.2, hzZ⟩, hz.1⟩,
            mem_connectedComponentIn (show z ∈ Y from ⟨hz.2, hzZ⟩)⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose ρ hρ using hopen
  -- closedness of `W` inside `X`
  have hcl : X ∩ closure W ⊆ W := by
    rintro x ⟨hxX, hxcl⟩
    by_contra hxW
    have hxZ : x ∉ Z := fun h => hxW (Or.inr ⟨hxX, h⟩)
    have hxY : x ∈ Y := ⟨hxX, hxZ⟩
    obtain ⟨ρ₁, hρ₁, hpre⟩ := hloc x hxY
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hZ.isOpen_compl x hxZ
    have hρmin : 0 < min ρ₁ δ := lt_min hρ₁ hδ
    have hcompW : connectedComponentIn Y x ∩ W = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzcomp, hzW⟩
      rcases hzW with ⟨y, hy, hzy⟩ | hxXZ
      · have hxy : x ∈ connectedComponentIn Y y := by
          have h1 : x ∈ connectedComponentIn Y x := mem_connectedComponentIn hxY
          rw [connectedComponentIn_eq hzcomp] at h1
          rw [← connectedComponentIn_eq hzy] at h1
          exact h1
        exact hxW (Or.inl ⟨y, hy, hxy⟩)
      · exact (connectedComponentIn_subset Y x hzcomp).2 hxXZ.2
    have hballW : Metric.ball x (min ρ₁ δ) ∩ X ∩ W = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨⟨hzball, hzX⟩, hzW⟩
      have hzball₁ : z ∈ Metric.ball x ρ₁ := Metric.ball_subset_ball (min_le_left _ _) hzball
      have hzballδ : z ∈ Metric.ball x δ := Metric.ball_subset_ball (min_le_right _ _) hzball
      by_cases hzZ : z ∈ Z
      · exact hδsub hzballδ hzZ
      · have hzY : z ∈ Y := ⟨hzX, hzZ⟩
        have hzcomp : z ∈ connectedComponentIn Y x :=
          hpre.subset_connectedComponentIn ⟨hxY, Metric.mem_ball_self hρ₁⟩ (fun w hw => hw.1)
            ⟨hzY, hzball₁⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hcompW) z ⟨hzcomp, hzW⟩
    obtain ⟨w, hwW, hwdist⟩ := Metric.mem_closure_iff.mp hxcl (min ρ₁ δ) hρmin
    exact (Set.eq_empty_iff_forall_notMem.mp hballW) w
      ⟨⟨Metric.mem_ball.mpr (by rw [dist_comm]; exact hwdist), hWX hwW⟩, hwW⟩
  -- separation argument: `X ⊆ W`
  have hXW : X ⊆ W := by
    set U : Set ℂ := ⋃ x : ℂ, ⋃ (_ : x ∈ X ∩ W), Metric.ball x (ρ x) with hUdef
    have hUopen : IsOpen U := by
      rw [hUdef]
      exact isOpen_iUnion fun x => isOpen_iUnion fun _ => Metric.isOpen_ball
    have hXcover : X ⊆ closure W ∪ Uᶜ := by
      intro z hz
      by_cases hzW : z ∈ W
      · exact Or.inl (subset_closure hzW)
      · refine Or.inr fun hzU => ?_
        obtain ⟨x, hzx⟩ := mem_iUnion.mp hzU
        obtain ⟨hxmem, hzball⟩ := mem_iUnion.mp hzx
        exact hzW ((hρ x hxmem).2 ⟨hzball, hz⟩)
    have hXdisj : X ∩ (closure W ∩ Uᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzX, hzcl, hzU⟩
      have hzW : z ∈ W := hcl ⟨hzX, hzcl⟩
      exact hzU (mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨⟨hzX, hzW⟩,
        Metric.mem_ball_self ((hρ z ⟨hzX, hzW⟩).1)⟩⟩)
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hX) (closure W) Uᶜ
      isClosed_closure hUopen.isClosed_compl hXcover hXdisj with h | h
    · exact fun z hz => hcl ⟨hz, h hz⟩
    · exfalso
      obtain ⟨g, hg⟩ := hGne
      exact (h (hGsub hg).1) (mem_iUnion.mpr ⟨g, mem_iUnion.mpr ⟨⟨(hGsub hg).1, hGW hg⟩,
        Metric.mem_ball_self ((hρ g ⟨(hGsub hg).1, hGW hg⟩).1)⟩⟩)
  -- conclusion: every point of `Y` lies in the component of `g₁` or of `g₂`
  obtain ⟨g₁, hg₁⟩ := hG₁ne
  obtain ⟨g₂, hg₂⟩ := hG₂ne
  have hg₁Y : g₁ ∈ Y := hG₁sub hg₁
  have hg₂Y : g₂ ∈ Y := hG₂sub hg₂
  have key : ∀ z ∈ Y, z ∈ connectedComponentIn Y g₁ ∨ z ∈ connectedComponentIn Y g₂ := by
    intro z hz
    have hzW : z ∈ W := hXW hz.1
    rcases hzW with ⟨y, hy, hzy⟩ | hzXZ
    · rcases hy with hy | hy
      · refine Or.inl ?_
        rw [connectedComponentIn_eq (hG₁.subset_connectedComponentIn hg₁ hG₁sub hy)]
        exact hzy
      · refine Or.inr ?_
        rw [connectedComponentIn_eq (hG₂.subset_connectedComponentIn hg₂ hG₂sub hy)]
        exact hzy
    · exact absurd hzXZ.2 hz.2
  intro a b c ha hb hc
  have hba := key b hb
  have hca := key c hc
  rcases key a ha with ha1 | ha2
  · rcases hba with hb1 | hb2
    · exact Or.inl ((connectedComponentIn_eq ha1).symm.trans (connectedComponentIn_eq hb1))
    · rcases hca with hc1 | hc2
      · exact Or.inr (Or.inl ((connectedComponentIn_eq ha1).symm.trans
          (connectedComponentIn_eq hc1)))
      · exact Or.inr (Or.inr ((connectedComponentIn_eq hb2).symm.trans
          (connectedComponentIn_eq hc2)))
  · rcases hba with hb1 | hb2
    · rcases hca with hc1 | hc2
      · exact Or.inr (Or.inr ((connectedComponentIn_eq hb1).symm.trans
          (connectedComponentIn_eq hc1)))
      · exact Or.inr (Or.inl ((connectedComponentIn_eq ha2).symm.trans
          (connectedComponentIn_eq hc2)))
    · exact Or.inl ((connectedComponentIn_eq ha2).symm.trans (connectedComponentIn_eq hb2))

end

end Work.Spike
