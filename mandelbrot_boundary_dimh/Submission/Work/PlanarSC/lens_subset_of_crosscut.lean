import Mathlib
import Submission.Work.PlanarSC.JordanSeparation

/-!
# The cap cut off by a crosscut lies in the domain

`Work.PlanarSC.lens_subset_of_crosscut`: let `γ : C(Circle, ℂ)` be a Jordan curve,
`U`, `V` the two complementary domains (`U` bounded, `V` unbounded, both open,
connected, disjoint, `U ∪ V = (range γ)ᶜ`), let `A = γ '' (range (Circle.path t₁ t₂))`
be one of the two arcs into which `t₁ ≠ t₂` cut the curve, and let `δ` be a curve
in `U ∪ range γ` joining the endpoints `γ t₁`, `γ t₂` of that arc with its interior
in `U` (a *crosscut*).  Then every bounded component of the complement of
`A ∪ range δ` (the "lens") lies in `U`.

The proof is elementary plane topology.  Its two ingredients are

* `U` and `V` are exactly the two connected components of `(range γ)ᶜ` (because the
  complement is partitioned into the two disjoint open connected sets `U`, `V`), so
  the frontier of each of them is the whole curve
  (`Commons.Topology.Connected.frontier_component_compl_range`);
* `V` is contained in the complement of the lens, so a point of `V` has a component
  which, being a superset of the unbounded set `V`, is unbounded.

Concretely, if `z` is outside the lens with a bounded component `C` and `z ∉ U`, then
either `z ∈ V` — whence `V ⊆ C` and `C` is unbounded — or `z ∈ range γ` lies on the
complementary arc of the curve, in which case `z ∈ frontier V`: a small ball around `z`
avoiding the (compact) arc and crosscut is contained in `C` and meets `V`, so again
`V ⊆ C` and `C` is unbounded.

Note that only two properties of the arc `A` and of the crosscut `δ` are used:
`A ⊆ range γ` and `range δ ⊆ U ∪ range γ`.
-/

namespace Work.PlanarSC

open Set

noncomputable section

/-- If `Kᶜ = U ∪ V` with `U`, `V` disjoint open sets and `U` connected, then `U` is a connected
component of `Kᶜ`. -/
theorem connectedComponentIn_eq_left_of_cover {K U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hdisj : Disjoint U V) (hUc : IsConnected U) (hcover : U ∪ V = Kᶜ) {u : ℂ} (hu : u ∈ U) :
    connectedComponentIn Kᶜ u = U := by
  have hUsub : U ⊆ Kᶜ := fun x hx => by rw [← hcover]; exact Or.inl hx
  refine Set.Subset.antisymm ?_ (hUc.isPreconnected.subset_connectedComponentIn hu hUsub)
  intro x hx
  have hxsub : connectedComponentIn Kᶜ u ⊆ U ∪ V := fun y hy => by
    rw [hcover]; exact connectedComponentIn_subset Kᶜ u hy
  rcases (isPreconnected_connectedComponentIn (F := Kᶜ) (x := u)).subset_or_subset hUo hVo hdisj
    hxsub with h | h
  · exact h hx
  · exact absurd (h (mem_connectedComponentIn (hUsub hu))) (Set.disjoint_left.mp hdisj hu)

/-- The symmetric form of `connectedComponentIn_eq_left_of_cover`. -/
theorem connectedComponentIn_eq_right_of_cover {K U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hdisj : Disjoint U V) (hVc : IsConnected V) (hcover : U ∪ V = Kᶜ) {v : ℂ} (hv : v ∈ V) :
    connectedComponentIn Kᶜ v = V :=
  connectedComponentIn_eq_left_of_cover hVo hUo hdisj.symm hVc
    (by rw [Set.union_comm]; exact hcover) hv

/-- If `Kᶜ` is the union of two disjoint nonempty open connected sets, it is not preconnected. -/
theorem not_isPreconnected_compl_of_cover {K U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hdisj : Disjoint U V) (hUc : IsConnected U) (hVc : IsConnected V) (hcover : U ∪ V = Kᶜ) :
    ¬ IsPreconnected Kᶜ := by
  intro hpre
  rcases hpre.subset_or_subset hUo hVo hdisj (le_of_eq hcover.symm) with h | h
  · obtain ⟨v, hv⟩ := hVc.nonempty
    have hvK : v ∈ Kᶜ := by rw [← hcover]; exact Or.inr hv
    exact Set.disjoint_left.mp hdisj (h hvK) hv
  · obtain ⟨u, hu⟩ := hUc.nonempty
    have huK : u ∈ Kᶜ := by rw [← hcover]; exact Or.inl hu
    exact Set.disjoint_left.mp hdisj hu (h huK)

theorem lens_subset_of_crosscut {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hdisj : Disjoint U V) (hUb : Bornology.IsBounded U) (hVb : ¬ Bornology.IsBounded V)
    (hcover : U ∪ V = (Set.range γ)ᶜ)
    {t₁ t₂ : Circle} (ht : t₁ ≠ t₂)
    {δ : C(Set.Icc (0:ℝ) 1, ℂ)} (hδ0 : δ 0 = γ t₁) (hδ1 : δ 1 = γ t₂)
    (hδint : ∀ s : Set.Icc (0:ℝ) 1, s ≠ 0 → s ≠ 1 → δ s ∈ U) :
    ∀ z : ℂ, z ∉ (γ '' (Set.range (Circle.path t₁ t₂))) ∪ Set.range δ →
      Bornology.IsBounded (connectedComponentIn
        (((γ '' (Set.range (Circle.path t₁ t₂))) ∪ Set.range δ)ᶜ) z) → z ∈ U := by
  intro z hzK hzbdd
  set A : Set ℂ := γ '' (Set.range (Circle.path t₁ t₂)) with hAdef
  set L : Set ℂ := Set.range δ with hLdef
  have hzA : z ∉ A := fun h => hzK (Or.inl h)
  have hzL : z ∉ L := fun h => hzK (Or.inr h)
  -- `U`, `V` are the complementary domains of `γ`
  have hUsub : U ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_left
  have hVsub : V ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_right
  -- `Uᶜ = V ∪ range γ`
  have hUeq : Uᶜ = V ∪ Set.range γ := by
    ext w
    constructor
    · intro hw
      by_cases hwV : w ∈ V
      · exact Or.inl hwV
      · refine Or.inr ?_
        by_contra hwR
        have hwc : w ∈ (Set.range γ)ᶜ := by simpa using hwR
        rw [← hcover] at hwc
        exact hwc.elim hw hwV
    · rintro (h | h)
      · exact fun hU => Set.disjoint_left.mp hdisj hU h
      · exact fun hU => hUsub hU h
  -- the lens is contained in `range γ ∪ U ∪ V`, so `V` avoids it
  have hAt : A ⊆ Set.range γ := Set.image_subset_range γ _
  have hLt : L ⊆ U ∪ Set.range γ := by
    rintro x ⟨s, rfl⟩
    by_cases h0 : s = 0
    · exact Or.inr ⟨t₁, by rw [h0, hδ0]⟩
    · by_cases h1 : s = 1
      · exact Or.inr ⟨t₂, by rw [h1, hδ1]⟩
      · exact Or.inl (hδint s h0 h1)
  have hVW : V ⊆ (A ∪ L)ᶜ := by
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨fun hvA => hVsub hv (hAt hvA), ?_⟩
    rintro ⟨s, hs⟩
    have h1 : v ∈ U ∪ Set.range γ := hs ▸ hLt ⟨s, rfl⟩
    rcases h1 with h | h
    · exact Set.disjoint_left.mp hdisj h hv
    · exact hVsub hv h
  have hnotpre : ¬ IsPreconnected (Set.range γ)ᶜ :=
    not_isPreconnected_compl_of_cover hUo hVo hdisj hUc hVc hcover
  by_contra hzU
  have hzUc : z ∈ Uᶜ := hzU
  rw [hUeq] at hzUc
  rcases hzUc with hzV | hzR
  · -- the component of a point of `V` contains the unbounded set `V`
    exact hVb (hzbdd.subset (hVc.isPreconnected.subset_connectedComponentIn hzV hVW))
  · -- `z` lies on the complementary arc of the Jordan curve
    obtain ⟨v₀, hv₀⟩ := hVc.nonempty
    have hfrontV : frontier V = Set.range γ := by
      have h := Commons.Topology.Connected.frontier_component_compl_range γ hγ hnotpre v₀
        (by rw [← hcover]; exact Or.inr hv₀)
      rwa [connectedComponentIn_eq_right_of_cover hUo hVo hdisj hVc hcover hv₀] at h
    have hzcl : z ∈ closure V := frontier_subset_closure (by rw [hfrontV]; exact hzR)
    -- a ball around `z` avoiding the compact set `A ∪ L`
    have hAcpt : IsCompact A := (isCompact_range (Circle.path t₁ t₂).continuous).image γ.continuous
    have hLcpt : IsCompact L := isCompact_range δ.continuous
    obtain ⟨ε₁, hε₁, hsub₁⟩ := Metric.isOpen_iff.mp hAcpt.isClosed.isOpen_compl z hzA
    obtain ⟨ε₂, hε₂, hsub₂⟩ := Metric.isOpen_iff.mp hLcpt.isClosed.isOpen_compl z hzL
    set ε : ℝ := min ε₁ ε₂ with hεdef
    have hεpos : 0 < ε := lt_min hε₁ hε₂
    have hballW : Metric.ball z ε ⊆ (A ∪ L)ᶜ := by
      intro w hw
      simp only [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨hsub₁ (Metric.ball_subset_ball (min_le_left _ _) hw),
        hsub₂ (Metric.ball_subset_ball (min_le_right _ _) hw)⟩
    -- that ball meets `V` and is contained in the component of `z`
    obtain ⟨v, hvV, hvd⟩ := Metric.mem_closure_iff.mp hzcl ε hεpos
    have hvC : v ∈ connectedComponentIn (A ∪ L)ᶜ z :=
      (convex_ball z ε).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hεpos)
        hballW (Metric.mem_ball.mpr (by rw [dist_comm]; exact hvd))
    have hVsubC : V ⊆ connectedComponentIn (A ∪ L)ᶜ z := by
      rw [connectedComponentIn_eq hvC]
      exact hVc.isPreconnected.subset_connectedComponentIn hvV hVW
    exact hVb (hzbdd.subset hVsubC)

end

end Work.PlanarSC
