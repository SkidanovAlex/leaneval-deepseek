import Mathlib
import Submission.Work.PlanarSC.JordanSeparation
import Submission.Lib.Unif2.Commons.Topology.Connected.frontier_component_compl_range

/-!
# The complement of two disjoint Jordan curves is not the union of two preconnected pieces

Let `γ₁ γ₂ : C(Circle, ℂ)` be injective with disjoint images (`K₁`, `K₂`).  Then the complement
`X = (K₁ ∪ K₂)ᶜ` of the union of the two curves cannot be written as `P ∪ Q` with `P`, `Q`
nonempty, disjoint and preconnected: `X` has *three* connected components (the exterior of both
curves, and one further region for each curve), so two preconnected pieces never suffice.

The proof only uses the Jordan separation theorem (`Commons.Topology.Jordan.plane_separation`),
which splits the complement of each curve into a bounded component `Uᵢ` and an unbounded component
`Vᵢ`, together with the fact that the frontier of each of the two components is the curve
(`Commons.Topology.Connected.frontier_component_compl_range`).

Every preconnected `S ⊆ X` is contained in `U₁` or `V₁` (the two are open, disjoint and cover
`K₁ᶜ ⊇ X`) and likewise in `U₂` or `V₂`; so it is contained in one of the four "classes"
`U₁∩U₂`, `U₁∩V₂`, `V₁∩U₂`, `V₁∩V₂`, and it can never contain two points lying in different
classes.  It therefore suffices to exhibit three points of `X` in three different classes, which
is done by splitting into the possible relative positions of the two curves.
-/

namespace Work.PlanarSC

open Set

set_option linter.unusedVariables false

noncomputable section

/-! ## Elementary plane-topology helpers -/

/-- For an open set the closure is the set itself together with its frontier. -/
lemma closure_eq_self_union_frontier_of_isOpen {s : Set ℂ} (hs : IsOpen s) :
    closure s = s ∪ frontier s := by
  rw [hs.frontier_eq]
  exact (Set.union_sdiff_cancel subset_closure).symm

/-- Every bounded subset of `ℂ` misses a point. -/
lemma exists_notMem_of_isBounded {W : Set ℂ} (hW : Bornology.IsBounded W) :
    ∃ z : ℂ, z ∉ W := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hW
  refine ⟨((max C 0 + 1 : ℝ) : ℂ), fun hz => ?_⟩
  have h1 := hC _ hz
  have h2 : ‖((max C 0 + 1 : ℝ) : ℂ)‖ = max C 0 + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h2] at h1
  linarith [le_max_left C 0]

/-- The complement of the image of a Jordan curve is not preconnected, as soon as the two
components `U`, `V` of the complement supplied by the Jordan separation theorem are known. -/
lemma not_isPreconnected_compl_range_of_separation {γ : C(Circle, ℂ)} {U V : Set ℂ}
    (hUo : IsOpen U) (hVo : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = (Set.range γ)ᶜ) :
    ¬ IsPreconnected (Set.range γ)ᶜ := by
  have hVsub : V ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_right
  have hUsub : U ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_left
  intro hpre
  rcases hpre.subset_or_subset hUo hVo hdisj (le_of_eq hcover.symm) with h | h
  · obtain ⟨y, hy⟩ := hVc.nonempty
    exact (Set.disjoint_left.mp hdisj) (h (hVsub hy)) hy
  · obtain ⟨y, hy⟩ := hUc.nonempty
    exact (Set.disjoint_left.mp hdisj) hy (h (hUsub hy))

/-- Each of the two complementary components of a Jordan curve is the connected component of
`(range γ)ᶜ` of any of its points. -/
lemma eq_connectedComponentIn_of_separation {γ : C(Circle, ℂ)} {U V : Set ℂ}
    (hγ : Function.Injective γ) (hUo : IsOpen U) (hVo : IsOpen V) (hUc : IsConnected U)
    (hVc : IsConnected V) (hdisj : Disjoint U V) (hcover : U ∪ V = (Set.range γ)ᶜ)
    {x : ℂ} (hx : x ∈ U) : connectedComponentIn ((Set.range γ)ᶜ) x = U := by
  have hUsub : U ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_left
  have hxγ : x ∈ (Set.range γ)ᶜ := hUsub hx
  refine Set.Subset.antisymm ?_ ?_
  · rcases (isPreconnected_connectedComponentIn (F := (Set.range γ)ᶜ) (x := x)).subset_or_subset
      hUo hVo hdisj (by rw [← hcover]; exact connectedComponentIn_subset _ _) with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn hxγ)) ((Set.disjoint_left.mp hdisj) hx)
  · exact hUc.isPreconnected.subset_connectedComponentIn hx hUsub

/-- The frontier of each of the two complementary components of a Jordan curve is the curve. -/
lemma frontier_eq_of_separation {γ : C(Circle, ℂ)} {U V : Set ℂ}
    (hγ : Function.Injective γ) (hUo : IsOpen U) (hVo : IsOpen V) (hUc : IsConnected U)
    (hVc : IsConnected V) (hdisj : Disjoint U V) (hcover : U ∪ V = (Set.range γ)ᶜ) :
    frontier U = Set.range γ ∧ frontier V = Set.range γ := by
  have hnotpre := not_isPreconnected_compl_range_of_separation hUo hVo hUc hVc hdisj hcover
  have hUsub : U ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_left
  have hVsub : V ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_right
  obtain ⟨u, hu⟩ := hUc.nonempty
  obtain ⟨v, hv⟩ := hVc.nonempty
  refine ⟨?_, ?_⟩
  · rw [← eq_connectedComponentIn_of_separation hγ hUo hVo hUc hVc hdisj hcover hu]
    exact Commons.Topology.Connected.frontier_component_compl_range γ hγ hnotpre u (hUsub hu)
  · have hcover' : V ∪ U = (Set.range γ)ᶜ := by rw [Set.union_comm]; exact hcover
    rw [← eq_connectedComponentIn_of_separation hγ hVo hUo hVc hUc hdisj.symm hcover' hv]
    exact Commons.Topology.Connected.frontier_component_compl_range γ hγ hnotpre v (hVsub hv)

/-- A point outside the union of two bounded sets and the images of two Jordan curves lies in both
unbounded complementary components. -/
lemma exists_mem_inter_exteriors {γ₁ γ₂ : C(Circle, ℂ)} {U₁ V₁ U₂ V₂ : Set ℂ}
    (hU₁b : Bornology.IsBounded U₁) (hU₂b : Bornology.IsBounded U₂)
    (hU₁V₁ : U₁ ∪ V₁ = (Set.range γ₁)ᶜ) (hU₂V₂ : U₂ ∪ V₂ = (Set.range γ₂)ᶜ) :
    ∃ z : ℂ, z ∈ V₁ ∧ z ∈ V₂ := by
  have hb : Bornology.IsBounded (U₁ ∪ U₂ ∪ Set.range γ₁ ∪ Set.range γ₂) :=
    ((hU₁b.union hU₂b).union (isCompact_range γ₁.continuous).isBounded).union
      (isCompact_range γ₂.continuous).isBounded
  obtain ⟨z, hzW⟩ := exists_notMem_of_isBounded hb
  have hzK₁ : z ∉ Set.range γ₁ := fun h => hzW (by simp [h])
  have hzK₂ : z ∉ Set.range γ₂ := fun h => hzW (by simp [h])
  refine ⟨z, ?_, ?_⟩
  · have hz : z ∈ U₁ ∪ V₁ := by rw [hU₁V₁]; exact hzK₁
    exact hz.resolve_left (fun h => hzW (by simp [h]))
  · have hz : z ∈ U₂ ∪ V₂ := by rw [hU₂V₂]; exact hzK₂
    exact hz.resolve_left (fun h => hzW (by simp [h]))

/-- If three points of a set `X` are pairwise inseparable by preconnected pieces of `X`, then `X`
is not the union of two nonempty disjoint preconnected pieces. -/
lemma not_cover_of_three_separated {α : Type*} [TopologicalSpace α] (X : Set α) {t₁ t₂ t₃ : α}
    (ht₁ : t₁ ∈ X) (ht₂ : t₂ ∈ X) (ht₃ : t₃ ∈ X)
    (hsep : ∀ S : Set α, IsPreconnected S → S ⊆ X →
      ¬ (t₁ ∈ S ∧ t₂ ∈ S) ∧ ¬ (t₁ ∈ S ∧ t₃ ∈ S) ∧ ¬ (t₂ ∈ S ∧ t₃ ∈ S)) :
    ¬ ∃ P Q : Set α, IsPreconnected P ∧ IsPreconnected Q ∧ P.Nonempty ∧ Q.Nonempty ∧
      Disjoint P Q ∧ P ∪ Q = X := by
  rintro ⟨P, Q, hPpre, hQpre, hPne, hQne, hPQdisj, hPXQ⟩
  obtain ⟨x, hxP⟩ := hPne
  obtain ⟨y, hyQ⟩ := hQne
  have hPsub : P ⊆ X := by rw [← hPXQ]; exact subset_union_left
  have hQsub : Q ⊆ X := by rw [← hPXQ]; exact subset_union_right
  have hcover : X ⊆ connectedComponentIn X x ∪ connectedComponentIn X y := by
    intro z hz
    have hz' : z ∈ P ∪ Q := by rw [hPXQ]; exact hz
    rcases hz' with hzP | hzQ
    · exact Or.inl (hPpre.subset_connectedComponentIn hxP hPsub hzP)
    · exact Or.inr (hQpre.subset_connectedComponentIn hyQ hQsub hzQ)
  have hx12 := (hsep _ isPreconnected_connectedComponentIn (connectedComponentIn_subset X x)).1
  have hx13 := (hsep _ isPreconnected_connectedComponentIn (connectedComponentIn_subset X x)).2.1
  have hx23 := (hsep _ isPreconnected_connectedComponentIn (connectedComponentIn_subset X x)).2.2
  have hy12 := (hsep _ isPreconnected_connectedComponentIn (connectedComponentIn_subset X y)).1
  have hy13 := (hsep _ isPreconnected_connectedComponentIn (connectedComponentIn_subset X y)).2.1
  have hy23 := (hsep _ isPreconnected_connectedComponentIn (connectedComponentIn_subset X y)).2.2
  rcases hcover ht₁ with h1 | h1 <;> rcases hcover ht₂ with h2 | h2 <;>
    rcases hcover ht₃ with h3 | h3 <;> tauto

/-! ## The main theorem -/

theorem not_two_preconnected_pieces_of_two_jordan (γ₁ γ₂ : C(Circle, ℂ))
    (h₁ : Function.Injective γ₁) (h₂ : Function.Injective γ₂)
    (hdisj : Disjoint (Set.range γ₁) (Set.range γ₂)) :
    ¬ ∃ P Q : Set ℂ, IsPreconnected P ∧ IsPreconnected Q ∧ P.Nonempty ∧ Q.Nonempty ∧
        Disjoint P Q ∧ P ∪ Q = (Set.range γ₁ ∪ Set.range γ₂)ᶜ := by
  classical
  -- the two complementary components of each curve
  obtain ⟨U₁, V₁, hU₁o, hV₁o, hU₁c, hV₁c, hU₁V₁disj, hU₁b, hV₁unb, hU₁V₁eq⟩ :=
    Commons.Topology.Jordan.plane_separation γ₁ h₁
  obtain ⟨U₂, V₂, hU₂o, hV₂o, hU₂c, hV₂c, hU₂V₂disj, hU₂b, hV₂unb, hU₂V₂eq⟩ :=
    Commons.Topology.Jordan.plane_separation γ₂ h₂
  obtain ⟨hfrontU₁, hfrontV₁⟩ :=
    frontier_eq_of_separation h₁ hU₁o hV₁o hU₁c hV₁c hU₁V₁disj hU₁V₁eq
  obtain ⟨hfrontU₂, hfrontV₂⟩ :=
    frontier_eq_of_separation h₂ hU₂o hV₂o hU₂c hV₂c hU₂V₂disj hU₂V₂eq
  -- each component lies in the complement of its curve
  have hU₁sub : U₁ ⊆ (Set.range γ₁)ᶜ := by rw [← hU₁V₁eq]; exact subset_union_left
  have hV₁sub : V₁ ⊆ (Set.range γ₁)ᶜ := by rw [← hU₁V₁eq]; exact subset_union_right
  have hU₂sub : U₂ ⊆ (Set.range γ₂)ᶜ := by rw [← hU₂V₂eq]; exact subset_union_left
  have hV₂sub : V₂ ⊆ (Set.range γ₂)ᶜ := by rw [← hU₂V₂eq]; exact subset_union_right
  -- the curve is a limit set of its two components
  have hK₁clU₁ : Set.range γ₁ ⊆ closure U₁ := by rw [← hfrontU₁]; exact frontier_subset_closure
  have hK₂clU₂ : Set.range γ₂ ⊆ closure U₂ := by rw [← hfrontU₂]; exact frontier_subset_closure
  have hclU₁ : closure U₁ = U₁ ∪ Set.range γ₁ := by
    rw [closure_eq_self_union_frontier_of_isOpen hU₁o, hfrontU₁]
  have hclU₂ : closure U₂ = U₂ ∪ Set.range γ₂ := by
    rw [closure_eq_self_union_frontier_of_isOpen hU₂o, hfrontU₂]
  -- the complement of an unbounded component is the closed region bounded by the curve
  have hcomplV₁ : V₁ᶜ = U₁ ∪ Set.range γ₁ := by
    ext z
    constructor
    · intro hz
      by_cases hzK : z ∈ Set.range γ₁
      · exact Or.inr hzK
      · exact Or.inl (by
          have h : z ∈ U₁ ∪ V₁ := by rw [hU₁V₁eq]; exact hzK
          exact h.resolve_right hz)
    · intro hz hzV
      rcases hz with hzU | hzK
      · exact (Set.disjoint_left.mp hU₁V₁disj) hzU hzV
      · exact (hV₁sub hzV) hzK
  have hcomplV₂ : V₂ᶜ = U₂ ∪ Set.range γ₂ := by
    ext z
    constructor
    · intro hz
      by_cases hzK : z ∈ Set.range γ₂
      · exact Or.inr hzK
      · exact Or.inl (by
          have h : z ∈ U₂ ∪ V₂ := by rw [hU₂V₂eq]; exact hzK
          exact h.resolve_right hz)
    · intro hz hzV
      rcases hz with hzU | hzK
      · exact (Set.disjoint_left.mp hU₂V₂disj) hzU hzV
      · exact (hV₂sub hzV) hzK
  -- a point in both unbounded components
  obtain ⟨p, hpV₁, hpV₂⟩ := exists_mem_inter_exteriors hU₁b hU₂b hU₁V₁eq hU₂V₂eq
  have hpX : p ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ := by
    intro h
    rcases h with h | h
    · exact hV₁sub hpV₁ h
    · exact hV₂sub hpV₂ h
  -- every preconnected piece of `X` lies on one side of each curve
  have hside₁ : ∀ S : Set ℂ, IsPreconnected S → S ⊆ (Set.range γ₁ ∪ Set.range γ₂)ᶜ →
      S ⊆ U₁ ∨ S ⊆ V₁ := by
    intro S hSpre hSX
    refine hSpre.subset_or_subset hU₁o hV₁o hU₁V₁disj ?_
    intro z hz
    rw [hU₁V₁eq]
    intro hzK₁
    exact hSX hz (Or.inl hzK₁)
  have hside₂ : ∀ S : Set ℂ, IsPreconnected S → S ⊆ (Set.range γ₁ ∪ Set.range γ₂)ᶜ →
      S ⊆ U₂ ∨ S ⊆ V₂ := by
    intro S hSpre hSX
    refine hSpre.subset_or_subset hU₂o hV₂o hU₂V₂disj ?_
    intro z hz
    rw [hU₂V₂eq]
    intro hzK₂
    exact hSX hz (Or.inr hzK₂)
  -- two points on opposite sides of one curve are never in the same preconnected piece
  have hpair₁ : ∀ S : Set ℂ, IsPreconnected S → S ⊆ (Set.range γ₁ ∪ Set.range γ₂)ᶜ →
      ∀ t t' : ℂ, t ∈ S → t' ∈ S → t ∈ U₁ → t' ∈ V₁ → False := by
    intro S hSpre hSX t t' htS ht'S htU ht'V
    rcases hside₁ S hSpre hSX with h | h
    · exact (Set.disjoint_left.mp hU₁V₁disj) (h ht'S) ht'V
    · exact (Set.disjoint_left.mp hU₁V₁disj) htU (h htS)
  have hpair₂ : ∀ S : Set ℂ, IsPreconnected S → S ⊆ (Set.range γ₁ ∪ Set.range γ₂)ᶜ →
      ∀ t t' : ℂ, t ∈ S → t' ∈ S → t ∈ U₂ → t' ∈ V₂ → False := by
    intro S hSpre hSX t t' htS ht'S htU ht'V
    rcases hside₂ S hSpre hSX with h | h
    · exact (Set.disjoint_left.mp hU₂V₂disj) (h ht'S) ht'V
    · exact (Set.disjoint_left.mp hU₂V₂disj) htU (h htS)
  -- the two curves cannot be nested in each other
  have hkey : ¬ (Set.range γ₁ ⊆ U₂ ∧ Set.range γ₂ ⊆ U₁) := by
    rintro ⟨hK₁U₂, hK₂U₁⟩
    have hV₁V₂ : V₁ ⊆ V₂ := by
      have hsub : V₁ ⊆ U₂ ∪ V₂ := by
        rw [hU₂V₂eq]
        intro z hz hzK₂
        exact (Set.disjoint_left.mp hU₁V₁disj) (hK₂U₁ hzK₂) hz
      rcases hV₁c.isPreconnected.subset_or_subset hU₂o hV₂o hU₂V₂disj hsub with h | h
      · exact absurd (hU₂b.subset h) hV₁unb
      · exact h
    have hV₂V₁ : V₂ ⊆ V₁ := by
      have hsub : V₂ ⊆ U₁ ∪ V₁ := by
        rw [hU₁V₁eq]
        intro z hz hzK₁
        exact (Set.disjoint_left.mp hU₂V₂disj) (hK₁U₂ hzK₁) hz
      rcases hV₂c.isPreconnected.subset_or_subset hU₁o hV₁o hU₁V₁disj hsub with h | h
      · exact absurd (hU₁b.subset h) hV₂unb
      · exact h
    have hVeq : V₁ = V₂ := Subset.antisymm hV₁V₂ hV₂V₁
    have hKeq : Set.range γ₁ = Set.range γ₂ := by rw [← hfrontV₁, ← hfrontV₂, hVeq]
    obtain ⟨w, hw⟩ := Set.range_nonempty γ₁
    exact (Set.disjoint_left.mp hdisj) hw (hKeq ▸ hw)
  -- when one bounded component misses the other curve the curve lies in the other component
  have hK₁U₂_of : ¬ (U₁ ∩ V₂).Nonempty → Set.range γ₁ ⊆ U₂ := by
    intro hB z hzK₁
    have hsub : U₁ ⊆ U₂ ∪ Set.range γ₂ := by
      intro w hw
      have hwV₂c : w ∈ V₂ᶜ := fun hwV₂ => hB ⟨w, hw, hwV₂⟩
      rwa [hcomplV₂] at hwV₂c
    have hzcl : z ∈ closure (U₂ ∪ Set.range γ₂) := closure_mono hsub (hK₁clU₁ hzK₁)
    rw [closure_union, hclU₂, (isCompact_range γ₂.continuous).isClosed.closure_eq] at hzcl
    rcases hzcl with h | h
    · rcases h with h | h
      · exact h
      · exact ((Set.disjoint_left.mp hdisj) hzK₁ h).elim
    · exact ((Set.disjoint_left.mp hdisj) hzK₁ h).elim
  have hK₂U₁_of : ¬ (V₁ ∩ U₂).Nonempty → Set.range γ₂ ⊆ U₁ := by
    intro hC z hzK₂
    have hsub : U₂ ⊆ U₁ ∪ Set.range γ₁ := by
      intro w hw
      have hwV₁c : w ∈ V₁ᶜ := fun hwV₁ => hC ⟨w, hwV₁, hw⟩
      rwa [hcomplV₁] at hwV₁c
    have hzcl : z ∈ closure (U₁ ∪ Set.range γ₁) := closure_mono hsub (hK₂clU₂ hzK₂)
    rw [closure_union, hclU₁, (isCompact_range γ₁.continuous).isClosed.closure_eq] at hzcl
    rcases hzcl with h | h
    · rcases h with h | h
      · exact h
      · exact ((Set.disjoint_left.mp hdisj) h hzK₂).elim
    · exact ((Set.disjoint_left.mp hdisj) h hzK₂).elim
  -- if the two bounded components are disjoint the curves lie side by side
  have hU₁V₂_of : ¬ (U₁ ∩ U₂).Nonempty → U₁ ⊆ V₂ := by
    intro hA
    have hdisjU₁K₂ : Disjoint U₁ (Set.range γ₂) := by
      rw [Set.disjoint_left]
      intro z hzU₁ hzK₂
      obtain ⟨w, hwU₁, hwU₂⟩ := mem_closure_iff.mp (hK₂clU₂ hzK₂) U₁ hU₁o hzU₁
      exact hA ⟨w, hwU₁, hwU₂⟩
    have hsub : U₁ ⊆ (Set.range γ₂)ᶜ := fun z hz hzK₂ =>
      (Set.disjoint_left.mp hdisjU₁K₂) hz hzK₂
    rcases hU₁c.isPreconnected.subset_or_subset hU₂o hV₂o hU₂V₂disj
      (by rw [hU₂V₂eq]; exact hsub) with h | h
    · obtain ⟨u, hu⟩ := hU₁c.nonempty
      exact absurd ⟨u, hu, h hu⟩ hA
    · exact h
  have hU₂V₁_of : ¬ (U₁ ∩ U₂).Nonempty → U₂ ⊆ V₁ := by
    intro hA
    have hdisjU₂K₁ : Disjoint U₂ (Set.range γ₁) := by
      rw [Set.disjoint_left]
      intro z hzU₂ hzK₁
      obtain ⟨w, hwU₂, hwU₁⟩ := mem_closure_iff.mp (hK₁clU₁ hzK₁) U₂ hU₂o hzU₂
      exact hA ⟨w, hwU₁, hwU₂⟩
    have hsub : U₂ ⊆ (Set.range γ₁)ᶜ := fun z hz hzK₁ =>
      (Set.disjoint_left.mp hdisjU₂K₁) hz hzK₁
    rcases hU₂c.isPreconnected.subset_or_subset hU₁o hV₁o hU₁V₁disj
      (by rw [hU₁V₁eq]; exact hsub) with h | h
    · obtain ⟨u, hu⟩ := hU₂c.nonempty
      exact absurd ⟨u, h hu, hu⟩ hA
    · exact h
  -- the final contradiction
  rintro ⟨P, Q, hPpre, hQpre, hPne, hQne, hPQdisj, hPXQ⟩
  have kill : ∀ t₁ t₂ t₃ : ℂ, t₁ ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ →
      t₂ ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ → t₃ ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ →
      (∀ S : Set ℂ, IsPreconnected S → S ⊆ (Set.range γ₁ ∪ Set.range γ₂)ᶜ →
        ¬ (t₁ ∈ S ∧ t₂ ∈ S) ∧ ¬ (t₁ ∈ S ∧ t₃ ∈ S) ∧ ¬ (t₂ ∈ S ∧ t₃ ∈ S)) → False := by
    intro t₁ t₂ t₃ ht₁ ht₂ ht₃ hsep
    exact not_cover_of_three_separated (Set.range γ₁ ∪ Set.range γ₂)ᶜ ht₁ ht₂ ht₃ hsep
      ⟨P, Q, hPpre, hQpre, hPne, hQne, hPQdisj, hPXQ⟩
  by_cases hA : (U₁ ∩ U₂).Nonempty
  · -- both bounded components meet: two further classes are nonempty
    obtain ⟨a, haU₁, haU₂⟩ := hA
    have haX : a ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ := by
      intro h
      rcases h with h | h
      · exact hU₁sub haU₁ h
      · exact hU₂sub haU₂ h
    have hBC : (U₁ ∩ V₂).Nonempty ∨ (V₁ ∩ U₂).Nonempty := by
      by_contra hcon
      rw [not_or] at hcon
      exact hkey ⟨hK₁U₂_of hcon.1, hK₂U₁_of hcon.2⟩
    rcases hBC with ⟨t, htU₁, htV₂⟩ | ⟨t, htV₁, htU₂⟩
    · have htX : t ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ := by
        intro h
        rcases h with h | h
        · exact hU₁sub htU₁ h
        · exact hV₂sub htV₂ h
      refine kill a t p haX htX hpX ?_
      intro S hSpre hSX
      exact ⟨fun ⟨haS, htS⟩ => hpair₂ S hSpre hSX a t haS htS haU₂ htV₂,
        fun ⟨haS, hpS⟩ => hpair₁ S hSpre hSX a p haS hpS haU₁ hpV₁,
        fun ⟨htS, hpS⟩ => hpair₁ S hSpre hSX t p htS hpS htU₁ hpV₁⟩
    · have htX : t ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ := by
        intro h
        rcases h with h | h
        · exact hV₁sub htV₁ h
        · exact hU₂sub htU₂ h
      refine kill a t p haX htX hpX ?_
      intro S hSpre hSX
      exact ⟨fun ⟨haS, htS⟩ => hpair₁ S hSpre hSX a t haS htS haU₁ htV₁,
        fun ⟨haS, hpS⟩ => hpair₁ S hSpre hSX a p haS hpS haU₁ hpV₁,
        fun ⟨htS, hpS⟩ => hpair₂ S hSpre hSX t p htS hpS htU₂ hpV₂⟩
  · -- the two bounded components are disjoint: the curves lie side by side
    obtain ⟨b, hbU₁⟩ := hU₁c.nonempty
    obtain ⟨c, hcU₂⟩ := hU₂c.nonempty
    have hbV₂ : b ∈ V₂ := hU₁V₂_of hA hbU₁
    have hcV₁ : c ∈ V₁ := hU₂V₁_of hA hcU₂
    have hbX : b ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ := by
      intro h
      rcases h with h | h
      · exact hU₁sub hbU₁ h
      · exact hV₂sub hbV₂ h
    have hcX : c ∈ (Set.range γ₁ ∪ Set.range γ₂)ᶜ := by
      intro h
      rcases h with h | h
      · exact hV₁sub hcV₁ h
      · exact hU₂sub hcU₂ h
    refine kill b c p hbX hcX hpX ?_
    intro S hSpre hSX
    exact ⟨fun ⟨hbS, hcS⟩ => hpair₁ S hSpre hSX b c hbS hcS hbU₁ hcV₁,
      fun ⟨hbS, hpS⟩ => hpair₁ S hSpre hSX b p hbS hpS hbU₁ hpV₁,
      fun ⟨hcS, hpS⟩ => hpair₂ S hSpre hSX c p hcS hpS hcU₂ hpV₂⟩

end

end Work.PlanarSC
