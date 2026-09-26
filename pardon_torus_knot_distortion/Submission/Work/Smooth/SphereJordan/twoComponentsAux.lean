import Mathlib

/-!
# Auxiliary topology for the Jordan separation on the sphere

Two elementary facts about connected components of the complement of a *closed* set in `ℂ`:

* a component of the complement of a closed set is open (`isOpen_connectedComponentIn_compl`);
* the **trace lemma** (`preconnected_subset_or_disjoint_connectedComponentIn`): if `A` is
  preconnected and disjoint from `M`, then every component of `Mᶜ` either contains `A` or is
  disjoint from it.
-/

open Set Metric

namespace Work.Smooth.SphereJordan.Aux

/-- For an **open** set `U`, the closure of its complement meets `U` in the empty set. -/
theorem inter_closure_compl_eq_empty {U : Set ℂ} (hU : IsOpen U) : U ∩ closure Uᶜ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨hxU, hxcl⟩ := hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨y, hyU, hyε⟩ := Metric.mem_closure_iff.mp hxcl (ε / 2) (by linarith)
  have hy : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_comm]; linarith
  exact hyU (hball hy)

/-- Components of the complement of a **closed** set of `ℂ` are open. -/
theorem isOpen_connectedComponentIn_compl {M : Set ℂ} (hM : IsClosed M) (x : ℂ) :
    IsOpen (connectedComponentIn Mᶜ x) := by
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hM.isOpen_compl y (connectedComponentIn_subset Mᶜ x hy)
  refine ⟨ε, hε, fun w hw => ?_⟩
  have hUpre : IsPreconnected (connectedComponentIn Mᶜ x) := isPreconnected_connectedComponentIn
  have hDpre : IsPreconnected (Metric.ball y ε) := Metric.isPreconnected_ball
  have hmeet : (connectedComponentIn Mᶜ x ∩ Metric.ball y ε).Nonempty :=
    ⟨y, hy, Metric.mem_ball_self hε⟩
  have hunion : IsPreconnected (connectedComponentIn Mᶜ x ∪ Metric.ball y ε) :=
    IsPreconnected.union' hmeet hUpre hDpre
  have hsub : connectedComponentIn Mᶜ x ∪ Metric.ball y ε ⊆ Mᶜ :=
    Set.union_subset (connectedComponentIn_subset Mᶜ x) hball
  have hyun : y ∈ connectedComponentIn Mᶜ x ∪ Metric.ball y ε := Or.inl hy
  have h1 : connectedComponentIn Mᶜ x ∪ Metric.ball y ε ⊆ connectedComponentIn Mᶜ y :=
    IsPreconnected.subset_connectedComponentIn hunion hyun hsub
  rw [← connectedComponentIn_eq hy] at h1
  exact h1 (Or.inr hw)

/-- Adding a point of the closure of a preconnected set keeps it preconnected. -/
theorem isPreconnected_insert_of_mem_closure {S : Set ℂ} {z : ℂ} (hS : IsPreconnected S)
    (hz : z ∈ closure S) : IsPreconnected (insert z S) :=
  hS.subset_closure (Set.subset_insert z S) (by
    intro w hw
    rcases hw with rfl | hw
    · exact hz
    · exact subset_closure hw)

/-- **Trace lemma.**  Let `M ⊆ ℂ` be closed, `A` preconnected with `A ∩ M = ∅`, and `x ∉ M`.  Then
the connected component of `x` in `Mᶜ` either contains `A` or is disjoint from it. -/
theorem preconnected_subset_or_disjoint_connectedComponentIn {M A : Set ℂ} (hM : IsClosed M)
    (hA : IsPreconnected A) (hAdisj : Disjoint A M) {x : ℂ} (hx : x ∉ M) :
    A ⊆ connectedComponentIn Mᶜ x ∨ Disjoint A (connectedComponentIn Mᶜ x) := by
  set U := connectedComponentIn Mᶜ x with hUdef
  have hUopen : IsOpen U := isOpen_connectedComponentIn_compl hM x
  have hUpre : IsPreconnected U := isPreconnected_connectedComponentIn
  have hUsub : U ⊆ Mᶜ := connectedComponentIn_subset Mᶜ x
  have hxU : x ∈ U := mem_connectedComponentIn (by simpa using hx)
  -- `A ∩ closure U ⊆ U`
  have hkey : A ∩ closure U ⊆ U := by
    intro z hz
    obtain ⟨hzA, hzcl⟩ := hz
    have hzM : z ∉ M := fun h => Set.disjoint_left.mp hAdisj hzA h
    have hins : IsPreconnected (insert z U) := isPreconnected_insert_of_mem_closure hUpre hzcl
    have hinsub : insert z U ⊆ Mᶜ := by
      intro w hw
      rcases hw with rfl | hw
      · exact hzM
      · exact hUsub hw
    have hxins : x ∈ insert z U := Set.mem_insert_of_mem z hxU
    have := IsPreconnected.subset_connectedComponentIn hins hxins hinsub
    exact this (Or.inl rfl)
  have hdisj : A ∩ (closure U ∩ closure Uᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨hzA, hzclU, hzclc⟩ := hz
    have hzU : z ∈ U := hkey ⟨hzA, hzclU⟩
    have : z ∈ U ∩ closure Uᶜ := ⟨hzU, hzclc⟩
    rw [inter_closure_compl_eq_empty hUopen] at this
    exact this
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hA) (closure U) (closure Uᶜ)
      isClosed_closure isClosed_closure (by
        intro z _
        show z ∈ closure U ∪ closure Uᶜ
        rw [← closure_union, Set.union_compl_self, closure_univ]
        trivial) hdisj with h | h
  · exact Or.inl fun z hz => hkey ⟨hz, h hz⟩
  · refine Or.inr (Set.disjoint_left.mpr fun z hzA hzU => ?_)
    have : z ∈ A ∩ (closure U ∩ closure Uᶜ) := ⟨hzA, subset_closure hzU, h hzA⟩
    rw [hdisj] at this
    exact this


/-- **At most two components, from a two-arc cover of the complement.**

If `A₁`, `A₂` are non-empty preconnected sets disjoint from the closed set `M`, and **every**
component of `Mᶜ` meets `A₁ ∪ A₂`, then of any three points off `M`, two lie in the same component.

By the trace lemma every component of `Mᶜ` either contains `A₁` or is disjoint from it; combining
with the hypothesis, every component contains `A₁` or `A₂`; and two components containing the same
`A_j` are equal (as `A_j ≠ ∅` and components are pairwise disjoint).  Hence a component is
determined by whether it contains `A₁`, so there are at most two. -/
theorem atMostTwo_of_trace {M : Set ℂ} (hM : IsClosed M) {A₁ A₂ : Set ℂ}
    (hA₁ne : A₁.Nonempty) (hA₂ne : A₂.Nonempty)
    (hA₁ : IsPreconnected A₁) (hA₂ : IsPreconnected A₂)
    (hdisj₁ : Disjoint A₁ M) (hdisj₂ : Disjoint A₂ M)
    (hmeet : ∀ p : ℂ, p ∉ M → (connectedComponentIn Mᶜ p ∩ (A₁ ∪ A₂)).Nonempty)
    {x y w : ℂ} (hx : x ∉ M) (hy : y ∉ M) (hw : w ∉ M) :
    connectedComponentIn Mᶜ x = connectedComponentIn Mᶜ y ∨
      connectedComponentIn Mᶜ x = connectedComponentIn Mᶜ w ∨
      connectedComponentIn Mᶜ y = connectedComponentIn Mᶜ w := by
  -- Every component contains `A₁` or `A₂`.
  have htype : ∀ p : ℂ, p ∉ M →
      A₁ ⊆ connectedComponentIn Mᶜ p ∨ A₂ ⊆ connectedComponentIn Mᶜ p := by
    intro p hp
    obtain ⟨a, ha, haA⟩ := hmeet p hp
    rcases haA with ha1 | ha2
    · exact Or.inl ((preconnected_subset_or_disjoint_connectedComponentIn hM hA₁ hdisj₁ hp).elim id
        (fun hd => absurd ha (Set.disjoint_left.mp hd ha1)))
    · exact Or.inr ((preconnected_subset_or_disjoint_connectedComponentIn hM hA₂ hdisj₂ hp).elim id
        (fun hd => absurd ha (Set.disjoint_left.mp hd ha2)))
  -- Two components containing the same `A_j` are equal.
  have hsame : ∀ p q : ℂ, p ∉ M → q ∉ M →
      (A₁ ⊆ connectedComponentIn Mᶜ p ↔ A₁ ⊆ connectedComponentIn Mᶜ q) →
      connectedComponentIn Mᶜ p = connectedComponentIn Mᶜ q := by
    intro p q hp hq hiff
    by_cases h1 : A₁ ⊆ connectedComponentIn Mᶜ p
    · obtain ⟨a, ha⟩ := hA₁ne
      exact (connectedComponentIn_eq (h1 ha)).trans (connectedComponentIn_eq ((hiff.mp h1) ha)).symm
    · have h2p : A₂ ⊆ connectedComponentIn Mᶜ p := (htype p hp).elim (fun h => absurd h h1) id
      have h2q : A₂ ⊆ connectedComponentIn Mᶜ q :=
        (htype q hq).elim (fun h => absurd (hiff.mpr h) h1) id
      obtain ⟨a, ha⟩ := hA₂ne
      exact (connectedComponentIn_eq (h2p ha)).trans (connectedComponentIn_eq (h2q ha)).symm
  -- Pigeonhole on the three truth values `A₁ ⊆ C ·`.
  by_cases hx1 : A₁ ⊆ connectedComponentIn Mᶜ x
  · by_cases hy1 : A₁ ⊆ connectedComponentIn Mᶜ y
    · exact Or.inl (hsame x y hx hy ⟨fun _ => hy1, fun _ => hx1⟩)
    · by_cases hw1 : A₁ ⊆ connectedComponentIn Mᶜ w
      · exact Or.inr (Or.inl (hsame x w hx hw ⟨fun _ => hw1, fun _ => hx1⟩))
      · exact Or.inr (Or.inr (hsame y w hy hw ⟨fun h => absurd h hy1, fun h => absurd h hw1⟩))
  · by_cases hy1 : A₁ ⊆ connectedComponentIn Mᶜ y
    · by_cases hw1 : A₁ ⊆ connectedComponentIn Mᶜ w
      · exact Or.inr (Or.inr (hsame y w hy hw ⟨fun _ => hw1, fun _ => hy1⟩))
      · exact Or.inr (Or.inl (hsame x w hx hw ⟨fun h => absurd h hx1, fun h => absurd h hw1⟩))
    · exact Or.inl (hsame x y hx hy ⟨fun h => absurd h hx1, fun h => absurd h hy1⟩)

end Work.Smooth.SphereJordan.Aux
