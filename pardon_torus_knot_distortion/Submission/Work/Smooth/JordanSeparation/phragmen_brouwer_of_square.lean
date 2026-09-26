import Mathlib

/-!
# Phragmén–Brouwer for two disjoint compact plane sets, from the square lemma

The classical **Phragmén–Brouwer (Alexander) lemma** in the plane says: for two compact sets
`A, B ⊆ ℂ` with `A ∩ B = ∅` and a point `x` outside both, the intersection of the connected
component of `x` in `Aᶜ` with the connected component of `x` in `Bᶜ` is exactly the connected
component of `x` in `(A ∪ B)ᶜ`.

This file proves it from the **square lemma** — the elementary fact that in the unit square,
two closed sets, one missing the left edge and the other the right edge, whose union misses the
bottom and the top edge, cannot separate the bottom from the top.  This lemma is taken here as the
hypothesis `hsq`, so that the present file reduces the planar statement to that input.

## The argument

The inclusion `connectedComponentIn (A ∪ B)ᶜ x ⊆ connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x`
is formal (`connectedComponentIn_mono`, since `(A ∪ B)ᶜ ⊆ Aᶜ` and `(A ∪ B)ᶜ ⊆ Bᶜ`).

For the converse, let `y` lie in both components.  Since `A` and `B` are compact, `Aᶜ` and `Bᶜ` are
open; an open connected subset of a locally path connected space is path connected
(`IsOpen.isConnected_iff_isPathConnected`), so there are paths `α` in `Aᶜ` and `β` in `Bᶜ` from
`x` to `y` (`joinedIn_of_mem_connectedComponentIn` below).  The straight-line homotopy

`H (u, v) = (1 - u) • α (r v) + u • β (r v)`   (`r = Set.projIcc 0 1`)

maps the bottom edge of the square to `x`, the top edge to `y`, the left edge into `Aᶜ` and the
right edge into `Bᶜ`.  Hence `S₁ = H ⁻¹' A` and `S₂ = H ⁻¹' B` are closed, disjoint, `S₁` misses the
left edge, `S₂` the right edge, and `S₁ ∪ S₂` misses the bottom and the top edge.  The square
lemma `hsq` then furnishes a preconnected subset `K` of the square, avoiding `S₁ ∪ S₂`, joining
`(0,0)` to `(0,1)`.  Its image `H '' K` is a preconnected subset of `(A ∪ B)ᶜ` containing `x` and
`y`, so `y` lies in the component of `x` in `(A ∪ B)ᶜ`.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- In a locally path connected space, two points lying in the same connected component of an open
set are joined by a path inside that set. -/
theorem joinedIn_of_mem_connectedComponentIn {α : Type*} [TopologicalSpace α]
    [LocallyPathConnectedSpace α] {U : Set α} (hU : IsOpen U) {x y : α} (hx : x ∈ U)
    (h : y ∈ connectedComponentIn U x) : JoinedIn U x y := by
  have hpc : IsPathConnected (connectedComponentIn U x) :=
    ((hU.connectedComponentIn).isConnected_iff_isPathConnected).mp
      ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
  obtain ⟨γ, hγ⟩ := hpc.joinedIn x (mem_connectedComponentIn hx) y h
  exact ⟨γ, fun t => connectedComponentIn_subset U x (hγ t)⟩

/-- **Phragmén–Brouwer for two disjoint compact plane sets, from the square lemma.**

If the square lemma `hsq` holds, then for disjoint compact `A B ⊆ ℂ` and `x ∉ A ∪ B` the
intersection of the components of `x` in `Aᶜ` and in `Bᶜ` is the component of `x` in `(A ∪ B)ᶜ`. -/
theorem phragmen_brouwer_of_square {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) {x : ℂ} (hx : x ∉ A ∪ B)
    (hsq : ∀ {S1 S2 : Set (ℝ × ℝ)}, IsClosed S1 → IsClosed S2 → Disjoint S1 S2 →
      S1 ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ →
      S2 ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ →
      (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ →
      (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅ →
      ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S1 ∪ S2)ᶜ ((0, 0) : ℝ × ℝ)) :
    connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x = connectedComponentIn (A ∪ B)ᶜ x := by
  have hAcl : IsClosed A := hA.isClosed
  have hBcl : IsClosed B := hB.isClosed
  have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
  have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
  have hsubA : connectedComponentIn (A ∪ B)ᶜ x ⊆ connectedComponentIn Aᶜ x :=
    connectedComponentIn_mono x (fun z hz hzA => hz (Or.inl hzA))
  have hsubB : connectedComponentIn (A ∪ B)ᶜ x ⊆ connectedComponentIn Bᶜ x :=
    connectedComponentIn_mono x (fun z hz hzB => hz (Or.inr hzB))
  apply Subset.antisymm
  · -- the interesting inclusion, through the square lemma
    intro y hy
    obtain ⟨hyA, hyB⟩ := hy
    have hyAc : y ∈ Aᶜ := connectedComponentIn_subset Aᶜ x hyA
    have hyBc : y ∈ Bᶜ := connectedComponentIn_subset Bᶜ x hyB
    -- paths in `Aᶜ` and in `Bᶜ` from `x` to `y`
    obtain ⟨α, hαU⟩ : JoinedIn Aᶜ x y := joinedIn_of_mem_connectedComponentIn hAcl.isOpen_compl hxA hyA
    obtain ⟨β, hβU⟩ : JoinedIn Bᶜ x y := joinedIn_of_mem_connectedComponentIn hBcl.isOpen_compl hxB hyB
    have h01 : (0:ℝ) ≤ 1 := by norm_num
    -- the straight-line homotopy between the two paths, reparametrised to all of `ℝ × ℝ`
    set H : ℝ × ℝ → ℂ := fun p =>
      (1 - p.1) * α (Set.projIcc 0 1 h01 p.2) + p.1 * β (Set.projIcc 0 1 h01 p.2) with hH
    have hHc : Continuous H := by rw [hH]; fun_prop
    set S₁ : Set (ℝ × ℝ) := H ⁻¹' A with hS₁
    set S₂ : Set (ℝ × ℝ) := H ⁻¹' B with hS₂
    have hmS₁ : ∀ z : ℝ × ℝ, z ∈ S₁ ↔ H z ∈ A := fun z => by rw [hS₁]; rfl
    have hmS₂ : ∀ z : ℝ × ℝ, z ∈ S₂ ↔ H z ∈ B := fun z => by rw [hS₂]; rfl
    have hS₁c : IsClosed S₁ := by rw [hS₁]; exact hAcl.preimage hHc
    have hS₂c : IsClosed S₂ := by rw [hS₂]; exact hBcl.preimage hHc
    have hSdisj : Disjoint S₁ S₂ := by
      rw [Set.disjoint_left]
      intro z hz₁ hz₂
      exact Set.disjoint_left.mp hAB ((hmS₁ z).mp hz₁) ((hmS₂ z).mp hz₂)
    -- values of `H` on the four edges
    have hleft : ∀ v : ℝ, H (0, v) = α (Set.projIcc 0 1 h01 v) := by intro v; simp [hH]
    have hright : ∀ v : ℝ, H (1, v) = β (Set.projIcc 0 1 h01 v) := by intro v; simp [hH]
    have hp0 : Set.projIcc 0 1 h01 (0:ℝ) = (0 : Set.Icc (0:ℝ) 1) := by
      apply Subtype.ext; rw [Set.projIcc_of_mem h01 ⟨le_rfl, zero_le_one⟩]; rfl
    have hp1 : Set.projIcc 0 1 h01 (1:ℝ) = (1 : Set.Icc (0:ℝ) 1) := by
      apply Subtype.ext; rw [Set.projIcc_of_mem h01 ⟨zero_le_one, le_rfl⟩]; rfl
    have hbot : ∀ u : ℝ, H (u, 0) = x := by
      intro u; simp only [hH]; rw [hp0, α.source, β.source]; ring
    have htop : ∀ u : ℝ, H (u, 1) = y := by
      intro u; simp only [hH]; rw [hp1, α.target, β.target]; ring
    -- the four edge conditions for the square lemma
    have hL : S₁ ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = α (Set.projIcc 0 1 h01 v) := by rw [hu]; exact hleft v
      exact hαU _ (hHu ▸ (hmS₁ _).mp h1)
    have hR : S₂ ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = β (Set.projIcc 0 1 h01 v) := by rw [hu]; exact hright v
      exact hβU _ (hHu ▸ (hmS₂ _).mp h1)
    have hBtm : (S₁ ∪ S₂) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = x := by rw [hv]; exact hbot u
      rcases h1 with h | h
      · exact hx (Or.inl (hHu ▸ (hmS₁ _).mp h))
      · exact hx (Or.inr (hHu ▸ (hmS₂ _).mp h))
    have hTop : (S₁ ∪ S₂) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨h1, h2⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
      obtain ⟨hu, hv⟩ := h2
      have hHu : H (u, v) = y := by rw [hv]; exact htop u
      rcases h1 with h | h
      · exact hyAc (hHu ▸ (hmS₁ _).mp h)
      · exact hyBc (hHu ▸ (hmS₂ _).mp h)
    -- the square lemma
    have hkey : ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S₁ ∪ S₂)ᶜ ((0, 0) : ℝ × ℝ) :=
      hsq hS₁c hS₂c hSdisj hL hR hBtm hTop
    set K : Set (ℝ × ℝ) := connectedComponentIn (S₁ ∪ S₂)ᶜ ((0, 0) : ℝ × ℝ) with hK
    have hKpre : IsPreconnected K := by rw [hK]; exact isPreconnected_connectedComponentIn
    have hKsub : K ⊆ (S₁ ∪ S₂)ᶜ := by rw [hK]; exact connectedComponentIn_subset _ _
    have h00K : ((0, 0) : ℝ × ℝ) ∈ K := by
      rw [hK]
      refine mem_connectedComponentIn ?_
      rw [Set.mem_compl_iff, Set.mem_union, not_or, hmS₁, hmS₂]
      exact ⟨fun h => hx (Or.inl (hbot 0 ▸ h)), fun h => hx (Or.inr (hbot 0 ▸ h))⟩
    have h01K : ((0, 1) : ℝ × ℝ) ∈ K := by rw [hK]; exact hkey
    -- push `K` forward along the homotopy
    have hImpre : IsPreconnected (H '' K) := hKpre.image H hHc.continuousOn
    have hImsub : H '' K ⊆ (A ∪ B)ᶜ := by
      rintro z ⟨p, hp, rfl⟩
      have hp' := hKsub hp
      rw [Set.mem_compl_iff, Set.mem_union, not_or] at hp'
      rw [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨fun h => hp'.1 ((hmS₁ p).mpr h), fun h => hp'.2 ((hmS₂ p).mpr h)⟩
    have hxIm : x ∈ H '' K := ⟨(0, 0), h00K, hbot 0⟩
    have hfin := hImpre.subset_connectedComponentIn hxIm hImsub
    exact hfin ⟨(0, 1), h01K, htop 0⟩
  · -- the easy inclusion
    intro y hy
    exact ⟨hsubA hy, hsubB hy⟩

end

end Work.Smooth.JordanSeparation
