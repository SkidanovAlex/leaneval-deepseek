import Mathlib

namespace Work.Horn.HB

/-- A connected component of a point in a subset `F` is closed *inside* `F`: hence if `y ∈ F`
lies in the ambient closure of `connectedComponentIn F x`, then it already lies in it. -/
theorem mem_connectedComponentIn_of_mem_closure {α : Type*} [TopologicalSpace α]
    {F : Set α} {x y : α} (hy : y ∈ F)
    (h : y ∈ closure (connectedComponentIn F x)) : y ∈ connectedComponentIn F x := by
  by_cases hx : x ∈ F
  · set C : Set F := connectedComponent (⟨x, hx⟩ : F) with hCdef
    have hcc : connectedComponentIn F x = Subtype.val '' C := by
      rw [hCdef, connectedComponentIn_eq_image hx]
    have hind := Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image C
    have hCe : closure C = C := IsClosed.closure_eq isClosed_connectedComponent
    have hpre : Subtype.val ⁻¹' closure (Subtype.val '' C) = C := by
      rw [← hind, hCe]
    have h2 : (⟨y, hy⟩ : F) ∈ Subtype.val ⁻¹' closure (Subtype.val '' C) := by
      rw [Set.mem_preimage, ← hcc]
      exact h
    rw [hpre] at h2
    rw [hcc]
    exact ⟨⟨y, hy⟩, h2, rfl⟩
  · rw [connectedComponentIn_eq_empty hx] at h
    simp at h

/-- The finite-local-monodromy (LF) condition is inherited by smaller balls: if the components of
`D ∩ g ⁻¹' ball v r` are proper over `ball v r`, then those of `D ∩ g ⁻¹' ball v ρ` are proper
over `ball v ρ` for every `ρ ≤ r`.

The point is that the small component is contained in the big one (compactness of the big set),
and it is closed: a limit point of it lies in the big compact set, hence in `D` with `g`-image in
`ball v ρ`, and it is a limit point of the small component, which is closed in `D ∩ g ⁻¹' ball v ρ`. -/
theorem LF_smaller_ball {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {r ρ : ℝ} (hρr : ρ ≤ r)
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K)) :
    ∀ x ∈ D, g x ∈ Metric.ball v ρ → ∀ K ⊆ Metric.ball v ρ, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x ∩ g ⁻¹' K) := by
  intro x hxD hxρ K hKsub hKc
  have hball : Metric.ball v ρ ⊆ Metric.ball v r := Metric.ball_subset_ball hρr
  have hsub : (D ∩ g ⁻¹' Metric.ball v ρ) ⊆ (D ∩ g ⁻¹' Metric.ball v r) :=
    Set.inter_subset_inter subset_rfl (Set.preimage_mono hball)
  have hcc : connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x
      ⊆ connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x := connectedComponentIn_mono x hsub
  have hLFr : IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K) :=
    hLF x hxD (hball hxρ) K (hKsub.trans hball) hKc
  have hLr_closed : IsClosed (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K) :=
    hLFr.isClosed
  have hsub2 : connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x ∩ g ⁻¹' K
      ⊆ connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K :=
    Set.inter_subset_inter hcc subset_rfl
  have hclosed : IsClosed (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x ∩ g ⁻¹' K) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have hyLr : y ∈ connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K := by
      have h1 : y ∈ closure (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K) :=
        closure_mono hsub2 hy
      rwa [hLr_closed.closure_eq] at h1
    have hycc_le : y ∈ closure (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v ρ) x) :=
      closure_mono Set.inter_subset_left hy
    obtain ⟨hycc_r, hyK⟩ := hyLr
    have hyD : y ∈ D := (connectedComponentIn_subset (D ∩ g ⁻¹' Metric.ball v r) x hycc_r).1
    have hyballρ : g y ∈ Metric.ball v ρ := hKsub hyK
    have hySρ : y ∈ D ∩ g ⁻¹' Metric.ball v ρ := ⟨hyD, hyballρ⟩
    exact ⟨mem_connectedComponentIn_of_mem_closure hySρ hycc_le, hyK⟩
  exact IsCompact.of_isClosed_subset hLFr hclosed hsub2

end Work.Horn.HB
