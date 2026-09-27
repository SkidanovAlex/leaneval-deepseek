import Mathlib
import Submission.Work.Whitney.PathTools.exists_arc_of_isPathConnected

/-!
# A preconnected open cover of a compact set avoiding a disjoint closed set

Given a compact `K` and a closed `Z` disjoint from it, there are finitely many **preconnected**
open sets `N p` covering `K`, each meeting `K`, and each with `closure (N p)` disjoint from `Z`.

This is the local building block of the collar construction
(`Work.Noncompact.CompressionTube.collar_pocketFree`): the collar `L = B ∩ Uᶜ` is obtained by
subtracting an open set `U` which

* covers the frontier of `B` — here `K = frontier B` and `Z = A`;
* covers the prescribed points `S` and the image of an arc running from a point of `B` to a point
  outside `B`, avoiding `A` — here `K = γ '' Icc 0 1` and `Z = A`.

In both cases the finitely many preconnected pieces of the cover are the connected pieces of `U`,
and the fact that each piece meets `K` is what makes every component of `U` meet `Bᶜ`.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **Preconnected open covers of a compact set avoiding a disjoint closed set.** -/
theorem exists_preconnected_open_cover {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {K Z : Set M} (hKc : IsCompact K) (hZc : IsClosed Z) (hKZ : Disjoint K Z) :
    ∃ (N : K → Set M) (s : Finset K) (b : (p : K) → Work.Whitney.PathTools.ChartBall n M Zᶜ (p : M)),
      (∀ p, N p = (b p).c.symm '' Metric.ball ((b p).c (p : M)) (b p).ρ) ∧
      (∀ p, IsOpen (N p)) ∧ (∀ p, IsPreconnected (N p)) ∧
      K ⊆ ⋃ p ∈ s, N p ∧ (∀ p, Disjoint Z (closure (N p))) ∧
      (∀ p ∈ s, (N p ∩ K).Nonempty) := by
  classical
  have hex : ∀ p : K, Nonempty (Work.Whitney.PathTools.ChartBall n M Zᶜ (p : M)) := by
    intro p
    exact Work.Whitney.PathTools.exists_chartBall (n := n) (M := M) (W := Zᶜ)
      (hZc.isOpen_compl) (by
        simp only [Set.mem_compl_iff]
        exact fun h => (Set.disjoint_left.mp hKZ p.2) h)
  let B : (p : K) → Work.Whitney.PathTools.ChartBall n M Zᶜ (p : M) :=
    fun p => Classical.choice (hex p)
  have hcover : K ⊆ ⋃ p : K, (B p).c.symm '' Metric.ball ((B p).c (p : M)) (B p).ρ := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact ⟨(B ⟨x, hx⟩).c (x : M), Metric.mem_ball_self (B ⟨x, hx⟩).hρ,
      (B ⟨x, hx⟩).c.left_inv (B ⟨x, hx⟩).hz⟩
  obtain ⟨s, hs⟩ := hKc.elim_finite_subcover
    (fun p : K => (B p).c.symm '' Metric.ball ((B p).c (p : M)) (B p).ρ)
    (fun p => Work.Whitney.PathTools.ChartBall.ballImage_open (B p)) hcover
  refine ⟨fun p => (B p).c.symm '' Metric.ball ((B p).c (p : M)) (B p).ρ, s, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rfl
  · intro p; exact Work.Whitney.PathTools.ChartBall.ballImage_open (B p)
  · intro p
    refine IsPreconnected.image ?_ (B p).c.symm ((B p).c.continuousOn_symm.mono ?_)
    · exact (convex_ball ((B p).c (p : M)) (B p).ρ).isPreconnected
    · intro w hw
      exact (B p).hclosed (Metric.ball_subset_closedBall hw)
  · intro x hx
    have h := hs hx
    simp only [Set.mem_iUnion] at h ⊢
    obtain ⟨p, hp, hxp⟩ := h
    exact ⟨p, hp, hxp⟩
  · intro p
    rw [Set.disjoint_left]
    intro z hz hzcl
    have hsub : (B p).c.symm '' Metric.ball ((B p).c (p : M)) (B p).ρ ⊆ (B p).K :=
      Work.Whitney.PathTools.ChartBall.ballImage_subset_K (B p)
    have hzK : z ∈ (B p).K := closure_minimal hsub (B p).isClosed_K hzcl
    exact (Work.Whitney.PathTools.ChartBall.K_subset_W (B p) hzK) hz
  · intro p _
    exact ⟨(p : M), ⟨(B p).c (p : M), Metric.mem_ball_self (B p).hρ,
      (B p).c.left_inv (B p).hz⟩, p.2⟩

end Work.Noncompact.CompressionTube
