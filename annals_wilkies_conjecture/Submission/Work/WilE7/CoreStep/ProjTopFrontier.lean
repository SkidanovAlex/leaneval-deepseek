/-
  `Work.WilE7.CoreStep.ProjTopFrontier`: two elementary set-theoretic lemmas the case-B step of
  `CoreLT_succ` uses.

  * `closure_projTop_subset`, `closure_diff_projTop_subset`: for a piece `S` inside the cube the
    closure of its `projTop`-image is already the image of the closure, so
    `closure (projTop S) \ projTop S ⊆ projTop (closure S \ S)` — this is BV's
    `∂π_n(X_α) ⊆ ⋃ π_n(Σ)` (the "the frontier of the projection is the projection of the
    frontier, up to the frontier of the piece"), and it is what lets the `Σ`-avoidance of a base
    cell remove `∂(π_{n+1}(T))` from the cylinder over that cell.

  * `preconnected_subset_or_disjoint_of_frontier`: if `A` is open and no point of `K` lies in
    `∂A`, then every preconnected subset of `K` is contained in `A` or disjoint from `A` (the
    "clopen" argument: `interior A` and `(closure A)ᶜ` are disjoint open sets covering `K`).
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopTransfer
import Submission.Work.WilE7.fiberCluster

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- For a piece `S` inside the cube, the closure of the `projTop`-image is the image of the
closure (the image of `closure S`, a compact set, is closed). -/
theorem closure_projTop_subset (n m : ℕ) {S : Set (Fin (n + (m + 1)) → ℝ)}
    (hS : S ⊆ cubeC (n + (m + 1))) :
    closure (projTop n m '' S) ⊆ projTop n m '' closure S := by
  have hcube : IsClosed (cubeC (n + (m + 1))) := (Work.WilE7.fc_cubeC_isCompact _).isClosed
  have hcl : IsClosed (projTop n m '' closure S) :=
    (((Work.WilE7.fc_cubeC_isCompact (n + (m + 1))).of_isClosed_subset isClosed_closure
        (closure_minimal hS hcube)).image (continuous_projTop n m)).isClosed
  exact closure_minimal (Set.image_mono subset_closure) hcl

/-- **BV's frontier-of-the-projection identity.**  The part of the closure of `projTop S` outside
`projTop S` comes from the part of `closure S` outside `S`. -/
theorem closure_diff_projTop_subset (n m : ℕ) {S : Set (Fin (n + (m + 1)) → ℝ)}
    (hS : S ⊆ cubeC (n + (m + 1))) :
    closure (projTop n m '' S) \ projTop n m '' S ⊆ projTop n m '' (closure S \ S) := by
  rintro p ⟨hpcl, hpnot⟩
  obtain ⟨z, hz, hzp⟩ := closure_projTop_subset n m hS hpcl
  refine ⟨z, ⟨hz, ?_⟩, hzp⟩
  intro hzS
  exact hpnot ⟨z, hzS, hzp⟩

/-- **The clopen argument.**  If `A` is open and no point of `K` lies in the frontier of `A`,
then every preconnected subset of `K` is contained in `A` or disjoint from `A`. -/
theorem preconnected_subset_or_disjoint_of_frontier {N : ℕ} {K A κ : Set (Fin N → ℝ)}
    (hAopen : IsOpen A) (hfront : ∀ p ∈ K, p ∈ frontier A → False)
    (hκK : κ ⊆ K) (hκpre : IsPreconnected κ) : κ ⊆ A ∨ Disjoint κ A := by
  have hdisj : Disjoint (interior A) ((closure A)ᶜ) :=
    Set.disjoint_left.mpr fun p hp hq => hq (subset_closure (interior_subset hp))
  have hcover : κ ⊆ interior A ∪ (closure A)ᶜ := by
    intro p hpκ
    by_cases hint : p ∈ interior A
    · exact Or.inl hint
    · refine Or.inr ?_
      intro hpcl
      exact hfront p (hκK hpκ) (by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨hpcl, by rw [closure_compl]; exact hint⟩)
  rcases hκpre.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl hdisj hcover with
    h | h
  · exact Or.inl fun p hp => interior_subset (h hp)
  · exact Or.inr (Set.disjoint_left.mpr fun p hp hq => h hp (subset_closure hq))

end Work.WilE7.CoreStep
