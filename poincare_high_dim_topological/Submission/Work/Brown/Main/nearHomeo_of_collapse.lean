import Mathlib
import Submission.Work.Brown.Basic
import Submission.Work.Brown.Engine.nearHomeo_of_fiber_shrinkable
import Submission.Work.Brown.Main.exists_homeomorph_shrink_compl_openCell

/-!
# The collapse of a cell-complement is a near homeomorphism

Let `f : 𝕊ⁿ → 𝕊ⁿ` be a continuous surjection whose only non-degenerate point inverse is a closed
set `K` whose complement is an open `n`-cell (`Kᶜ ≅ ℝⁿ`).  Then `f` is a near homeomorphism, i.e.
a uniform limit of homeomorphisms of `𝕊ⁿ`.

This is the special case of Uspenskij's shrinking criterion needed for the collapse sequence in
Brown's monotone union theorem: for a fibre `K` whose complement is an open cell, the shrinking
homeomorphism supplied by `Work.Brown.Main.exists_homeomorph_shrink_compl_openCell` can be
produced *without* any invariance-of-domain input, and Bing's shrinking criterion in the form
`Work.Brown.Engine.nearHomeo_of_fiber_shrinkable` then applies verbatim.
-/

namespace Work.Brown.Main

open Set Metric

/-- **A collapse of `𝕊ⁿ` with a single non-degenerate fibre whose complement is an open cell is
a near homeomorphism.** -/
theorem nearHomeo_of_collapse_compl_openCell {n : ℕ}
    (f : ↥(Metric.sphere (0 : PL.E (n + 1)) 1) → ↥(Metric.sphere (0 : PL.E (n + 1)) 1))
    (hc : Continuous f) (hsurj : Function.Surjective f)
    {K : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)} (hK : IsClosed K) (hKne : K.Nonempty)
    (hcell : PL.IsOpenCell n (Kᶜ : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)))
    (hfib : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ K ∧ y ∈ K)) :
    Work.Brown.IsNearHomeo f := by
  haveI : CompactSpace ↥(Metric.sphere (0 : PL.E (n + 1)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  refine Work.Brown.Engine.nearHomeo_of_fiber_shrinkable f hc hsurj ?_
  intro ε hε
  obtain ⟨k0, hk0⟩ := hKne
  set p : ↥(Metric.sphere (0 : PL.E (n + 1)) 1) := f k0 with hp
  set W : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1) := f ⁻¹' Metric.ball p (ε / 3) with hW
  have hWopen : IsOpen W := Metric.isOpen_ball.preimage hc
  have hKW : K ⊆ W := by
    intro x hx
    simp only [W, Set.mem_preimage, hp]
    rw [(hfib x k0).mpr (Or.inr ⟨hx, hk0⟩)]
    exact Metric.mem_ball_self (by linarith)
  obtain ⟨h, x0, hhid, hhK⟩ :=
    exists_homeomorph_shrink_compl_openCell hK hcell.2.some hWopen hKW
      (show (0 : ℝ) < ε / 2 by linarith)
  refine ⟨h, ?_, ?_⟩
  · -- `h` is `ε`-close to the identity in the `f`-sense
    intro x
    by_cases hx : x ∈ W
    · have hxW : h x ∈ W := by
        by_contra hcon
        have h1 : h (h x) = h x := hhid (h x) hcon
        have h2 : h x = x := h.injective h1
        exact hcon (by rw [h2]; exact hx)
      have h1 : f (h x) ∈ Metric.ball p (ε / 3) := hxW
      have h2 : f x ∈ Metric.ball p (ε / 3) := hx
      rw [Metric.mem_ball] at h1 h2
      calc dist (f (h x)) (f x) ≤ dist (f (h x)) p + dist p (f x) := dist_triangle _ _ _
        _ = dist (f (h x)) p + dist (f x) p := by rw [dist_comm p (f x)]
        _ < ε / 3 + ε / 3 := add_lt_add h1 h2
        _ < ε := by linarith
    · rw [hhid x hx, dist_self]
      exact hε
  · -- `h` shrinks the fibres of `f`
    intro x y hxy
    rcases (hfib x y).mp hxy with h' | ⟨hx, hy⟩
    · subst h'; rw [dist_self]; exact hε
    · have hx0 : h x ∈ Metric.ball x0 (ε / 2) := hhK (Set.mem_image_of_mem h hx)
      have hy0 : h y ∈ Metric.ball x0 (ε / 2) := hhK (Set.mem_image_of_mem h hy)
      rw [Metric.mem_ball] at hx0 hy0
      calc dist (h x) (h y) ≤ dist (h x) x0 + dist x0 (h y) := dist_triangle _ _ _
        _ = dist (h x) x0 + dist (h y) x0 := by rw [dist_comm x0 (h y)]
        _ < ε / 2 + ε / 2 := add_lt_add hx0 hy0
        _ = ε := by ring

end Work.Brown.Main
