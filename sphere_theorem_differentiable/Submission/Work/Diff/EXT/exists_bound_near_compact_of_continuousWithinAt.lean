import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- A map `f : X → Y` that is continuous within `S` at every point of `S` is bounded on the
part of `S` lying in a small neighbourhood of a compact subset `C ⊆ S`.

Proof: at each `c ∈ C` the ε–δ form of `ContinuousWithinAt` (with `ε = 1`) gives a radius
`δ c > 0` on which `f` is bounded by `‖f c‖ + 1`; the balls `ball c (δ c / 2)` cover the compact
set `C`, so finitely many of them do; the uniform radius is `(min δ)/4` and the uniform bound is
the maximum of the finitely many local bounds. -/
theorem exists_bound_near_compact_of_continuousWithinAt
    {X : Type*} [PseudoMetricSpace X] {Y : Type*} [NormedAddCommGroup Y]
    {S C : Set X} (hCne : C.Nonempty) (hCS : C ⊆ S) (hC : IsCompact C) {f : X → Y}
    (hf : ∀ x ∈ S, ContinuousWithinAt f S x) :
    ∃ r > 0, ∃ M : ℝ, ∀ x ∈ S, (∃ c ∈ C, dist x c < r) → ‖f x‖ ≤ M := by
  -- Local boundedness at every point of `C`, within `S`.
  have hloc : ∀ c ∈ C, ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ S, dist y c < δ → dist (f y) (f c) < 1 := by
    intro c hc
    exact (Metric.continuousWithinAt_iff).1 (hf c (hCS hc)) 1 zero_lt_one
  choose δ hδpos hδbnd using hloc
  have hδpos' : ∀ c (hc : c ∈ C), 0 < δ c hc := hδpos
  have hδbnd' : ∀ c (hc : c ∈ C) (y : X), y ∈ S → dist y c < δ c hc → dist (f y) (f c) < 1 :=
    hδbnd
  -- The balls of radius `δ c / 2` cover the compact set `C`.
  have hcover : C ⊆ ⋃ c : C, Metric.ball (c : X) (δ c c.2 / 2) := by
    intro c hc
    refine Set.mem_iUnion.2 ⟨⟨c, hc⟩, ?_⟩
    simp only [Metric.mem_ball, dist_self]
    linarith [hδpos' c hc]
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : C => Metric.ball (c : X) (δ c c.2 / 2))
    (fun _ => Metric.isOpen_ball) hcover
  have htne : t.Nonempty := by
    obtain ⟨c0, hc0⟩ := hCne
    rcases Set.mem_iUnion₂.1 (ht hc0) with ⟨c, hct, _⟩
    exact ⟨c, hct⟩
  refine ⟨t.inf' htne (fun c : C => δ c c.2) / 4, ?_, t.sup' htne (fun c : C => ‖f c‖ + 1), ?_⟩
  · have hpos : 0 < t.inf' htne (fun c : C => δ c c.2) := by
      rw [Finset.lt_inf'_iff]
      intro c _
      exact hδpos' c c.2
    linarith
  · intro x hx ⟨c0, hc0C, hc0r⟩
    rcases Set.mem_iUnion₂.1 (ht hc0C) with ⟨i, hit, hi⟩
    have hi' : dist c0 (i : X) < δ i i.2 / 2 := by simpa [Metric.mem_ball] using hi
    have hδi : 0 < δ i i.2 := hδpos' i i.2
    have hrle : t.inf' htne (fun c : C => δ c c.2) ≤ δ i i.2 := Finset.inf'_le _ hit
    have hdist : dist x (i : X) < δ i i.2 := by
      have h1 : dist x (i : X) ≤ dist x c0 + dist c0 (i : X) := dist_triangle _ _ _
      linarith
    have hbnd : dist (f x) (f (i : X)) < 1 := hδbnd' i i.2 x hx hdist
    have hsup : ‖f (i : X)‖ + 1 ≤ t.sup' htne (fun c : C => ‖f c‖ + 1) :=
      Finset.le_sup' (fun c : C => ‖f c‖ + 1) hit
    have h1 : ‖f x‖ ≤ ‖f (i : X)‖ + ‖f (i : X) - f x‖ := norm_le_norm_add_norm_sub _ _
    rw [dist_eq_norm, norm_sub_rev] at hbnd
    linarith

end Work.Diff.EXT
