import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Covering.Basic

open Filter Set
open scoped Topology

namespace Commons.Topology.Covering

/-- If `x` is evenly covered by `f`, then the cardinality of the fibre of `f` is locally constant
near `x`. -/
theorem eventually_natCard_fiber_eq_of_isEvenlyCovered {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {f : E → B} {x : B}
    (h : IsEvenlyCovered f x (f ⁻¹' {x})) :
    ∀ᶠ y in 𝓝 x, Nat.card (f ⁻¹' {x}) = Nat.card (f ⁻¹' {y}) := by
  obtain ⟨_, U, hxU, hU, -, H, hH⟩ := h
  filter_upwards [hU.mem_nhds hxU] with y hy
  let incl : (f ⁻¹' {y}) → (f ⁻¹' U) := fun p =>
    ⟨p.1, by rw [Set.mem_preimage, Set.mem_singleton_iff.mp p.2]; exact hy⟩
  have hinc : ∀ (p : f ⁻¹' {y}), f (incl p).1 = y := fun p => by
    show f p.1 = y
    exact Set.mem_singleton_iff.mp p.2
  have Hincl : ∀ p : f ⁻¹' {y}, H (incl p) = (⟨y, hy⟩, (H (incl p)).2) := fun p =>
    Prod.ext (Subtype.ext ((hH (incl p)).trans (hinc p))) rfl
  let φ : (f ⁻¹' {y}) → (f ⁻¹' {x}) := fun p => (H (incl p)).2
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q hpq
      change (H (incl p)).2 = (H (incl q)).2 at hpq
      have hHeq : H (incl p) = H (incl q) := by rw [Hincl p, Hincl q, hpq]
      have : incl p = incl q := H.injective hHeq
      exact Subtype.ext (congrArg (fun t : f ⁻¹' U => (t : E)) this)
    · intro q
      set u := H.symm (⟨y, hy⟩, q) with hu
      have hfu : f u.1 = y := by
        have hh := hH u
        rw [hu] at hh
        simp only [Homeomorph.apply_symm_apply] at hh
        exact hh.symm
      refine ⟨⟨u.1, hfu⟩, ?_⟩
      change (H (incl ⟨u.1, hfu⟩)).2 = q
      have : incl ⟨u.1, hfu⟩ = u := Subtype.ext rfl
      rw [this, hu, Homeomorph.apply_symm_apply]
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

/-- Fibres of a covering map over a preconnected set have constant cardinality. -/
theorem natCard_fiber_eq_of_preconnected {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {f : E → B} {s : Set B} (h : IsCoveringMapOn f s) (hs : IsPreconnected s)
    {a b : B} (ha : a ∈ s) (hb : b ∈ s) :
    Nat.card (f ⁻¹' {a}) = Nat.card (f ⁻¹' {b}) := by
  refine hs.induction₂ (fun x y => Nat.card (f ⁻¹' {x}) = Nat.card (f ⁻¹' {y})) ?_ ?_ ?_ ha hb
  · intro x hx
    exact (eventually_natCard_fiber_eq_of_isEvenlyCovered (h x hx)).filter_mono nhdsWithin_le_nhds
  · intro x y z _ _ _ hxy hyz
    exact hxy.trans hyz
  · intro x y _ _ hxy
    exact hxy.symm

end Commons.Topology.Covering