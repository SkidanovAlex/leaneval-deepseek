import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

set_option autoImplicit false

/-- If the open vertical segment between two points of the plane carries no point of `K`, then every
point of it lies in the same component of `Kᶜ` as the midpoint. -/
theorem mem_connectedComponentIn_midpoint
    (K : Set (ℝ × ℝ)) (k l w x : ℝ × ℝ)
    (hk1 : k.1 = 0) (hl1 : l.1 = 0) (hkl : k.2 < l.2)
    (hx1 : x.1 = 0) (hx2 : x.2 = (k.2 + l.2) / 2)
    (hw1 : w.1 = 0) (hwk : k.2 < w.2) (hwl : w.2 < l.2) (hwK : w ∉ K)
    (hfree : ∀ p ∈ K, p.1 = 0 → k.2 < p.2 → p.2 < l.2 → False) :
    w ∈ connectedComponentIn (Kᶜ) x := by
  -- The open vertical segment between `k` and `l` is the image of the open interval
  -- `(k.2, l.2)` under the continuous map `t ↦ (0, t)`, hence preconnected.
  let s : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ k.2 < p.2 ∧ p.2 < l.2}
  have hs : IsPreconnected s := by
    have heq : s = (fun t : ℝ => ((0 : ℝ), t)) '' (Set.Ioo k.2 l.2) := by
      ext p
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨p.2, ⟨h2, h3⟩, Prod.ext h1.symm rfl⟩
      · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
        exact ⟨rfl, ht1, ht2⟩
    rw [heq]
    exact ((isConnected_Ioo hkl).image _ (by fun_prop)).isPreconnected
  -- The midpoint of `k` and `l` lies on the segment.
  have hx_mem : x ∈ s := by
    refine ⟨hx1, ?_, ?_⟩ <;> rw [hx2] <;> linarith
  -- The segment is disjoint from `K`.
  have hsub : s ⊆ Kᶜ := by
    intro p hp hpK
    exact hfree p hpK hp.1 hp.2.1 hp.2.2
  have hw_mem : w ∈ s := ⟨hw1, hwk, hwl⟩
  exact hs.subset_connectedComponentIn hx_mem hsub hw_mem

end Work.RPB1a.Caratheodory.Brouwer
