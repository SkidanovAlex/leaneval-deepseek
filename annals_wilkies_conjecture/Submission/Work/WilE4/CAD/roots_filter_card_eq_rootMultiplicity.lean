import Mathlib

namespace Work.WilE4.CAD

/-- If `z` is the only root of `p` lying in the open disk of radius `ρ` around `z`, then the
multiset of roots of `p` inside that disk has cardinality exactly `p.rootMultiplicity z` (i.e.
the multiplicity of `z`).

The filtered multiset consists of copies of `z` alone, so counting `z` in it recovers its
cardinality; counting `z` in the filtered multiset equals counting `z` in `p.roots` (since the
filter predicate holds at `z`); and the latter is `p.rootMultiplicity z` by
`Polynomial.count_roots`. -/
theorem roots_filter_card_eq_rootMultiplicity {p : Polynomial ℂ} (hp : p ≠ 0) {z : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hiso : ∀ w : ℂ, p.IsRoot w → dist w z < ρ → w = z) :
    (p.roots.filter (fun w => dist w z < ρ)).card = p.rootMultiplicity z := by
  have hzP : dist z z < ρ := by simp [hρ]
  -- The filtered multiset contains only `z`, so its size is its count of `z`.
  have hcnt : (p.roots.filter (fun w => dist w z < ρ)).count z
      = (p.roots.filter (fun w => dist w z < ρ)).card := by
    rw [Multiset.count_eq_card]
    intro x hx
    rw [Multiset.mem_filter] at hx
    obtain ⟨hxroot, hxd⟩ := hx
    exact (hiso x ((Polynomial.mem_roots hp).mp hxroot) hxd).symm
  rw [← hcnt, Multiset.count_filter]
  simp only [hzP, ↓reduceIte]
  exact Polynomial.count_roots p

end Work.WilE4.CAD
