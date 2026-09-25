import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Commons.RingTheory.Valuation

/-- Given a nonzero polynomial `f` over `K` and a valuation subring `W` of a field extension
`L`, the roots of `f` in `L` are pairwise separated by a positive element of the value group
of `W`: there is `δ > 0` with `δ ≤ W.valuation (x - y)` for every two distinct roots `x ≠ y`
of `f` in `L`.

The proof is a minimum over the (finite) set of differences of distinct roots, using that a
valuation of a nonzero element is positive. -/
theorem exists_root_separation_val {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) {f : Polynomial K} (hf : f ≠ 0) :
    ∃ δ : W.ValueGroup, 0 < δ ∧ ∀ x ∈ f.rootSet L, ∀ y ∈ f.rootSet L, x ≠ y →
      δ ≤ W.valuation (x - y) := by
  classical
  have hfne : f ≠ 0 := hf
  let g : L × L → W.ValueGroup := fun p => W.valuation (p.1 - p.2)
  let P : Set (L × L) := {p | p.1 ∈ f.rootSet L ∧ p.2 ∈ f.rootSet L ∧ p.1 ≠ p.2}
  have hPfin : P.Finite := by
    refine ((Polynomial.rootSet_finite f L).prod (Polynomial.rootSet_finite f L)).subset ?_
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  by_cases hne : P.Nonempty
  · obtain ⟨p, hp, hmin⟩ := Set.exists_min_image P g hPfin hne
    refine ⟨g p, ?_, ?_⟩
    · rw [Valuation.pos_iff]
      exact sub_ne_zero.mpr hp.2.2
    · intro x hx y hy hxy
      exact hmin (x, y) ⟨hx, hy, hxy⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx y hy hxy
    exact absurd ⟨(x, y), hx, hy, hxy⟩ hne

end Commons.RingTheory.Valuation