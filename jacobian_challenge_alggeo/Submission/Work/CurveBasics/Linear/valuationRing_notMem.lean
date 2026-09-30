import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Linear

/-- If `h : K` is transcendental over a subfield `k ⊆ K`, then there is a valuation subring `V`
of `K` containing `k` with `h ∉ V`.

Proof sketch: let `R` be the integral closure of `k` in `K` (as a subring, e.g.
`(integralClosure k K).toSubring`). Since `h` is transcendental it is not integral over `k`, so
`h ∉ R`, and `R` is integrally closed in `K` (instance
`IsIntegrallyClosedIn (integralClosure k K).toSubring K`). Apply
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`. -/
theorem valuationRing_notMem {k K : Type*} [Field k] [Field K] [Algebra k K] {h : K}
    (hh : ¬ IsAlgebraic k h) :
    ∃ V : ValuationSubring K, (∀ c : k, algebraMap k K c ∈ V.toSubring) ∧ h ∉ V.toSubring := by
  have hhR : h ∉ (integralClosure k K).toSubring := by
    rw [Subalgebra.mem_toSubring]
    intro hmem
    exact hh (IsIntegral.isAlgebraic hmem)
  obtain ⟨V, hRV, hV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hhR
  refine ⟨V, ?_, hV⟩
  intro c
  apply hRV
  rw [Subalgebra.mem_toSubring]
  exact isIntegral_algebraMap

end Work.CurveBasics.Linear
