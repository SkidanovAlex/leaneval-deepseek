import Mathlib
import Submission.Work.Descent.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.Descent

/-- There is an element of `k'` whose Galois trace `x ↦ ∑ σ, σ x` is `1`. -/
theorem exists_trace_one {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] :
    ∃ c : k', ∑ σ : Work.Descent.Gal k k', σ c = 1 := by
  -- The trace form of a finite separable extension is nondegenerate, so the trace is onto `k`;
  -- the sum of Galois conjugates is `algebraMap k k' (Algebra.trace k k' _)`.
  obtain ⟨c, hc⟩ := Algebra.trace_surjective k k' 1
  refine ⟨c, ?_⟩
  have h := trace_eq_sum_automorphisms (K := k) (L := k') c
  rw [hc] at h
  simpa using h.symm

end Work.Descent
