import Mathlib
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.FinChainCx

/-- `bdCheck` is the conjunction of its per-degree pieces `bdCheckDeg`: if the boundary
condition has been verified in every degree `k < N`, then `bdCheck` holds at `N`. -/
theorem bdCheck_of_pieces {dim : ℕ → ℕ} {bd : ∀ k, SOp (dim k) (dim (k+1))} {N : ℕ}
    (h : ∀ k, k < N → bdCheckDeg dim bd k = true) : bdCheck dim bd N = true := by
  rw [bdCheck_eq]
  exact List.all_eq_true.mpr fun k hk => h k (List.mem_range.mp hk)

end Work.Certificates.FinChainCx
