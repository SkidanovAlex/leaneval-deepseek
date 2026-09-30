import Mathlib
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory Limits

namespace Work.Certificates.FinChainCx

/-- If a `FinChainCx` has no cells in degree `k` (`dim k = 0`), then its `k`-th homology
vanishes: the chain group `C_k = ℤ^{(dim k)}` is the zero module, and homology in degree `k`
is a quotient of a submodule of `C_k`. -/
theorem subsingleton_homology_of_dim_zero (C : FinChainCx) (k : ℕ) (h : C.dim k = 0) :
    Subsingleton (C.homology k) := by
  have hsub : Subsingleton (Fin (C.dim k) → ℤ) := by
    rw [h]
    exact ⟨fun f g => funext fun i => Fin.elim0 i⟩
  have hX : IsZero ((C.toChainComplex).X k) :=
    ModuleCat.isZero_of_iff_subsingleton.mpr hsub
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact ShortComplex.isZero_homology_of_isZero_X₂ ((C.toChainComplex).sc k) hX

end Work.Certificates.FinChainCx
