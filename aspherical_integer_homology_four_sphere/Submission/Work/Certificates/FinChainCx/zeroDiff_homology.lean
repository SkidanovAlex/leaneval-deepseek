/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Homology of the complex with zero boundary maps

`zeroDiff b` is the finite chain complex with `b k` free generators in each degree `k` and all
boundary operators zero.  Its homology is therefore concentrated in the same degrees as the
underlying chain modules: `H_k (zeroDiff b) ≅ ℤ^{(b k)}`.

The proof is a direct computation.  All differentials of `zeroDiff b` vanish, so the short complex
`(zeroDiff b).toChainComplex.sc k` (`= C_{k+1} → C_k → C_{k-1}`) has both its maps equal to zero;
`ShortComplex.LeftHomologyData.ofZeros` then exhibits `C_k` itself as its left homology, and
`ShortComplex.LeftHomologyData.homologyIso` converts this into an isomorphism with the homology.
-/

import Mathlib
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.Certificates.FinChainCx

/-- Every differential of the chain complex with zero boundary operators is zero. -/
lemma zeroDiff_toChainComplex_d (b : ℕ → ℕ) (i j : ℕ) :
    (zeroDiff b).toChainComplex.d i j = 0 := by
  by_cases h : i = j + 1 <;>
    simp only [FinChainCx.toChainComplex, FinChainCx.zeroDiff, ChainComplex.of.d, h,
      dite_eq_left, SOp.toMatrix_zero, map_zero, ModuleCat.ofHom_zero] <;>
    rfl

/-- The `k`-th homology of the finite chain complex with `b k` generators in degree `k` and zero
boundary maps is `ℤ^{(b k)}`. -/
theorem zeroDiff_homology (b : ℕ → ℕ) (k : ℕ) :
    Nonempty ((zeroDiff b).homology k ≅ ModuleCat.of ℤ (Fin (b k) → ℤ)) := by
  have hf : ((zeroDiff b).toChainComplex.sc k).f = 0 := zeroDiff_toChainComplex_d b _ _
  have hg : ((zeroDiff b).toChainComplex.sc k).g = 0 := zeroDiff_toChainComplex_d b _ _
  exact ⟨ShortComplex.LeftHomologyData.homologyIso
    (ShortComplex.LeftHomologyData.ofZeros _ hf hg)⟩

end Work.Certificates.FinChainCx
