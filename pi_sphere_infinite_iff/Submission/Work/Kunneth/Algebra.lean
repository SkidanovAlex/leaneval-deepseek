import Mathlib
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Algebraic vocabulary for the Künneth theorem

* `Work.Kunneth.sumShift M` — the chain complex `⊕_q M q [q]` with zero differentials (the
  "homology complex" of a chain complex, via `M q = D.homology q`);
* `Work.Kunneth.homSum D` — `sumShift (fun q => D.homology q)`, the chain complex with
  `D`'s homology in each degree and zero differentials.

The Künneth theorem is proved by showing that a chain complex of free `ℤ`-modules with free
homology is homotopy equivalent to its `homSum`, and then computing the tensor product with
`homSum`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- Morphisms of chain complexes of `ℤ`-modules, spelled so that statements quoted outside the
chapter do not need the `⟶` notation in scope. -/
abbrev chHom (C D : ChainComplex (ModuleCat ℤ) ℕ) : Type := C ⟶ D

/-- The chain complex with `M q` in degree `q` and zero differentials. -/
def sumShift (M : ℕ → ModuleCat ℤ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of M (fun _ => 0) (by simp)

/-- The **homology complex** of a chain complex: `D`'s homology in each degree, with zero
differentials. -/
def homSum (D : ChainComplex (ModuleCat ℤ) ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  sumShift (fun q => D.homology q)

@[simp]
theorem sumShift_X (M : ℕ → ModuleCat ℤ) (q : ℕ) : (sumShift M).X q = M q := rfl

@[simp]
theorem sumShift_d (M : ℕ → ModuleCat ℤ) (q : ℕ) : (sumShift M).d (q + 1) q = 0 := by
  simp only [sumShift, ChainComplex.of_d]
  try rfl

end

end Work.Kunneth
