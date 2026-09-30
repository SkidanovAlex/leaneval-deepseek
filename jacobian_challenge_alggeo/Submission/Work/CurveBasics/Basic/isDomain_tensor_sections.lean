/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tensoring the affine sections of a curve with a field extension

Combining `isDomain_tensor_of_isOpenImmersion` with the description of the structure
morphism of an affine open (see `Sections.lean`) yields: for a curve `C` over `k`, a
non-empty affine open `U ⊆ C` and a field extension `L/k`, the ring `Γ(C, U) ⊗[k] L` is a
domain.
-/
import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Basic.Sections
import Submission.Work.CurveBasics.Basic.isDomain_tensor_of_isOpenImmersion

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- For a non-empty affine open `U` of a curve and a field extension `L/k`, the ring
`Γ(C, U) ⊗[k] L` is a domain. -/
theorem isDomain_tensor_sections (C : Curve k) {U : C.left.Opens} (hU : IsAffineOpen U)
    [Nonempty U] (L : Type u) [Field L] [Algebra k L] :
    IsDomain (Γ(C.left, U) ⊗[k] L) := by
  haveI : Nontrivial Γ(C.left, U) := by
    refine ⟨0, 1, fun h => ?_⟩
    have h1 : (C.left.germToFunctionField U) (0 : Γ(C.left, U)) =
        (C.left.germToFunctionField U) 1 := by rw [h]
    simp at h1
  exact isDomain_tensor_of_isOpenImmersion C.hom hU.fromSpec
    (specMap_algebraMap_sections C hU).symm L

end

end Curve

end Work.CurveBasics
