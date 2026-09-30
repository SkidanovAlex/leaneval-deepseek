/-
Area AV (abelian-variety toolkit) for the Jacobian challenge: test objects.
-/
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Test objects for the abelian-variety toolkit

* `Work.AbVar.Gm k` is the multiplicative group scheme `𝔾_m` over `k`, i.e.
  `Spec k[T;T⁻¹]`, with its group scheme structure coming from the Hopf algebra
  structure on Laurent polynomials.
* `Work.AbVar.Ga k` is the additive group `𝔸¹` over `k` (as a scheme only; the group
  structure is not needed for the rigidity hypotheses, which only require geometric
  integrality and local finiteness).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj
open AlgebraicGeometry

namespace Work.AbVar

/-- The multiplicative group scheme `𝔾_m = Spec k[T;T⁻¹]` over `k`. -/
noncomputable abbrev Gm (k : Type u) [Field k] : Sch k :=
  (Spec (CommRingCat.of (LaurentPolynomial k))).asOver (Spec (.of k))

/-- `𝔾_m` is a group scheme. -/
noncomputable instance (k : Type u) [Field k] : GrpObj (Gm k) := inferInstance

lemma gm_locallyOfFiniteType (k : Type u) [Field k] : LocallyOfFiniteType (Gm k).hom := by
  change LocallyOfFiniteType (Spec (CommRingCat.of (LaurentPolynomial k)) ↘ Spec (.of k))
  infer_instance

/-- The affine line `𝔸¹ = Spec k[X]` over `k`. -/
noncomputable abbrev Ga (k : Type u) [Field k] : Sch k :=
  Over.mk (Spec (CommRingCat.of (Polynomial k)) ↘ Spec (.of k))

end Work.AbVar
