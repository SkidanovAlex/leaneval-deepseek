/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of the tensor power (area SY, contract item 3)

For a field extension `F → L` and a commutative `F`-algebra `Q`, the base change of the `n`-fold
tensor power `Tens F Q n` to `L` is the `n`-fold tensor power `Tens L (L ⊗[F] Q) n`, and
`bcT L : Tens F Q n →ₐ[F] Tens L (L ⊗[F] Q) n` is the algebra homomorphism
`tprod u ↦ tprod (1 ⊗ u_j)`.  It is the map along which the norm point functional
(`normPoint`, NP2 of `Submission/Work/NOTES_LEAD_jacobian_divof.md` §4) is compared with its
value after base change (NP5).
-/
import Submission.Work.SymQuot.NormPoint.Basic
import Submission.Work.SymQuot.NormPoint.bcT_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.NormPoint

variable {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}

/-- **Base change of the tensor power**: the unique `F`-algebra homomorphism
`⨂[F]^n Q ⟶ ⨂[L]^n (L ⊗[F] Q)` sending `u₀ ⊗ … ⊗ u_{n-1}` to `(1⊗u₀) ⊗ … ⊗ (1⊗u_{n-1})`. -/
noncomputable def bcT (L : Type u) [Field L] [Algebra F L] :
    Tens F Q n →ₐ[F] Tens L (TensorProduct F L Q) n :=
  Classical.choose (bcT_exists (F := F) (Q := Q) (n := n) L)

/-- The defining formula of `bcT` on pure tensors. -/
theorem bcT_tprod (L : Type u) [Field L] [Algebra F L] (u : Fin n → Q) :
    bcT (F := F) (Q := Q) (n := n) L (PiTensorProduct.tprod F u) =
      PiTensorProduct.tprod L (fun j => TensorProduct.tmul F (1 : L) (u j)) :=
  Classical.choose_spec (bcT_exists (F := F) (Q := Q) (n := n) L) u

end Work.SymQuot.NormPoint
