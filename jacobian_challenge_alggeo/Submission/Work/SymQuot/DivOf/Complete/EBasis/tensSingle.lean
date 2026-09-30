/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The single-factor embeddings under base change of the tensor power

`tensSingle F Q n m : Q →ₐ[F] Q^{⊗n}` is the `m`-th tensor-factor inclusion.  This file records
its interaction with `evalT` (product evaluation), with the base change `bcT` of the tensor power
and with the tensor power `mapT e` of an algebra equivalence.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.RhoData
import Submission.Work.SymQuot.NormPoint.MapT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.DivOf.Complete

open Work.SymQuot.NormPoint

/-- Product evaluation on a single-factor embedding. -/
theorem evalT_tensSingle {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q]
    {n : ℕ} (ψ : Fin n → Q →ₐ[F] F) (m : Fin n) (q : Q) :
    evalT ψ (tensSingle F Q n m q) = ψ m q := by
  rw [tensSingle_apply, evalT_tprod]
  rw [Finset.prod_eq_single m]
  · simp
  · intro j _ hj
    rw [if_neg hj, map_one]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- Base change of the tensor power on a single-factor embedding. -/
theorem bcT_tensSingle {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q]
    (L : Type u) [Field L] [Algebra F L] {n : ℕ} (m : Fin n) (q : Q) :
    bcT (F := F) (Q := Q) (n := n) L (tensSingle F Q n m q) =
      tensSingle L (TensorProduct F L Q) n m ((1 : L) ⊗ₜ[F] q) := by
  rw [tensSingle_apply, bcT_tprod, tensSingle_apply]
  congr 1
  funext j
  by_cases h : j = m
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, ← Algebra.TensorProduct.one_def]

/-- The tensor power of an algebra equivalence on a single-factor embedding. -/
theorem mapT_tensSingle {F : Type u} [Field F] {Q Q' : Type u} [CommRing Q] [Algebra F Q]
    [CommRing Q'] [Algebra F Q'] {n : ℕ} (e : Q ≃ₐ[F] Q') (m : Fin n) (q : Q) :
    mapT e (tensSingle F Q n m q) = tensSingle F Q' n m (e q) := by
  rw [tensSingle_apply, mapT_tprod, tensSingle_apply]
  congr 1
  funext j
  by_cases h : j = m
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_one]

end Work.SymQuot.DivOf.Complete
