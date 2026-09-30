/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The norm point of a finite flat algebra (area SY, contract item 3)

Let `F` be a field, `Q` a commutative `F`-algebra (of finite `F`-dimension `n`) and

`T := ⨂[F]^n Q = ⨂[F] (_ : Fin n), Q`

the `n`-fold tensor power of `Q`, which Mathlib endows with the structure of a commutative
`F`-algebra (`Mathlib/RingTheory/PiTensorProduct.lean`).  The symmetric group `S_n` acts on `T`
by permuting the factors (`permAlg`), and `TS := T^{S_n}` (`symTensors`) is the subalgebra of
symmetric tensors.  This file sets up:

* `permAlg σ` — the algebra automorphism of `T` reindexing the factors;
* `symTensors F Q n : Subalgebra F T` — the symmetric tensors;
* `detT v : T →ₗ[F] F` — the determinant form followed by the tensor contraction;
* `normVal v t : F` — the value of the "norm functional" `t ↦ detT v (t * tprod v)`;
* `evalT ψ : T →ₐ[F] F` — the product evaluation `tprod u ↦ ∏_j ψ_j (u_j)`.

The main results (in the files of this directory) are that `normVal v` is multiplicative on the
symmetric tensors, so that `normVal v : symTensors →ₐ[F] F` is an algebra homomorphism
(`normPoint`), that it is independent of the basis `v` (`normVal_basis_indep`), and that it
computes the product evaluation for a flag basis (`normVal_eq_evalT`); this is the algebraic
core of the construction of a point of `Sym^n C` from an effective divisor of degree `n`.
-/
import Mathlib
import Mathlib.RingTheory.PiTensorProduct

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

/-- The `n`-fold tensor power `Q^{⊗n}`, carrying the commutative `F`-algebra structure of
`PiTensorProduct` (multiplication is componentwise on pure tensors). -/
abbrev Tens (F : Type u) [CommSemiring F] (Q : Type u) [AddCommMonoid Q] [Module F Q]
    (n : ℕ) : Type u :=
  ⨂[F] (_ : Fin n), Q

variable {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}

/-- **The permutation automorphism of the tensor power.**  `permAlg σ` reindexes the `n` tensor
factors by the permutation `σ`. -/
noncomputable def permAlg (σ : Equiv.Perm (Fin n)) : Tens F Q n ≃ₐ[F] Tens F Q n :=
  AlgEquiv.ofLinearEquiv (PiTensorProduct.reindex F (fun _ : Fin n => Q) σ)
    (by
      rw [PiTensorProduct.one_def, PiTensorProduct.reindex_tprod]
      rfl)
    (by
      intro x y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod s g =>
          simp only [PiTensorProduct.smul_tprod_mul_smul_tprod, map_smul,
            PiTensorProduct.reindex_tprod, Pi.mul_def]
        | add y z hy hz => simp only [mul_add, map_add, hy, hz]
      | add x y hx hy => simp only [add_mul, map_add, hx, hy])

/-- The action of the symmetric group on a pure tensor. -/
@[simp]
theorem permAlg_tprod (σ : Equiv.Perm (Fin n)) (f : Fin n → Q) :
    permAlg (Q := Q) σ (PiTensorProduct.tprod F f) =
      PiTensorProduct.tprod F (fun i => f (σ.symm i)) :=
  PiTensorProduct.reindex_tprod (R := F) (s := fun _ : Fin n => Q) σ f

/-- The **symmetric tensors**: the elements of `Q^{⊗n}` fixed by every permutation of the
factors. -/
noncomputable def symTensors (F : Type u) [Field F] (Q : Type u) [CommRing Q] [Algebra F Q]
    (n : ℕ) :
    Subalgebra F (Tens F Q n) where
  carrier := {t | ∀ σ : Equiv.Perm (Fin n), permAlg (Q := Q) σ t = t}
  mul_mem' := fun {x y} hx hy σ => by rw [map_mul, hx σ, hy σ]
  add_mem' := fun {x y} hx hy σ => by rw [map_add, hx σ, hy σ]
  algebraMap_mem' := fun r σ => (permAlg (Q := Q) σ).commutes r

@[simp]
theorem mem_symTensors {t : Tens F Q n} :
    t ∈ symTensors F Q n ↔ ∀ σ : Equiv.Perm (Fin n), permAlg (Q := Q) σ t = t := by
  simp [symTensors]

/-- **The determinant functional** on the tensor power: contraction with the alternating form
`det` of a basis `v` of `Q`. -/
noncomputable def detT (v : Module.Basis (Fin n) F Q) : Tens F Q n →ₗ[F] F :=
  PiTensorProduct.lift v.det.toMultilinearMap

/-- **The norm functional** attached to a basis `v` of `Q`: `t ↦ det (t * v^{⊗n})`. -/
noncomputable def normVal (v : Module.Basis (Fin n) F Q) (t : Tens F Q n) : F :=
  detT v (t * PiTensorProduct.tprod F v)

/-- The **product evaluation** functional: `tprod u ↦ ∏_j ψ_j (u_j)`. -/
noncomputable def evalT (ψ : Fin n → (Q →ₐ[F] F)) : Tens F Q n →ₐ[F] F :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra F (Fin n) F).compLinearMap (fun j => (ψ j).toLinearMap))
    (by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        Pi.one_apply, AlgHom.toLinearMap_apply, map_one, Finset.prod_const_one])
    (by
      intro x y
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        Pi.mul_apply, AlgHom.toLinearMap_apply, map_mul, Finset.prod_mul_distrib])

@[simp]
theorem evalT_tprod (ψ : Fin n → (Q →ₐ[F] F)) (f : Fin n → Q) :
    evalT ψ (PiTensorProduct.tprod F f) = ∏ j, ψ j (f j) := by
  simp only [evalT, PiTensorProduct.liftAlgHom, AlgHom.ofLinearMap_apply,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply]

end Work.SymQuot.NormPoint
