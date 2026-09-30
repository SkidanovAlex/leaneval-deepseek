/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The norm point functional on the symmetric tensors (area SY, contract item 3)

`Work.SymQuot.NormPoint.normPoint v : symTensors F Q n →ₐ[F] F` is the algebra homomorphism
`t ↦ detT v (t * v^{⊗n})` on the symmetric tensors of the `n`-fold tensor power of a
commutative `F`-algebra `Q` of `F`-dimension `n`.  Its multiplicativity is `detT_mul`
(NP1 of `Submission/Work/NOTES_LEAD_jacobian_divof.md` §4), and it is the algebraic heart of
the construction of a point of `Sym^n C` from an effective divisor of degree `n`.
-/
import Submission.Work.SymQuot.NormPoint.Basic
import Submission.Work.SymQuot.NormPoint.detT_mul

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

/-- The norm functional at the unit of the tensor algebra is `1`. -/
theorem normVal_one (v : Module.Basis (Fin n) F Q) : normVal v (1 : Tens F Q n) = 1 := by
  have h : detT v (PiTensorProduct.tprod F v) = v.det (⇑v) :=
    PiTensorProduct.lift.tprod _
  rw [normVal, one_mul, h, Module.Basis.det_apply, Module.Basis.toMatrix_self, Matrix.det_one]

/-- **The norm functional is multiplicative on the symmetric tensors** (NP2). -/
theorem normVal_mul (v : Module.Basis (Fin n) F Q) {s t : Tens F Q n}
    (hs : s ∈ symTensors F Q n) (ht : t ∈ symTensors F Q n) :
    normVal v (s * t) = normVal v s * normVal v t := by
  rw [normVal, mul_assoc, detT_mul v hs]
  rfl

/-- **The norm point functional**: the algebra homomorphism `t ↦ detT v (t * v^{⊗n})` on the
symmetric tensors of `Q^{⊗n}`. -/
noncomputable def normPoint (v : Module.Basis (Fin n) F Q) : symTensors F Q n →ₐ[F] F :=
  AlgHom.ofLinearMap
    { toFun := fun t => normVal v t
      map_add' := fun a b => by
        simp only [normVal, Subalgebra.coe_add, add_mul, map_add]
      map_smul' := fun c a => by
        simp only [normVal, Subalgebra.coe_smul, smul_mul_assoc, map_smul, RingHom.id_apply] }
    (normVal_one v)
    (fun s t => normVal_mul v s.2 t.2)

@[simp]
theorem normPoint_apply (v : Module.Basis (Fin n) F Q) (t : symTensors F Q n) :
    normPoint v t = normVal v t := rfl

end Work.SymQuot.NormPoint
