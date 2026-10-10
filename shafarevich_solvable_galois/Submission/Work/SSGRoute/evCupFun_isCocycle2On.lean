import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E7Fin.cupPairing
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `evCupFun` of two `1`-cocycles is a `2`-cocycle

`Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b` is the naive cup product

  `(g, h) ↦ evLin (a g ⊗ (res g • b h)) : DualMod p T`

of two `1`-cochains `a : G_k → M` and `b : G_k → DualMod p (M ⊗ T)`, evaluated into
`DualMod p T ≅ μ_p`.  The point of this file is that on the locus where both `a` and `b` are
`1`-cocycles, the result is a `2`-cocycle (`Work.SSGRoute.IsCocycle2On`).  This is the standard
computation for the cup product: the crossed-homomorphism identities for `a` and `b` turn the
`2`-cocycle condition into the telescoping identity of tensor products

  `(φ g • a h) ⊗ Z - (a g + φ g • a h) ⊗ Z + a g ⊗ (U + Z) - a g ⊗ U = 0`

(with `U = φ g • b h`, `Z = φ g • (φ h • b l)`), which is associativity of addition.

The single non-formal ingredient is the `G`-equivariance of `evLin` for the *diagonal* action on
`M ⊗ DualMod p (M ⊗ T)` (`evLin_smul_diag` below); it is checked pointwise on `T` using the
contragredient rule `(g • ψ) y = ψ (g⁻¹ • y)` of `DualMod.dualSMul` and the diagonal action
`Work.Shrinking.diagTensor_smul_tmul` on `M ⊗ T`.
-/

open scoped TensorProduct Pointwise

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
  [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

omit [NumberField k] [IsAlgClosure k Ω] [FiniteDimensional k K] [IsGalois k K] in
/-- `evLin` is equivariant for the diagonal action on the first tensor factor:
`g • evLin (x ⊗ₜ ψ) = evLin ((g • x) ⊗ₜ (g • ψ))`. -/
lemma evLin_smul_diag (g : K ≃ₐ[k] K) (x : M)
    (ψ : DualMod p (TensorProduct (ZMod p) M T)) :
    g • (E7Fin.evLin p M T (TensorProduct.tmul (ZMod p) x ψ))
      = E7Fin.evLin p M T (TensorProduct.tmul (ZMod p) (g • x) (g • ψ)) := by
  ext t
  simp only [DualMod.dualSMul_apply, E7Fin.evLin_tmul, LinearMap.comp_apply,
    TensorProduct.mk_apply]
  rw [Work.Shrinking.diagTensor_smul_tmul (p := p) (G := K ≃ₐ[k] K) (g⁻¹) (g • x) t]
  simp

omit [NumberField k] [IsAlgClosure k Ω] [FiniteDimensional k K] in
/-- The `2`-cocycle identity for the naive cup product, in the form in which the crossed-homomorphism
identities for `a` and `b` supply the two ingredients `ha'`, `hb'`. -/
lemma evCupFun_cocycle_step (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (TensorProduct (ZMod p) M T))
    (g h l : Ω ≃ₐ[k] Ω)
    (ha' : a (g * h) = a g + SSGRoute.res k K g • a h)
    (hb' : b (h * l) = b h + SSGRoute.res k K h • b l) :
    SSGRoute.res k K g • E7Fin.evCupFun p k Ω K T M a b h l
      - E7Fin.evCupFun p k Ω K T M a b (g * h) l
      + E7Fin.evCupFun p k Ω K T M a b g (h * l)
      - E7Fin.evCupFun p k Ω K T M a b g h = 0 := by
  simp only [E7Fin.evCupFun]
  rw [evLin_smul_diag p k Ω K T M ((SSGRoute.res k K) g) (a h) ((SSGRoute.res k K) h • b l)]
  rw [map_mul (SSGRoute.res k K) g h, mul_smul]
  rw [ha', hb']
  rw [smul_add]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
  abel

theorem evCupFun_isCocycle2On (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b) :
    Work.SSGRoute.IsCocycle2On p k Ω K (Work.SSGRoute.DualMod p T) H
      (fun g h => Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g h) := by
  intro g hg h hh l hl
  exact evCupFun_cocycle_step p k Ω K T M a b g h l (ha g hg h hh) (hb h hh l hl)

end

end Work.SSGRoute
