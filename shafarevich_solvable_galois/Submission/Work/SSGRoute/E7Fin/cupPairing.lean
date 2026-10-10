import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.Interfaces

open SSGRoute
open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

noncomputable section

/-- The evaluation map `M ⊗ Hom_{𝔽_p}(M ⊗ T, 𝔽_p) → Hom_{𝔽_p}(T, 𝔽_p)`, given on pure tensors by
`x ⊗ φ ↦ (t ↦ φ (x ⊗ t))`.  It is the coefficient-level map through which the cup product becomes a
`DualMod p T`-valued (hence, up to the cyclotomic identification, `μ_p`-valued) `2`-cochain. -/
def evLin (p : ℕ) (M T : Type) [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] :
    TensorProduct (ZMod p) M (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p T :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun φ => φ.comp (TensorProduct.mk (ZMod p) M T x)
          map_add' := fun φ ψ => by ext t; simp
          map_smul' := fun c φ => by ext t; simp }
      map_add' := fun x y => by ext φ t; simp
      map_smul' := fun c x => by ext φ t; simp }

@[simp] theorem evLin_tmul (p : ℕ) (M T : Type) [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T]
    (x : M) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    evLin p M T (x ⊗ₜ[ZMod p] φ) = φ.comp (TensorProduct.mk (ZMod p) M T x) := by
  simp [evLin]

/-- The naive cup product of two `1`-cochains, evaluated into the module `DualMod p T ≅ μ_p`:
`(g,h) ↦ evLin (a g ⊗ (g • b h))`.  This is the cochain whose `inv`-value (for a fixed invariant
functional `inv`) is the local Tate pairing. -/
def evCupFun (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T :=
  fun g h => evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • b h))

@[simp] theorem evCupFun_apply (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (g h : Ω ≃ₐ[k] Ω) :
    evCupFun p k Ω K T M a b g h =
      (SSGRoute.res k K g • b h).comp (TensorProduct.mk (ZMod p) M T (a g)) := by
  simp [evCupFun]

/-- **The local pairing attached to a fixed invariant functional `inv`**: on locally constant
`1`-cocycles on `H` it is `(a,b) ↦ inv (evCupFun a b)`, and it is `0` off the cocycles (the clause
list of `E7` is only asserted on cocycles, so the values off them are irrelevant). -/
def pairOfInv (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) : ZMod p := by
  classical
  exact if SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧
      SSGRoute.IsCocycleOn (SSGRoute.res k K) H b
    then inv (evCupFun p k Ω K T M a b) else 0

@[simp] theorem pairOfInv_of_cocycle (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hab : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧
      SSGRoute.IsCocycleOn (SSGRoute.res k K) H b) :
    pairOfInv p k Ω K T inv M H a b = inv (evCupFun p k Ω K T M a b) :=
  if_pos hab

end

end Work.SSGRoute.E7Fin
