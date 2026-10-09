import Mathlib
import Submission.Work.SSGRoute.E7Fin.cupPairing
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7Fin

open SSGRoute
open scoped TensorProduct

/-- **Clause (5) (naturality in the coefficient module) for the cup-generated local pairing.**
With `pairOfInv inv M H a b = inv (evCupFun M a b)` on locally constant cocycles, and the level-`T`
coefficient identification given by the transpose relation `hff'`, the pairing is natural with
respect to an equivariant `f : M →ₗ M₂` and its transpose `f'`.

The proof is the pointwise identity
`evLin (f (a g) ⊗ (g • b h)) = evLin (a g ⊗ (g • f' (b h)))`, a computation with the two
diagonal-action hypotheses `hdiagM`, `hdiagM₂` and the transpose relation `hff'`: by
`DualMod.dualSMul_apply` (`(g • φ) y = φ (g⁻¹ • y)`) and `hff'`, both sides are
`b h (f (g⁻¹ • a g) ⊗ (g⁻¹ • t))` at every `(g,h,t)`.  The two guard conditions (the two arguments
being cocycles) follow from `ha`, `hb`, the equivariance `hf` of `f` and the equivariance of `f'`,
which is itself a consequence of `hff'`, `hf` and the diagonal actions. -/
theorem pairOfInv_natural
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (M M₂ : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M₂ T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M₂ T)]
    (hdiagM₂ : ∀ (g : K ≃ₐ[k] K) (x : M₂) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) :
    Work.SSGRoute.E7Fin.pairOfInv p k Ω K T inv M₂ H (fun σ => f (a σ)) b =
      Work.SSGRoute.E7Fin.pairOfInv p k Ω K T inv M H a (fun σ => f' (b σ)) := by
  have hf'eq : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      f' (g • φ) = g • f' φ := by
    intro g φ
    apply TensorProduct.ext'
    intro e t
    show (f' (g • φ)) (TensorProduct.tmul (ZMod p) e t) =
      (g • f' φ) (TensorProduct.tmul (ZMod p) e t)
    rw [hff' (g • φ) e t, Work.SSGRoute.DualMod.dualSMul_apply]
    rw [hdiagM₂]
    rw [← hf g⁻¹ e]
    rw [← hff' φ (g⁻¹ • e) (g⁻¹ • t)]
    rw [← hdiagM g⁻¹ e t]
    rw [← Work.SSGRoute.DualMod.dualSMul_apply]
  have hfc : SSGRoute.IsCocycleOn (SSGRoute.res k K) H (fun σ => f (a σ)) := by
    intro g hg h hh
    show f (a (g * h)) = f (a g) + SSGRoute.res k K g • f (a h)
    rw [ha.1 g hg h hh, map_add, hf]
  have hf'c : SSGRoute.IsCocycleOn (SSGRoute.res k K) H (fun σ => f' (b σ)) := by
    intro g hg h hh
    show f' (b (g * h)) = f' (b g) + SSGRoute.res k K g • f' (b h)
    rw [hb.1 g hg h hh, map_add, hf'eq]
  rw [Work.SSGRoute.E7Fin.pairOfInv_of_cocycle p k Ω K T inv M₂ H (fun σ => f (a σ)) b ⟨hfc, hb.1⟩,
      Work.SSGRoute.E7Fin.pairOfInv_of_cocycle p k Ω K T inv M H a (fun σ => f' (b σ)) ⟨ha.1, hf'c⟩]
  congr 1
  funext g h
  simp only [Work.SSGRoute.E7Fin.evCupFun]
  apply LinearMap.ext
  intro t
  calc evLin p M₂ T (TensorProduct.tmul (ZMod p) (f (a g)) (SSGRoute.res k K g • b h)) t
      = (SSGRoute.res k K g • b h) (TensorProduct.tmul (ZMod p) (f (a g)) t) := by
        simp only [evLin_tmul, LinearMap.comp_apply, TensorProduct.mk_apply]
    _ = b h ((SSGRoute.res k K g)⁻¹ • (TensorProduct.tmul (ZMod p) (f (a g)) t)) := by
        rw [Work.SSGRoute.DualMod.dualSMul_apply]
    _ = b h (TensorProduct.tmul (ZMod p) ((SSGRoute.res k K g)⁻¹ • f (a g))
            ((SSGRoute.res k K g)⁻¹ • t)) := by
        rw [hdiagM₂]
    _ = b h (TensorProduct.tmul (ZMod p) (f ((SSGRoute.res k K g)⁻¹ • a g))
            ((SSGRoute.res k K g)⁻¹ • t)) := by
        rw [← hf (SSGRoute.res k K g)⁻¹ (a g)]
    _ = (f' (b h)) (TensorProduct.tmul (ZMod p) ((SSGRoute.res k K g)⁻¹ • a g)
            ((SSGRoute.res k K g)⁻¹ • t)) := by
        rw [← hff' (b h) ((SSGRoute.res k K g)⁻¹ • a g) ((SSGRoute.res k K g)⁻¹ • t)]
    _ = (f' (b h)) ((SSGRoute.res k K g)⁻¹ • (TensorProduct.tmul (ZMod p) (a g) t)) := by
        rw [← hdiagM (SSGRoute.res k K g)⁻¹ (a g) t]
    _ = (SSGRoute.res k K g • f' (b h)) (TensorProduct.tmul (ZMod p) (a g) t) := by
        rw [← Work.SSGRoute.DualMod.dualSMul_apply]
    _ = evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • f' (b h))) t := by
        simp only [evLin_tmul, LinearMap.comp_apply, TensorProduct.mk_apply]

end Work.SSGRoute.E7Fin
