import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.vfShared
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option backward.isDefEq.respectTransparency false

/-- **The `⊤`-guard of the archimedean pairing is preserved by the coefficient transpose.**

`G1⁺`'s pairing at an involution group is defined with the guard
`IsCocycleOn (res k K) ⊤ b ∧ IsLocConstOn ⊤ b` (value `0` otherwise).  Clause (5) at an involution
group compares `pair M₂ ⟨c⟩ (f ∘ a) b` with `pair M ⟨c⟩ a (f' ∘ b)`, so the guard must hold for
`f' ∘ b` whenever it holds for `b`.

Route.  Locally constant: the same constancy subgroup `U` witnesses it for `f' ∘ b`.  Cocycle: the
content is that the transpose `f'` of `f ⊗ id_T` intertwines the two dual actions; by `hff'` on pure
tensors both sides equal `φ ((γ⁻¹ • f e) ⊗ (γ⁻¹ • t))` where `γ = res k K g`, using `hf` at `γ⁻¹`
and the diagonal tensor action, so `f'` is `Gal(K/k)`-equivariant
(`LinearMap.ext` + `TensorProduct.induction_on`).  Then
`f' (b (g * h)) = f' (b g + res k K g • b h) = f' (b g) + res k K g • f' (b h)`. -/
theorem archPairGuard_coefficient (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T))
    (h : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ (fun σ => f' (b σ)) ∧
      SSGRoute.IsLocConstOn ⊤ (fun σ => f' (b σ)) := by
  obtain ⟨hcoc, hlc⟩ := h
  -- The transpose `f'` of `f ⊗ id_T` intertwines the two dual actions.
  have heq : ∀ (γ : K ≃ₐ[k] K)
      (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      f' (γ • φ) = γ • f' φ := by
    intro γ φ
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e t =>
      rw [hff' (γ • φ) e t, Work.SSGRoute.DualMod.dualSMul_apply,
        Work.Shrinking.diagTensor_smul_tmul,
        Work.SSGRoute.DualMod.dualSMul_apply, Work.Shrinking.diagTensor_smul_tmul,
        hff' φ (γ⁻¹ • e) (γ⁻¹ • t), hf γ⁻¹ e]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_, ?_⟩
  · intro g _ h _
    change f' (b (g * h)) = f' (b g) + SSGRoute.res k K g • f' (b h)
    rw [hcoc g trivial h trivial, map_add, heq (SSGRoute.res k K g) (b h)]
  · obtain ⟨U, hUo, hU⟩ := hlc
    exact ⟨U, hUo, fun g _ u hu _ => by
      change f' (b (g * u)) = f' (b g)
      rw [hU g trivial u hu trivial]⟩

end Work.SSGRoute.PT
