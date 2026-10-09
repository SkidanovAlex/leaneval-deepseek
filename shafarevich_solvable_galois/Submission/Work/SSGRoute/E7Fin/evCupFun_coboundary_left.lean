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

section EvLinDiagonal

variable (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

omit [Normal k K] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] in
/-- The diagonal action on pure tensors computes the action of `K ≃ₐ[k] K` on the value of `evLin`:
`g • evLin (x ⊗ₜ ψ) = evLin ((g • x) ⊗ₜ (g • ψ))`.  This is *not* an instance-level statement: it
is checked pointwise on `T`, using the contragredient rule `(g • ψ) y = ψ (g⁻¹ • y)` and then the
diagonal-action hypothesis `hdiagM` at `(g⁻¹, g • x, t)`. -/
lemma smul_evLin_tmul
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (g : K ≃ₐ[k] K) (x : M) (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    g • evLin p M T (TensorProduct.tmul (ZMod p) x ψ) =
      evLin p M T (TensorProduct.tmul (ZMod p) (g • x) (g • ψ)) := by
  ext t
  simp only [Work.SSGRoute.DualMod.dualSMul_apply, evLin_tmul, LinearMap.comp_apply,
    TensorProduct.mk_apply]
  rw [hdiagM (g⁻¹) (g • x) t]
  simp

end EvLinDiagonal

/-- **The cup product of a `1`-coboundary with a `1`-cocycle is a `2`-coboundary** (the content of
clause (3) of the local pairing list for the cup-generated family): if `a g = res g • m - m` on `H`
and `b` is a locally constant `1`-cocycle on `H`, then
`evCupFun a b : (g,h) ↦ evLin (a g ⊗ (res g • b h))` is a `2`-coboundary, with cobounding cochain
`g ↦ evLin (m ⊗ b g)` (locally constant because `b` is, and because `evLin` is linear in the
coefficient).

The key step is `res g • evLin (m ⊗ ψ) = evLin ((res g • m) ⊗ (res g • ψ))` for pure tensors, which
is the diagonal-action hypothesis `hdiagM` together with the contragredient rule
`(g • ψ) y = ψ (g⁻¹ • y)` of `DualMod.dualSMul_apply`; the rest is the cocycle identity for `b` and
bilinearity of `evLin`.  No action on `M ⊗ DualMod p (M ⊗ T)` is needed. -/
theorem evCupFun_coboundary_left
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b)
    (hb_lc : SSGRoute.IsLocConstOn H b) :
    SSGRoute.IsCoboundary2On (SSGRoute.res k K) H
      (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨U, hUopen, hUb⟩ := hb_lc
  refine ⟨fun g => evLin p M T (TensorProduct.tmul (ZMod p) m (b g)), ⟨U, hUopen, ?_⟩, ?_⟩
  · intro g hg u hu huH
    show evLin p M T (TensorProduct.tmul (ZMod p) m (b (g * u))) =
      evLin p M T (TensorProduct.tmul (ZMod p) m (b g))
    rw [hUb g hg u hu huH]
  · intro g hg h hh
    have h1 : SSGRoute.res k K g • evLin p M T (TensorProduct.tmul (ZMod p) m (b h)) =
        evLin p M T (TensorProduct.tmul (ZMod p) (SSGRoute.res k K g • m)
          (SSGRoute.res k K g • b h)) :=
      smul_evLin_tmul p k Ω K T M hdiagM (SSGRoute.res k K g) m (b h)
    have h2 : SSGRoute.res k K g • b h = b (g * h) - b g := by
      rw [hb g hg h hh]
      abel
    show evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • b h)) =
      SSGRoute.res k K g • evLin p M T (TensorProduct.tmul (ZMod p) m (b h))
        - evLin p M T (TensorProduct.tmul (ZMod p) m (b (g * h)))
        + evLin p M T (TensorProduct.tmul (ZMod p) m (b g))
    rw [hm g hg, h1, h2]
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub, map_sub]
    abel

end Work.SSGRoute.E7Fin
