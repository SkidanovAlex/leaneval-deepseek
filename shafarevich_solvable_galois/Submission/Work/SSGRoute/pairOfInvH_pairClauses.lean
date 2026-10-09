import Mathlib
import Submission.Work.SSGRoute.cupInvariantPerPlace
import Submission.Work.SSGRoute.E7Fin.pairOfInv_pairClauses
import Submission.Work.SSGRoute.E7Fin.pairOfInv_clauses
import Submission.Work.SSGRoute.E7Fin.pairOfInv_natural
import Submission.Work.SSGRoute.E7Fin.pairOfInv_coboundary
import Submission.Work.SSGRoute.H1Pair.Clauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Additive congruence: `a + b = c + d` from `a = c` and `b = d`.  Used to combine the two
induction hypotheses in the tensor-product induction below without ever having to name the
ambient tensor-product action. -/
private theorem add_congr_aux {X : Type} [Add X] {a b c d : X} (h1 : a = c) (h2 : b = d) :
    a + b = c + d := by
  rw [h1, h2]

/-- **The ambient action of `K ≃ₐ[k] K` on `M ⊗ T` is the diagonal action.**  If a
`DistribMulAction` instance on `M ⊗[ZMod p] T` multiplies pure tensors diagonally (hypothesis
`hdiagM`), then it *is* the global diagonal instance
`Work.Shrinking.instDistribMulActionTensorProduct`.  Two `DistribMulAction`s on the same additive
group with the same `smul` are equal, and the `smul` is determined by its values on pure tensors.

This is the bridge that reconciles the two ways type-class synthesis resolves the action on
`M ⊗ T` in the statement of `pairOfInvH_pairClauses`: the local instance in the hypotheses
(`hdiagM`, `hstabM`, `h4`) and the global instance used in the conclusion. -/
theorem tensorAction_eq_of_diag
    (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [ia : DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) =
        TensorProduct.tmul (ZMod p) (g • x) (g • t)) :
    ia = Work.Shrinking.instDistribMulActionTensorProduct
      (p := p) (G := K ≃ₐ[k] K) (M := M) (N := T) := by
  ext g x
  induction x using TensorProduct.induction_on with
  | zero =>
      exact (DistribMulAction.smul_zero (self := ia) g).trans
        (DistribMulAction.smul_zero
          (self := Work.Shrinking.instDistribMulActionTensorProduct
            (p := p) (G := K ≃ₐ[k] K) (M := M) (N := T)) g).symm
  | tmul m t =>
      exact (hdiagM g m t).trans
        (Work.Shrinking.diagTensor_smul_tmul (p := p) (G := K ≃ₐ[k] K) g m t).symm
  | add y z hy hz =>
      exact (DistribMulAction.smul_add (self := ia) g y z).trans
        ((add_congr_aux hy hz).trans
          (DistribMulAction.smul_add
            (self := Work.Shrinking.instDistribMulActionTensorProduct
              (p := p) (G := K ≃ₐ[k] K) (M := M) (N := T)) g y z).symm)

theorem pairOfInvH_pairClauses
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hinv_add : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      inv H (c + c') = inv H c + inv H c')
    (hinv_cob : ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv H c = 0)
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv (SSGRoute.decomp k A) c = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) =
        TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (hstabM : ∀ n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsLocConstOn H (fun g => SSGRoute.res k K g • n))
    (h4 : (∀ a : (Ω ≃ₐ[k] Ω) → M,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
          Work.SSGRoute.pairOfInvH p k Ω K T inv M H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
          Work.SSGRoute.pairOfInvH p k Ω K T inv M H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b)) :
    H1Pair.PairClauses p K T M (fun a b => Work.SSGRoute.pairOfInvH p k Ω K T inv M H a b) H ∧
      (∀ (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
          [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
          [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M₂ T)]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M₂ T)]
          (hdiagM₂ : ∀ (g : K ≃ₐ[k] K) (x : M₂) (t : T),
            g • (TensorProduct.tmul (ZMod p) x t) =
              TensorProduct.tmul (ZMod p) (g • x) (g • t))
          (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
          (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
            Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M)
            (t : T),
            f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
          (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        Work.SSGRoute.pairOfInvH p k Ω K T inv M₂ H (fun σ => f (a σ)) b =
          Work.SSGRoute.pairOfInvH p k Ω K T inv M H a (fun σ => f' (b σ))) ∧
      (∀ (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsFinPlace k A → ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
        (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
        Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) := by
  have hinstD := tensorAction_eq_of_diag p k Ω K T M hdiagM
  subst hinstD
  refine ⟨⟨?_, ?_, ?_, h4.1, h4.2⟩, ?_, ?_⟩
  · intro a a' b ha ha' hb
    exact Work.SSGRoute.E7Fin.pairOfInv_add_left p k Ω K T M H (inv H) (hinv_add H) a a' b ha ha' hb
  · intro a b b' ha hb hb'
    exact Work.SSGRoute.E7Fin.pairOfInv_add_right p k Ω K T M H (inv H) (hinv_add H) a b b' ha hb hb'
  · intro a b ha hb h
    rcases h with h | h
    · show Work.SSGRoute.E7Fin.pairOfInv p k Ω K T (inv H) M H a b = 0
      rw [Work.SSGRoute.E7Fin.pairOfInv_of_cocycle p k Ω K T (inv H) M H a b ⟨ha.1, hb.1⟩]
      exact hinv_cob _ (Work.SSGRoute.E7Fin.evCupFun_coboundary_left p k Ω K T M hdiagM H a b h hb.1 hb.2)
    · show Work.SSGRoute.E7Fin.pairOfInv p k Ω K T (inv H) M H a b = 0
      rw [Work.SSGRoute.E7Fin.pairOfInv_of_cocycle p k Ω K T (inv H) M H a b ⟨ha.1, hb.1⟩]
      exact hinv_cob _ (Work.SSGRoute.E7Fin.evCupFun_coboundary_right p k Ω K T M hdiagM H a b ha.1 ha.2 h hstabM)
  · intro M₂ h1 h2 h3 h4 h5 h6 hdiagM₂ f hf f' hff' a b ha hb
    exact Work.SSGRoute.E7Fin.pairOfInv_natural p k Ω K T (inv H) M M₂ hdiagM hdiagM₂ f hf f' hff' H a b ha hb
  · intro A a b hA hp hram ha hb hunram
    show Work.SSGRoute.E7Fin.pairOfInv p k Ω K T (inv (SSGRoute.decomp k A)) M (SSGRoute.decomp k A) a b = 0
    rw [Work.SSGRoute.E7Fin.pairOfInv_of_cocycle p k Ω K T (inv (SSGRoute.decomp k A)) M (SSGRoute.decomp k A) a b ⟨ha.1, hb.1⟩]
    exact hinv_unram A hA hp hram _ (fun g h hgh =>
      Work.SSGRoute.E7Fin.evCupFun_eq_zero_of_inertia p k Ω K T M A a b
        (fun σ hσ => (hunram σ hσ).1) (fun σ hσ => (hunram σ hσ).2) g h hgh)

end Work.SSGRoute
