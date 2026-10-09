/-
# The whole clause list of the cup-generated local pairing, modulo perfectness

This is the final interface of the cup construction: at a fixed local group `H`, the pairing
`pairOfInv inv M H` attached to a *single* invariant functional `inv` satisfies

* clauses (1), (2), (3), (5), (6) — **proved** (`E7Fin.pairOfInv_clauses`,
  `E7Fin.pairOfInv_coboundary`);
* clause (4) — perfectness, local Tate duality in its strong form — is the **arithmetic input**,
  taken as the hypothesis `h4`.

So `Work.SSGRoute.PTembedding.localTatePairing_canonical` (node `E7`, the clause list of `G1`)
follows from the cup construction together with `h4` at every local group, and with the arithmetic
facts recorded in the hypotheses (`hinv_add`, `hinv_cob`, `hinv_unram` for the invariant, the
diagonal action `hdiag`, and the local constancy `hstab` of the orbit maps on the dual modules).
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.H1Pair.Clauses
import Submission.Work.SSGRoute.E7Fin.pairOfInv_bundle
import Submission.Work.SSGRoute.E7Fin.pairOfInv_coboundary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

noncomputable section

set_option linter.unusedSectionVars false

/-- **The clause list of `E7` for the cup-generated pairing, modulo perfectness.** -/
theorem pairOfInv_pairClauses
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hinv_add : ∀ c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      inv (c + c') = inv c + inv c')
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv c = 0)
    (hdiag : ∀ (X : Type) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) X T)]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) X T)],
      ∀ (g : K ≃ₐ[k] K) (x : X) (t : T),
        g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (hstab : ∀ (X : Type) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) X T)]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) X T)],
      ∀ n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) X T),
        SSGRoute.IsLocConstOn H (fun g => SSGRoute.res k K g • n))
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv c = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (h4 : (∀ a : (Ω ≃ₐ[k] Ω) → M,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
          pairOfInv p k Ω K T inv M H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
          pairOfInv p k Ω K T inv M H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b)) :
    H1Pair.PairClauses p K T M (fun a b => pairOfInv p k Ω K T inv M H a b) H ∧
      (∀ (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
          [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
          (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
          (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
            Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
            f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
          (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pairOfInv p k Ω K T inv M₂ H (fun σ => f (a σ)) b =
          pairOfInv p k Ω K T inv M H a (fun σ => f' (b σ))) ∧
      (∀ (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsFinPlace k A → ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
        (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
        pairOfInv p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) := by
  obtain ⟨h12, h5, h6⟩ :=
    pairOfInv_clauses p k Ω K T inv hinv_add hdiag hinv_unram M H
  obtain ⟨h1, h2⟩ := h12
  refine ⟨⟨h1, h2, ?_, h4.1, h4.2⟩, h5, h6⟩
  intro a b ha hb hab
  exact pairOfInv_coboundary p k Ω K T M H inv hinv_cob (hdiag M) (hstab M) a b ha hb hab

end

end Work.SSGRoute.E7Fin
