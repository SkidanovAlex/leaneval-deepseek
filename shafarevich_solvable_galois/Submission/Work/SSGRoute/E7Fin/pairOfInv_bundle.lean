/-
# The clause bundle of the cup-generated local pairing

`E7Fin/cupPairing.lean` defines, for a *single* invariant functional `inv` per local group, the
pairing `pairOfInv inv M H a b = inv (evCupFun M a b)` on locally constant `1`-cocycles (and `0`
off them).  This file bundles the clauses of the local pairing list that the construction supplies,
in one statement, so that a consumer (the `E7` node, i.e. input `G1` of the `H¹`-assembly) can
instantiate the clause list in a single step:

* **(1), (2)** additivity in each variable (`E7Fin.pairOfInv_add_left`, `…_right`);
* **(5)** naturality in the coefficient module for an equivariant `f` and its transpose
  (`E7Fin.pairOfInv_natural`) — this is the clause that a pairing produced from a dimension count
  *cannot* satisfy, and the reason the explicit cup construction is needed;
* **(6)** orthogonality on unramified classes at a good place (`E7Fin.pairOfInv_unramified`).

The clause **(3)** (vanishing on a coboundary) is added by `E7Fin.pairOfInv_coboundary` (from the
two cup computations `evCupFun_coboundary_left`/`_right`), and clause **(4)** (perfectness) is the
arithmetic input (local Tate duality in its strong form); with (3) and (4) this gives the whole
clause list of `E7`.

The hypotheses are the formal properties of the two inputs:

* `hinv_add` — `inv` is additive on `DualMod p T`-valued `2`-cochains;
* `hdiag` — the action of `Gal(K/k)` on each tensor product `X ⊗ T` is the diagonal one
  (`g • (x ⊗ t) = (g • x) ⊗ (g • t)`), for every coefficient module `X` — in the intended setting
  this is how the action is defined;
* `hinv_unram` — `inv` kills the `2`-cochains that vanish on every pair with a coordinate in the
  inertia of a good place (the local invariant of an unramified class vanishes there).
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.E7Fin.pairOfInv_clauses
import Submission.Work.SSGRoute.E7Fin.pairOfInv_natural
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

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- **The clauses (1), (2), (5), (6) of the local pairing list, for the cup-generated pairing.**
The clause (5) conjunct carries the `M₂`-instances and the naturality data of
`E7Fin.pairOfInv_natural`; the diagonal-action rule for `M₂ ⊗ T` and for `M ⊗ T` come from the
theorem-level hypothesis `hdiag`. -/
theorem pairOfInv_clauses
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      inv (c + c') = inv c + inv c')
    (hdiag : ∀ (X : Type) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) X T)]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) X T)],
      ∀ (g : K ≃ₐ[k] K) (x : X) (t : T),
        g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv c = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    -- (1) additive in the first variable
    ((∀ (a a' : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      pairOfInv p k Ω K T inv M H (a + a') b =
        pairOfInv p k Ω K T inv M H a b + pairOfInv p k Ω K T inv M H a' b) ∧
    -- (2) additive in the second variable
    (∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
      pairOfInv p k Ω K T inv M H a (b + b') =
        pairOfInv p k Ω K T inv M H a b + pairOfInv p k Ω K T inv M H a b')) ∧
    -- (5) naturality in the coefficient module
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
    -- (6) orthogonality on unramified classes at good places
    (∀ (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsFinPlace k A → ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
      (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
      pairOfInv p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a a' b ha ha' hb
    exact pairOfInv_add_left p k Ω K T M H inv hinv_add a a' b ha ha' hb
  · intro a b b' ha hb hb'
    exact pairOfInv_add_right p k Ω K T M H inv hinv_add a b b' ha hb hb'
  · intro M₂ _ _ _ _ f hf f' hff' a b ha hb
    exact pairOfInv_natural p k Ω K T inv M M₂ (hdiag M) (hdiag M₂) f hf f' hff' H a b ha hb
  · intro A a b hA hp hram ha hb hunram
    exact pairOfInv_unramified (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (inv := inv) (hinv_unram := hinv_unram) (A := A) (hA := hA) (hp := hp) (hram := hram)
      (a := a) (b := b) (ha := ha) (hb := hb) (hunram := hunram)

end

end Work.SSGRoute.E7Fin
