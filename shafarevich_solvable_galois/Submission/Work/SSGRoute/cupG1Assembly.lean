import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.H1Pair.Clauses
import Submission.Work.SSGRoute.E7Arch.g1Assembly
import Submission.Work.SSGRoute.E7Arch.exists_level_localDegree_ge_three
import Submission.Work.SSGRoute.cupInvariantPerPlace
import Submission.Work.SSGRoute.pairOfInvH_pairClauses
import Submission.Work.SSGRoute.E7Fin.pairOfInv_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-place half of input `G1` from the cup datum (place-dependent invariant)

`Work.SSGRoute.canonical_localPairing_with_reciprocity` (`G1`) asks for a family of local pairings,
indexed by the coefficient module alone, with clauses (1)–(6) at every local group and the
reciprocity clause (7).  The `E7Arch` lane reduces it to a *finite-place half* `fin` satisfying

* `hclauses` — clauses (1)–(4) at the decomposition group of every finite place,
* `hnat` — clause (5) at every subgroup,
* `horth` — clause (6) at every good place,
* `hrecJoint` — the joint reciprocity,
* `hempty` — disjointness of the two shapes of local group (proved: `E7Arch.localGroupDisjoint`),

the archimedean half and the gluing being *proved* (`E7Arch.glue_of_finiteHalf`).

This file proves the first three of those, with `fin := Work.SSGRoute.pairOfInvH` (the cup
construction with one invariant functional *per local group* — the only formalisation that is
satisfiable, see `Submission/Work/SSGRoute/ACTION_cupInvariantPerPlace.md`), from

* `hdiag` — the diagonal-tensor rule for each coefficient module,
* `h4` — perfectness of the cup pairing at the decomposition groups of the finite places (local Tate
  duality in its strong form; the arithmetic input).

## Why the final step is *not* a one-line application of `glue_of_finiteHalf`

`glue_of_finiteHalf`'s `hnat`/`hclauses`/`horth` hypotheses mention `fin M H a b`, and the
`DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)` instance used to elaborate them is
resolved by *typeclass search when `E7Arch/g1Assembly.lean` is compiled* — it is not a binder of
those hypotheses.  A `fin` elaborated in another file therefore need not be definitionally
compatible with `hnat`: the composition fails to typecheck even though the mathematical content
matches (verified: feeding `pairOfInvH` to `glue_of_finiteHalf` together with the lemmas below gives
`Application type mismatch` at the `hnat` slot).  A consumer either re-derives the gluing in one file
with the tensor-action instances bound explicitly in `fin`'s type, or restates `hnat` with those
instances as binders.
-/

open SSGRoute
open scoped TensorProduct BigOperators

namespace Work.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)


/-- **Clauses (1)–(4) of the local pairing list at a finite place** for the cup pairing with a
place-dependent invariant, from the perfectness input `h4`. -/
theorem cupH_pairClauses
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      inv H (c + c') = inv H c + inv H c')
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv H c = 0)
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv (SSGRoute.decomp k A) c = 0)
    (hdiag : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
      (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) =
        TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (h4 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
          (∀ b : (Ω ≃ₐ[k] Ω) →
              Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
          (∀ a : (Ω ≃ₐ[k] Ω) → M,
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    H1Pair.PairClauses p K T M
      (fun a b => Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b)
      (SSGRoute.decomp k A) :=
  (Work.SSGRoute.pairOfInvH_pairClauses p k Ω K T inv (SSGRoute.decomp k A)
    hinv_add (fun c hc => hinv_cob (SSGRoute.decomp k A) c hc) hinv_unram
    M (hdiag M) (isLocConstOn_res_smul_dualMod (K := K) (H := SSGRoute.decomp k A)
      (X := M) (T' := T) _)
    (h4 M A hA)).1

/-- **Clause (5) (naturality in the coefficient module) at every subgroup** for the cup pairing with
a place-dependent invariant.  It needs only the diagonal-tensor rules `hdiag`. -/
theorem cupH_natural
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      inv H (c + c') = inv H c + inv H c')
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv H c = 0)
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv (SSGRoute.decomp k A) c = 0)
    (hdiag : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
      (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) =
        TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
    [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hff' : ∀ (φ : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
      f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) :
    Work.SSGRoute.pairOfInvH p k Ω K T inv M₂ H (fun σ => f (a σ)) b =
      Work.SSGRoute.pairOfInvH p k Ω K T inv M H a (fun σ => f' (b σ)) :=
  Work.SSGRoute.E7Fin.pairOfInv_natural p k Ω K T (inv H) M M₂
    (hdiag M) (hdiag M₂) f hf f' hff' H a b ha hb

/-- **Clause (6) (orthogonality on unramified classes) at every good place** for the cup pairing with
a place-dependent invariant. -/
theorem cupH_unramified
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      inv H (c + c') = inv H c + inv H c')
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv H c = 0)
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv (SSGRoute.decomp k A) c = 0)
    (hdiag : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
      (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) =
        TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (h4 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
          (∀ b : (Ω ≃ₐ[k] Ω) →
              Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
          (∀ a : (Ω ≃ₐ[k] Ω) → M,
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) :
    Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0 :=
  (Work.SSGRoute.pairOfInvH_pairClauses p k Ω K T inv (SSGRoute.decomp k A)
    hinv_add (fun c hc => hinv_cob (SSGRoute.decomp k A) c hc) hinv_unram
    M (hdiag M) (isLocConstOn_res_smul_dualMod (K := K) (H := SSGRoute.decomp k A)
      (X := M) (T' := T) _)
    (h4 M A hA)).2.2 A a b hA hpA hramA ha hb hiner

end

end Work.SSGRoute
