import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Poitou–Tate counting identity for the relaxed Selmer groups

This file isolates the **second arithmetic input** of `Work.SSGRoute.PT.pt_canonical_relaxed`
(the first being the canonical local pairing with its local axioms and reciprocity, node
`SSGRoute/PT/pt_canonical_pairing`).  It is the Euler-characteristic half of the H¹-part of the
Poitou–Tate nine-term sequence:

`|V| · |W| = |∏_{S ∪ C} H¹|`

where

* `V` is the image, in the finite space
  `∏_{A ∈ S} H¹(D_A, M) × ∏_{c ∈ C} H¹(⟨c⟩, M)`,
  of the *relaxed* Selmer group of `M` (global locally constant cocycles of `M` unramified
  outside `S ∪ cs(N)`), and
* `W` is the image of the *relaxed dual* Selmer group of `M' = DualMod p (M ⊗ T)` in the
  corresponding space with coefficients in `M'` (the same size, by local Tate duality at every
  place of `S ∪ C`): global locally constant cocycles of `M'` that are coboundaries on `D_B` for
  every finite place `B` split in `N` and outside `S`, and vanish on inertia at every finite
  place `B` outside `S` that is not split in `N`.

The identity is **independent of the choice of local pairing**, so it composes with node
`SSGRoute/PT/pt_canonical_pairing`.  Together with the verified
`Work.SSGRoute.PT.pt_orthogonality_of_realizable` (`V ⊆ W^⊥`, from reciprocity and the local
clauses) it gives `V = W^⊥`, hence the realizability clause (3) of
`Work.SSGRoute.PT.pt_canonical_relaxed`; and with `Work.SSGRoute.pt_selmer_relaxed`'s counting
argument it gives that statement for *every* family of local pairings satisfying the same axioms.

Its proof is the counting content of `Work.SSGRoute/PT/pt_selmer_relaxed.lean`'s route, i.e. the
Euler characteristic of the Selmer complex (Milne, *Arithmetic Duality Theorems*, I.4.10;
Neukirch–Schmidt–Wingberg 8.6.8), and requires the local duality dimension equality at every
place of `S ∪ C`.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.PT

/-- The **primal** local class space at `S ∪ C`: one local `H¹`-class of `M` at each place of one
place per prime in `S`, and at each involution in `C`. -/
abbrev primalClasses (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω)) : Type :=
  ((A : {A : ValuationSubring Ω // A ∈ S}) →
      H1loc p k Ω K M (SSGRoute.decomp k A.1)) ×
    ((c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) → H1loc p k Ω K M (Subgroup.zpowers c.1))

/-- The class of local data `(α, β)` in the primal local class space. -/
noncomputable def primalClassOf (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :
    primalClasses p k Ω K M S C :=
  (fun A => toClass p k Ω K M (SSGRoute.decomp k A.1) (α A.1),
    fun c => toClass p k Ω K M (Subgroup.zpowers c.1) (β c.1))

/-- **A primal class is realizable** if some global locally constant cocycle `ε` of `M`, unramified
outside `S ∪ cs(N)`, has the prescribed local classes at `S ∪ C`. -/
def IsRealizableClass (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N) (M : Type)
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (x : primalClasses p k Ω K M S C) : Prop :=
  ∃ (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (ε : (Ω ≃ₐ[k] Ω) → M),
    primalClassOf p k Ω K M S C α β = x ∧
    SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
    (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
      (fun σ => ε σ - α A σ)) ∧
    (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
      (fun σ => ε σ - β c σ)) ∧
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0

/-- **A dual class lies in the relaxed dual Selmer group** if some global locally constant cocycle
`b` of `M'` has it as its local class tuple and satisfies the relaxed dual local conditions. -/
def IsDualSelmerClass (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) : Prop :=
  ∃ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
    primalClassOf p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C
        (fun _ => b) (fun _ => b) = y ∧
    SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) ∧
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0

/-! The counting identity itself is requested as the separate declaration
`SSGRoute/PT/pt_selmer_counting_identity` (file `pt_selmer_counting_identity.lean`), so that the
definitions above are a stable vocabulary module. -/

end Work.SSGRoute.PT
