import Mathlib
import Submission.Work.SSGRoute.ZSplit.levelKCounting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared vocabulary for the level-`K` local-pairing pieces

This module fixes the two predicates in terms of which the deep level-`K` inputs of
`Work.SSGRoute.ZSplit.levelK_local_pairing_with_reciprocity` are stated, so that the pieces can be
requested from the fleet without touching the target file:

* `IsLevelKLocalTateSystem` — the local axioms (bilinearity on locally constant cocycles, vanishing
  on coboundaries, perfectness on cocycles) for a cochain pairing at the level-`K` local groups
  `decomp k A ⊓ K.fixingSubgroup`;
* `HasLevelKReciprocity` — the level-`K` product formula (Hilbert-symbol reciprocity): the sum of
  the local values of a pair of *global* locally constant cocycles over one place per prime of `K`
  vanishes, outside which both cocycles are unramified;
* the place-set structure is the workspace's `Work.SSGRoute.kConj` (level-`K` conjugacy of places,
  whose classes are the primes of `K`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZSplit

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The level-`K` local axioms** for a cochain pairing, at the level-`K` local groups
`decomp k A ⊓ K.fixingSubgroup`: bilinearity on locally constant cocycles, vanishing on a
coboundary in either argument, and perfectness on cocycles. -/
def IsLevelKLocalTateSystem
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p) :
    Prop :=
  ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
    (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
    (∀ (a a' b : (Ω ≃ₐ[k] Ω) → ZMod p),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      pair H (a + a') b = pair H a b + pair H a' b) ∧
    (∀ (a : (Ω ≃ₐ[k] Ω) → ZMod p) (b b' : (Ω ≃ₐ[k] Ω) → ZMod p),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
      pair H a (b + b') = pair H a b + pair H a b') ∧
    (∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
      pair H a b = 0) ∧
    (∀ a : (Ω ≃ₐ[k] Ω) → ZMod p,
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (∀ b : (Ω ≃ₐ[k] Ω) → ZMod p,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair H a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a)

/-- **The level-`K` local Tate axioms with perfectness in both variables.**  This is
`IsLevelKLocalTateSystem` together with the mirror non-degeneracy clause (triviality of the right
kernel on locally constant cocycles), which is what the descent to the local `H¹`-groups consumes. -/
def IsLevelKLocalTateSystemR
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p) :
    Prop :=
  IsLevelKLocalTateSystem p k Ω K pair ∧
  ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
    (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
    ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p,
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (∀ a : (Ω ≃ₐ[k] Ω) → ZMod p,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        pair H a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b

/-- **The level-`K` product formula**: for global locally constant cocycles `a`, `b` on `G_K` and a
finite set `T'` of pairwise non-`G_K`-conjugate finite places outside which both are unramified,
the sum of the local pairings over `T'` vanishes. -/
def HasLevelKReciprocity
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p) :
    Prop :=
  ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
    SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a →
    SSGRoute.IsLocConstOn K.fixingSubgroup a →
    SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b →
    SSGRoute.IsLocConstOn K.fixingSubgroup b →
    ∀ T' : Finset (ValuationSubring Ω), (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
    (∀ A ∈ T', ∀ B ∈ T', Work.SSGRoute.kConj k Ω K A B → A = B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T', ¬ Work.SSGRoute.kConj k Ω K A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
    ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a b = 0

end Work.SSGRoute.ZSplit
