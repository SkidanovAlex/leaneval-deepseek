import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Definitions for the odd-`p`, one-dimensional `z`-data route (`μ_p` case)

Shared vocabulary of the node `Work.SSGRoute.ZDataMup.isMupZData_odd`: the local Tate pairing system
of Schmidt--Wingberg §4 (`IsLocalTateSystem`), the Hilbert-symbol product formula in the form the
realisation consumes (`IsProductFormula`) and the orthogonality of local data against the dual
Selmer group (`IsOrthogonalToDual`).

These live in this module (rather than in the node's own file) so that a proof of the realisation
`Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation` can be placed in a module importing *this* file
only: were it to import the node's file, the node could not import it back (import cycle) and the
realisation could not be used in the assembly.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The local Tate pairings on the trivial `𝔽_p[G_K]`-module `ZMod p`, one for each decomposition
group, with their local axioms: `𝔽_p`-bilinearity on local `1`-cocycles, vanishing on a coboundary
in either argument, and perfectness (left non-degeneracy) on cocycles modulo coboundaries. -/
structure IsLocalTateSystem (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
      ZMod p) : Prop where
  additive_left : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup) →
      ∀ (a a' b : (Ω ≃ₐ[k] Ω) → ZMod p),
        (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
        (IsCocycleOn (res k K) H a' ∧ IsLocConstOn H a') →
        (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
        pair H (a + a') b = pair H a b + pair H a' b
  additive_right : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup) →
      ∀ (a b b' : (Ω ≃ₐ[k] Ω) → ZMod p),
        (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
        (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
        (IsCocycleOn (res k K) H b' ∧ IsLocConstOn H b') →
        pair H a (b + b') = pair H a b + pair H a b'
  vanishes_coboundary : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup) →
      ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
        (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
        (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
        (IsCoboundaryOn (res k K) H a ∨ IsCoboundaryOn (res k K) H b) →
        pair H a b = 0
  perfect : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup) →
      ∀ a : (Ω ≃ₐ[k] Ω) → ZMod p,
        (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
        (∀ b : (Ω ≃ₐ[k] Ω) → ZMod p,
          (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
          pair H a b = 0) →
        IsCoboundaryOn (res k K) H a

/-- The Hilbert-symbol product formula for a local Tate system, in the form consumed by the
realisation P1: for global cocycles `a`, `b` which are unramified outside a finite set `T'` of
pairwise non-conjugate places (one place per conjugacy class), the sum of the local pairings over
the places of `T'` vanishes. -/
def IsProductFormula (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
      ZMod p) : Prop :=
  ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
    IsCocycleOn (res k K) K.fixingSubgroup a →
    IsLocConstOn K.fixingSubgroup a →
    IsCocycleOn (res k K) K.fixingSubgroup b →
    IsLocConstOn K.fixingSubgroup b →
    ∀ (T' : Finset (ValuationSubring Ω)), (∀ A ∈ T', IsFinPlace k A) →
    (∀ A ∈ T', ∀ B ∈ T',
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
    ∑ A ∈ T', pair (decomp k A ⊓ K.fixingSubgroup) a b = 0

/-- Local data `f` at a finite set `T` (one place per `G_K`-conjugacy class) is *orthogonal to the
dual Selmer group*: it pairs trivially with every global cocycle `b` which is unramified outside
the conjugates of `T`.  This is the hypothesis of the realisation P1, exposed separately so that
the realisation and the arithmetic that supplies it can be stated independently. -/
def IsOrthogonalToDual (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
      ZMod p)
    (T : Finset (ValuationSubring Ω)) (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p) : Prop :=
  ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p,
    IsCocycleOn (res k K) K.fixingSubgroup b →
    IsLocConstOn K.fixingSubgroup b →
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → b σ = 0) →
    ∑ A ∈ T, pair (decomp k A ⊓ K.fixingSubgroup) (f A) b = 0

end Work.SSGRoute.ZDataMup
