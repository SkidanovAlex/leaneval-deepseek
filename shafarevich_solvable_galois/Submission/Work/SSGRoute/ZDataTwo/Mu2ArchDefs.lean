import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` local Tate system *with the archimedean terms*: the predicate

`Work.SSGRoute.ZDataTwo.IsMu2LocalTateSystemWithArch k Ω K pair` is the shape of the `p = 2`
local Tate system that the `p = 2` realisation consumes.  It differs from the finite-places-only
predicates `Work.SSGRoute.ZDataMup.IsLocalTateSystem` / `IsProductFormula` in exactly the way that
makes the `p = 2` case work, and it mirrors the `M = T = ZMod 2` instance of the hypotheses of
`Work.SSGRoute.PT.pt_selmer_relaxed`:

* the local axioms are required at the finite decomposition groups `decomp k A` **and** at the
  involution subgroups `Subgroup.zpowers c` (the real places, encoded as involutions);
* the cochain variables of the reciprocity clause are global (`⊤`, i.e. cocycles on all of `G_k`),
  not only cocycles on `G_K`: with the latter, the reciprocity would be refuted by the indicator of
  an involution outside `G_K` (the local axioms at `Subgroup.zpowers c` are non-degenerate, so that
  term cannot vanish);
* the excluded places satisfy `B ∤ 2`, `B` unramified in `K`, and `a`, `b` vanish on the inertia of
  `B`;
* the reciprocity sum runs over a finite set `S'` of finite places **together with** a finite set
  `C'` of involution representatives.

The finite-places-only version is *false* at `p = 2`: with `k = K = ℚ`, `S'` the place over `2` and
`a = b` the sign character, the finite sum is `1 ≠ 0` while only `inv₂ + inv_ℝ = 1 + 1 = 0` is
reciprocity.  The archimedean half of the pairing is `Work.SSGRoute.archPair` (non-degeneracy
`Work.SSGRoute.archPair_nondegenerate`), the finite half is the local Hilbert symbol, and the
reciprocity with the archimedean place is
`Work.HilbertSymbolGeneral.hilbertReciprocityTwo`.

This is the shared vocabulary for the delegated statement
`Work.SSGRoute.ZDataTwo.mu2LocalTateSystemWithArch` (the `p = 2`, `M = T = ZMod 2` specialisation of
`Work.SSGRoute.canonical_localPairing_with_reciprocity`, nodes `E7`+`G1`); it is placed here so that
the target can be stated without any pointwise-action notation.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod 2)] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) (ZMod 2)]

/-- **The `p = 2` local Tate system with the archimedean terms.** -/
def IsMu2LocalTateSystemWithArch
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod 2) → ((Ω ≃ₐ[k] Ω) → ZMod 2) → ZMod 2) :
    Prop :=
  (∀ H : Subgroup (Ω ≃ₐ[k] Ω),
    ((∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A) ∨
      (∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c)) →
    (∀ (a a' b : (Ω ≃ₐ[k] Ω) → ZMod 2),
      (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
      (IsCocycleOn (res k K) H a' ∧ IsLocConstOn H a') →
      (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
      pair H (a + a') b = pair H a b + pair H a' b) ∧
    (∀ (a b b' : (Ω ≃ₐ[k] Ω) → ZMod 2),
      (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
      (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
      (IsCocycleOn (res k K) H b' ∧ IsLocConstOn H b') →
      pair H a (b + b') = pair H a b + pair H a b') ∧
    (∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod 2),
      (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
      (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
      (IsCoboundaryOn (res k K) H a ∨ IsCoboundaryOn (res k K) H b) →
      pair H a b = 0) ∧
    (∀ a : (Ω ≃ₐ[k] Ω) → ZMod 2,
      (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
      (∀ b : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
        pair H a b = 0) →
      IsCoboundaryOn (res k K) H a) ∧
    (∀ b : (Ω ≃ₐ[k] Ω) → ZMod 2,
      (IsCocycleOn (res k K) H b ∧ IsLocConstOn H b) →
      (∀ a : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (IsCocycleOn (res k K) H a ∧ IsLocConstOn H a) →
        pair H a b = 0) →
      IsCoboundaryOn (res k K) H b)) ∧
  (∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod 2),
    IsCocycleOn (res k K) ⊤ a → IsLocConstOn ⊤ a →
    IsCocycleOn (res k K) ⊤ b → IsLocConstOn ⊤ b →
    ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', IsFinPlace k A) →
    (∀ A ∈ S', ∀ B ∈ S', IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S', ¬ IsConjPlace k A B) →
      ¬ B.valuation (2 : Ω) < 1 ∧ ¬ IsRamifiedIn k K B ∧
        ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
    ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
    (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 →
      ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
    (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
    ∑ A ∈ S', pair (decomp k A) a b + ∑ c ∈ C', pair (Subgroup.zpowers c) a b = 0)

end Work.SSGRoute.ZDataTwo
