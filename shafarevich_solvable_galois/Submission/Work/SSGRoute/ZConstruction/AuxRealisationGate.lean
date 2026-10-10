import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZRealV2.AuxOfGrunwaldV2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The auxiliary realisation, as a named gate with the involution hypothesis removed

`Work.SSGRoute.isAuxiliaryZData_of_grunwald_v2` supplies the auxiliary class of Schmidt--Wingberg §4
from the Grünwald-with-escape realisation, but its statement carries the hypothesis

  `hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1`

which is *false* at `p = 2` whenever `K` has a real place (Ω is algebraically closed, so the complex
conjugation at a real place of `K` is an involution of `G_K`).  `hKimag` is used only to discharge
the involutions clause of the realised class; at `p = 2` that clause has to come from the arithmetic
(the escape element must be totally positive).

This file isolates the statement *without* `hKimag` as a named `Prop`,
`Work.SSGRoute.ZConstruction.AuxRealisationGate`, so that

* the odd-`p` instance is a one-line wrapper around the existing theorem
  (`auxRealisationGate_odd` below), and
* a `p = 2` instance can be supplied separately (from the `p = 2` narrow escape oracle; see
  `ACTION_p2_twoFieldRealisation.md`), without touching the generic induction
  (`Work.SSGRoute.ZDataGen.zDataGeneralOfMupAndZetaGen`).

The statement is a verbatim transcription of the binders of
`Work.SSGRoute.isAuxiliaryZData_of_grunwald_v2` minus `hKimag`; the `hgate` hypothesis (the
one-dimensional case of the `z`-construction for the coefficient module `ZMod p`, i.e.
`Work.SSGRoute.IsMupZData p k Ω K` specialised to `ZMod p`) is kept. -/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The auxiliary realisation of §4, without the (false at `p = 2`) involution hypothesis.**
See the module docstring. -/
def AuxRealisationGate (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) : Prop :=
  ∀ (hgate : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
      ∀ (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, IsFinPlace k A) →
      (∀ A ∈ S, ∀ B ∈ S, IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B →
        (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B) →
      ∀ (y : (Ω ≃ₐ[k] Ω) → ZMod p),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h) →
      IsLocConstOn K.fixingSubgroup y →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
        ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = 0) →
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) →
      ∃ z, IsZData p K Λ S y z),
  ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
    ∀ (Λ₀ : IntermediateField k Ω) [FiniteDimensional k Λ₀] [IsGalois k Λ₀], Λ ≤ Λ₀ → K ≤ Λ₀ →
    ∀ (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L], L ≤ Λ₀ →
    ∀ (S₀ : Finset (ValuationSubring Ω)),
    (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L B →
      ∃ A ∈ S₀, IsConjPlace k A B) →
    (∀ A ∈ S₀, IsFinPlace k A) →
    (∀ A ∈ S₀, ∀ B ∈ S₀, IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k Λ₀ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S₀, IsConjPlace k A B) →
    ∀ (S : Finset (ValuationSubring Ω)),
    (∀ A ∈ S, IsFinPlace k A) →
    S ⊆ S₀ →
    (∀ A ∈ S₀, A ∉ S → IsSplitIn k Λ A) →
    ∀ (L₂ : IntermediateField k Ω) [FiniteDimensional k L₂] [IsGalois k L₂],
    K ≤ L₂ → Λ ⊔ L₂ = Λ₀ →
    (∀ σ ∈ K.fixingSubgroup, σ ^ p ∈ L₂.fixingSubgroup) →
    (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ L₂.fixingSubgroup) →
    (∀ A ∈ S, ∀ σ ∈ K.fixingSubgroup, IsInertia k A σ → σ ∈ L₂.fixingSubgroup) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k Λ B →
      ∃ A ∈ S₀, IsConjPlace k A B) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L₂ B →
      ∃ A ∈ S₀, IsConjPlace k A B) →
    ∀ (ν : (Ω ≃ₐ[k] Ω) → ZMod p),
    (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, ν (g * h) = ν g + ν h) →
    IsLocConstOn K.fixingSubgroup ν →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
      ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → ν σ = 0) →
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ν c = 0) →
    (∃ f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ A : ValuationSubring Ω, (∃ A' ∈ S, IsConjPlace k A' A) → f A = ν) ∧
      ∃ yt zF, IsYRealisation p K Λ₀ S S₀ f yt ∧ IsZData p K Λ₀ S₀ yt zF)

/-- **The odd-`p` instance of the gate** from the proved Grünwald-with-escape realisation
(`hKimag` is available for odd `p`, since its domain is empty). -/
theorem auxRealisationGate_odd {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (hp : p ≠ 2) :
    AuxRealisationGate (p := p) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) :=
  fun hgate =>
    isAuxiliaryZData_of_grunwald_v2 p k Ω K ζ hζ hζK (fun h2 => absurd h2 hp) hgate

end Work.SSGRoute.ZConstruction
