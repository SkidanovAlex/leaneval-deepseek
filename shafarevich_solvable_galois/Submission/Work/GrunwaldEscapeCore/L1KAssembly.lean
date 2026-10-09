import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The final bookkeeping of the escape statement at `L₁ = K`

This small module contains the *last step* of `Work.GrunwaldEscapeCore.grunwald_escape_relative_L1K`
(the escape realisation of Grünwald–Wang at `L₁ = K`, `g = 0`): given the Grünwald element
`a ∈ ↥Kˣ` realising the datum `h` at `T` and the output of a *correction step* — a place `Q` split
in `L` outside the `↥K`-classes of `T`, and an element `b ∈ ↥Kˣ` whose Kummer character agrees with
that of `a` on every local group `D_A` and is unramified outside the `↥K`-classes of `T` and of `Q`
— it produces the global additive, locally constant class `z` together with all the clauses of the
conclusion.  The class `z` is the Kummer character of `b`.

It is kept apart from the main file, and with deliberately small imports, because it is the piece
that the correction steps of the lane consume (e.g.
`Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionL1K`, whose proof is exactly this bookkeeping applied
to `Work.GrunwaldEscapeCore.grunwald_escape_relative_L1K`); importing *this* module rather than the
main file keeps the dependency graph acyclic.
-/

namespace Work.GrunwaldEscapeCore

open scoped Pointwise
open NumberField IsDedekindDomain

set_option linter.unusedVariables false

/-- **The escape realisation at `L₁ = K` from the correction step.**

Given the Grünwald element `a ∈ ↥Kˣ` realising the datum `h` at `T` and the *output of the
correction step* — a place `Q` split in `L` outside the `↥K`-classes of `T`, and an element
`b ∈ ↥Kˣ` whose Kummer character agrees with that of `a` on every local group `D_A` and is
unramified outside the `↥K`-classes of `T` and of `Q` — this produces the global additive class `z`
of the conclusion. -/
theorem escape_L1K_of_correction (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (T : Finset (ValuationSubring Ω))
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p
          (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (Q : ValuationSubring Ω) (b : (↥K)ˣ)
    (hQfin : SSGRoute.IsFinPlace k Q) (hQsplit : SSGRoute.IsSplitIn k L Q)
    (hQnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q)
    (hagree : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p
            (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p
            (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) a
            (Work.SSGRoute.gesLocalToGalK K σ))
    (hesc : ∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ Work.SSGRoute.gesKConj K Q B →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p
            (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q' : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q' ∧ SSGRoute.IsSplitIn k L Q' ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q') ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) →
        (∀ τ ∈ K.fixingSubgroup, τ • Q' ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  refine ⟨Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, hQfin, hQsplit, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro A hA τ hτ hτA
    exact hQnotT A hA ⟨τ, hτ, hτA⟩
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto, hagree A hA ⟨σ, hσ⟩]
    exact (ha A hA ⟨σ, hσ⟩).symm
  · intro B hB hnotT hnotQ σ hσ hI
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    refine hesc B hB ?_ ?_ σ hσ hI
    · intro A hA hconj
      obtain ⟨τ, hτ, hτA⟩ := hconj
      exact hnotT A hA τ hτ hτA
    · intro hconj
      obtain ⟨τ, hτ, hτQ⟩ := hconj
      exact hnotQ τ hτ hτQ

end Work.GrunwaldEscapeCore
