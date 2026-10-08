import Mathlib
import Submission.Work.BG.HatInjDefs

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Degree-weighted multiplicity sum of an induced character.** For a finite group `U`, a
subgroup `C ≤ U`, and `β ∈ Irr(C)`, let `p α` be the multiplicity `(α|_C, β)_C` of `β` in the
restriction of `α ∈ Irr(U)` and `d α` the degree `α(1)` (similarly `dβ = β(1)`). If `p`, `d`, `dβ`
are natural numbers realizing these quantities, then the degree-weighted multiplicity sum equals
`[U : C] · β(1)`: `Σ_{α ∈ Irr U} p α · d α = [U : C] · dβ`.
Route: Fourier expansion of the induced character `β^U` at `1`
(`sum_inner_irreducibleCharacter_smul`, `ClassFunction.induce_apply_one`), Frobenius reciprocity
(`ClassFunction.inner_induce_eq_inner_restrict`), and `star`-symmetry of the inner product. -/
theorem multiplicityDegreeNat {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (C : Subgroup U) [Fintype ↥C]
    [Invertible (Nat.card ↥C : ℂ)] [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter U)]
    (β : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C)
    (p : OddOrder.RepresentationTheory.IrreducibleCharacter U → ℕ)
    (hp : ∀ α : OddOrder.RepresentationTheory.IrreducibleCharacter U,
        OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity C (α : OddOrder.RepresentationTheory.ClassFunction U ℂ)
          (β : OddOrder.RepresentationTheory.ClassFunction ↥C ℂ) = (p α : ℂ))
    (d : OddOrder.RepresentationTheory.IrreducibleCharacter U → ℕ)
    (hd : ∀ α : OddOrder.RepresentationTheory.IrreducibleCharacter U,
        (α : OddOrder.RepresentationTheory.ClassFunction U ℂ) 1 = (d α : ℂ))
    (dβ : ℕ) (hβ : (β : OddOrder.RepresentationTheory.ClassFunction ↥C ℂ) 1 = (dβ : ℂ)) :
    (∑ α : OddOrder.RepresentationTheory.IrreducibleCharacter U, p α * d α) = C.index * dβ := by
  -- Fourier expansion of the induced character `β^U` at the identity.
  have hF := sum_inner_irreducibleCharacter_smul (G := U)
      (ClassFunction.induce C (β : ClassFunction ↥C ℂ))
  have hval := congrArg (fun g : ClassFunction U ℂ => g 1) hF
  have hmain : (∑ α : IrreducibleCharacter U,
        ClassFunction.inner (ClassFunction.induce C (β : ClassFunction ↥C ℂ)) (α : ClassFunction U ℂ)
          * ((α : ClassFunction U ℂ) 1)) = (C.index : ℂ) * (dβ : ℂ) := by
    rw [show (∑ α : IrreducibleCharacter U,
        ClassFunction.inner (ClassFunction.induce C (β : ClassFunction ↥C ℂ)) (α : ClassFunction U ℂ)
          * ((α : ClassFunction U ℂ) 1))
        = (∑ χ : IrreducibleCharacter U,
            ClassFunction.inner (ClassFunction.induce C (β : ClassFunction ↥C ℂ))
              (χ : ClassFunction U ℂ) • (χ : ClassFunction U ℂ)) 1 from by
          simp [ClassFunction.smul_apply]]
    rw [hval, ClassFunction.induce_apply_one C (β : ClassFunction ↥C ℂ), hβ]
  -- Each inner product is the multiplicity `p α` (Frobenius + `star`-symmetry), each value a
  -- degree, so the sum rewrites as `Σ_α p α · d α` cast to `ℂ`.
  have hcast : (∑ α : IrreducibleCharacter U, (p α : ℂ) * (d α : ℂ))
      = (C.index : ℂ) * (dβ : ℂ) := by
    calc (∑ α : IrreducibleCharacter U, (p α : ℂ) * (d α : ℂ))
        = ∑ α : IrreducibleCharacter U,
            ClassFunction.inner (ClassFunction.induce C (β : ClassFunction ↥C ℂ))
              (α : ClassFunction U ℂ) * ((α : ClassFunction U ℂ) 1) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          have hinner : ClassFunction.inner (ClassFunction.induce C (β : ClassFunction ↥C ℂ))
              (α : ClassFunction U ℂ) = (p α : ℂ) := by
            rw [ClassFunction.inner_induce_eq_inner_restrict]
            rw [ClassFunction.inner_star_comm]
            rw [← ClassFunction.restrictionMultiplicity_def, hp α, star_natCast]
          rw [hinner, hd α]
      _ = (C.index : ℂ) * (dβ : ℂ) := hmain
  -- Descend the `ℂ`-identity to `ℕ`.
  have hnat : ((∑ α : IrreducibleCharacter U, p α * d α : ℕ) : ℂ)
      = ((C.index * dβ : ℕ) : ℂ) := by
    push_cast
    exact hcast
  exact Nat.cast_injective hnat

end Work.BG
