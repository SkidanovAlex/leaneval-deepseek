import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## A small additivity lemma for induction

`ClassFunction.induce` is not bundled as a linear map in the odd-order library, so we record
the additivity statement (in the `sub` form needed below) by hand. -/

/-- Induction is additive: `Ind_H^G (θ - ψ) = Ind_H^G θ - Ind_H^G ψ`. -/
theorem chiDeg_induce_sub {G : Type} [Group G] [Fintype G] {H : Subgroup G}
    [Invertible (Nat.card ↥H : ℂ)] (θ ψ : ClassFunction ↥H ℂ) :
    ClassFunction.induce H (θ - ψ) =
      ClassFunction.induce H θ - ClassFunction.induce H ψ := by
  have h : ClassFunction.induce H (-ψ) = -ClassFunction.induce H ψ := by
    rw [show -ψ = (-1 : ℂ) • ψ from by simp, ClassFunction.induce_smul]
    simp
  simp only [sub_eq_add_neg, ClassFunction.induce_add, h]

/- **The `Λ`-orbit differences are `f`-invariants.**  For `μ, ν ∈ Irr(H₀)` with `ν = λ μ`
(`λ ∈ Λ`) and `χ` any class function on `G`, the difference of the multiplicities of the
induced characters `Ind_{H₀}^G μ`, `Ind_{H₀}^G ν` in `χ` equals the difference of the
multiplicities of their coherent extensions `f μ`, `f ν`.

Proof: clause (iii) of the coherence theorem (`GoodOn C (orbitKey C μ) f`, applied to the two
members `μ, ν` of the key `Λμ ∪ (Λμ)^s`) gives `Ind_{H₀}^G (μ - ν) = f μ - f ν`; then apply
`χ`-inner products and use additivity of `Ind` and of the inner product in the second
argument.  No irreducibility of `χ` and no `Fintype ↥C.P.H0` are needed. -/
open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem chiDegDiffInvariant {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) :
    ∀ μ ν : IrreducibleCharacter ↥C.P.H0,
      Work.BG.LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) (ν : ClassFunction ↥C.P.H0 ℂ) →
      (ClassFunction.inner χ (ClassFunction.induce C.P.H0 (μ : ClassFunction ↥C.P.H0 ℂ)) -
        ClassFunction.inner χ (ClassFunction.induce C.P.H0 (ν : ClassFunction ↥C.P.H0 ℂ))) =
      (ClassFunction.inner χ (f (μ : ClassFunction ↥C.P.H0 ℂ)) -
        ClassFunction.inner χ (f (ν : ClassFunction ↥C.P.H0 ℂ))) := by
  intro μ ν hlam
  have hμ : IsIrreducibleCharacter (μ : ClassFunction ↥C.P.H0 ℂ) := μ.2
  have hν : IsIrreducibleCharacter (ν : ClassFunction ↥C.P.H0 ℂ) := ν.2
  -- `μ` lies on its own key `Λμ ∪ (Λμ)^s` (refl. of `LamEquiv`, `λ₁ = 1`).
  have hrefl : Work.BG.LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ)
      (μ : ClassFunction ↥C.P.H0 ℂ) := by
    refine ⟨1, ?_⟩
    ext h
    simp only [ClassFunction.mul_apply, lamCF, ClassFunction.compHom_apply,
      linearClassFunction_apply, MonoidHom.one_apply, Units.val_one, one_mul]
  -- clause (i) of `IsCoherent` at the key of `μ`, read at the two members `μ`, `ν`.
  have hgood := (hf.1 (μ : ClassFunction ↥C.P.H0 ℂ) hμ)
      (μ : ClassFunction ↥C.P.H0 ℂ) (Or.inl hrefl)
      (ν : ClassFunction ↥C.P.H0 ℂ) (Or.inl hlam) hμ hν
  -- clause (iii): `Ind_{H₀}^G (μ - ν) = f μ - f ν`.
  have hind : ClassFunction.induce C.P.H0
        ((μ : ClassFunction ↥C.P.H0 ℂ) - (ν : ClassFunction ↥C.P.H0 ℂ)) =
      f (μ : ClassFunction ↥C.P.H0 ℂ) - f (ν : ClassFunction ↥C.P.H0 ℂ) :=
    hgood.2.2.2.1 hlam
  have hsub : ClassFunction.induce C.P.H0 (μ : ClassFunction ↥C.P.H0 ℂ) -
        ClassFunction.induce C.P.H0 (ν : ClassFunction ↥C.P.H0 ℂ) =
      ClassFunction.induce C.P.H0
        ((μ : ClassFunction ↥C.P.H0 ℂ) - (ν : ClassFunction ↥C.P.H0 ℂ)) :=
    (chiDeg_induce_sub _ _).symm
  rw [← ClassFunction.inner_sub_right, ← ClassFunction.inner_sub_right, hsub, hind]

end Work.BG
