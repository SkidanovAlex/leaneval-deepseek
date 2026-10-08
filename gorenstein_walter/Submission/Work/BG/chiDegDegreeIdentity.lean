import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem chiDegDegreeIdentity {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter ↥C.P.H0)] (χ : ClassFunction G ℂ) :
    (∑ θ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χ (ClassFunction.induce C.P.H0 (θ : ClassFunction ↥C.P.H0 ℂ)) *
          (θ : ClassFunction ↥C.P.H0 ℂ) 1) = χ 1 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  -- Fourier expansion of `χ` restricted to `H₀` in the irreducible-character basis of `H₀`.
  have hFourier : ClassFunction.restrict C.P.H0 χ =
      ∑ θ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (θ : ClassFunction ↥C.P.H0 ℂ) •
          (θ : ClassFunction ↥C.P.H0 ℂ) :=
    (sum_inner_irreducibleCharacter_smul (ClassFunction.restrict C.P.H0 χ)).symm
  -- Evaluate the expansion at `1`, using `(restrict H₀ χ) 1 = χ 1`.
  have h1 : χ 1 = ∑ θ : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (θ : ClassFunction ↥C.P.H0 ℂ) *
        (θ : ClassFunction ↥C.P.H0 ℂ) 1 := by
    have h := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ (1 : ↥C.P.H0)) hFourier
    rw [ClassFunction.restrict_apply] at h
    rw [ClassFunction.sum_apply] at h
    simp only [ClassFunction.smul_apply] at h
    simpa using h
  rw [h1]
  -- Frobenius reciprocity `(Res χ, θ)_{H₀} = (χ, Ind θ)_G` in the orientation required.
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [show ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (θ : ClassFunction ↥C.P.H0 ℂ)
       = ClassFunction.inner χ (ClassFunction.induce C.P.H0 (θ : ClassFunction ↥C.P.H0 ℂ)) by
        rw [ClassFunction.inner_star_comm, ← ClassFunction.inner_induce_eq_inner_restrict C.P.H0
          (θ : ClassFunction ↥C.P.H0 ℂ) χ, ClassFunction.inner_star_comm, star_star]]

end Work.BG
