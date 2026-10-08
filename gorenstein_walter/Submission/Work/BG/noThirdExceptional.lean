import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma34Exc
import Submission.Work.BG.noThirdSfixedFour
import Submission.Work.BG.noThirdSfixedNeFour
import Submission.Work.GLUE.Defs

/-!
# `Work.BG.noThirdExceptional`

The exceptional configuration of Bender–Glauberman 1981, Lemma 3.4, in the case in which the
non-`s`-fixed character `ν` is a *linear* character `λ_β = lamCF C β` of `H₀` with
`λ_β(t) = -1` and `D.n = 4`.  The conclusion is that `𝒮(f λ_β) = bset C f (f (λ_β))` has no
member other than `λ_β` and its `s`-conjugate.

Assembly:

* `λ_β` is irreducible (`lamCF_isIrreducible`), coherence at its orbit gives
  `f (λ_β) ∈ ℤ[Irr G]` of norm `1`, so `f (λ_β) ∈ ±Irr(G)` and `λ_β ∈ 𝒮(f λ_β)`.
* `sconj '' Λλ_β = Λλ_β` because `(λ_β)^s = λ_{β⁻¹} = λ_{β⁻²}·λ_β ∈ Λλ_β`.
* A third member `ξ` of `𝒮(f λ_β)` which is not `s`-fixed is impossible by Theorem 3.2
  (`|𝒮| ≤ 3`, `Work.BG.l34_no_third_nonfixed`).
* If `ξ` is `s`-fixed, the two cases `|Λξ| = 4` and `|Λξ| ≠ 4` are the two sub-cases of the
  exceptional configuration (`Work.BG.l34Exc_sfixed_four`, `Work.BG.l34Exc_sfixed_ne_four`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

section Irr

variable {G : Type} [Group G] [Finite G]

/-- `λ_β = lamCF C β` is the inflation of a linear character of `H₀/U`, hence irreducible. -/
theorem lamCF_isIrreducible (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    IsIrreducibleCharacter (lamCF C β) := by
  have h1triv : lamCF C (1 : quotGroup C.P →* ℂˣ) = trivialClassFunction ↥C.P.H0 := by
    rw [lamCF_one]
    ext h
    simp [linearClassFunction_apply, trivialClassFunction_apply]
  have h1irr : IsIrreducibleCharacter (lamCF C (1 : quotGroup C.P →* ℂˣ)) := by
    rw [h1triv]; exact trivialClassFunction_isIrreducible
  have hmem : lamCF C β ∈ Lambda C.P := ⟨β, rfl⟩
  have h := lambda_mul_irreducible C.P hmem h1irr
  have hmul : lamCF C β * lamCF C (1 : quotGroup C.P →* ℂˣ) = lamCF C β := by
    rw [lamCF_one, ClassFunction.mul_linearClassFunction_one]
  simpa [hmul] using h

end Irr

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem noThirdExceptional {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hcompat : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (β : Work.BG.quotGroup C.P →* ℂˣ) (hβt : Work.BG.lamCF C β C.t = -1)
    (hβs : Work.BG.sconj C (Work.BG.lamCF C β) ≠ Work.BG.lamCF C β)
    (horb : (Work.BG.lamOrbit C (Work.BG.lamCF C β)).ncard = D.n) (h4 : D.n = 4) :
    ∀ ξ ∈ Work.GW2.C16.bset C f (f (Work.BG.lamCF C β)),
      ξ ≠ Work.BG.lamCF C β → ξ ≠ Work.BG.sconj C (Work.BG.lamCF C β) → False := by
  intro ξ hξ hξ1 hξ2
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  -- `λ_β` is irreducible, and coherence gives the norm-`1` data at its orbit
  have hνirr : IsIrreducibleCharacter (lamCF C β) := lamCF_isIrreducible C β
  have hG := hf.1 (lamCF C β) hνirr
  have hE : lamCF C β ∈ orbitKey C (lamCF C β) := Or.inl (s02c_LamEquiv_refl C _)
  obtain ⟨hZI, -, hnorm, -, -, -⟩ := hG (lamCF C β) hE (lamCF C β) hE hνirr hνirr
  have hnorm1 : ClassFunction.inner (f (lamCF C β)) (f (lamCF C β)) = 1 := by
    rw [hnorm, if_neg hβs]
  have hχpm : IsPmIrr (f (lamCF C β)) :=
    isPmIrr_of_mem_ZIrr_inner_self_eq_one hZI hnorm1
  have hνmem : lamCF C β ∈ bset C f (f (lamCF C β)) :=
    ⟨hνirr, by rw [hnorm1]; norm_num⟩
  -- `(λ_β)^s = λ_{β⁻¹} = λ_{β⁻²}·λ_β ∈ Λλ_β`, so `Λλ_β` is `s`-stable
  have hkey : (β⁻¹ * β⁻¹) * β = β⁻¹ :=
    (mul_assoc β⁻¹ β⁻¹ β).trans
      ((congrArg (fun z => β⁻¹ * z) (inv_mul_cancel β)).trans (mul_one β⁻¹))
  have hsconjmem : LamEquiv C (lamCF C β) (sconj C (lamCF C β)) := by
    refine ⟨β⁻¹ * β⁻¹, ?_⟩
    rw [LamCFFixed.sconj_lamCF, ← lamCF_mul, hkey]
  have hinv : sconj C '' lamOrbit C (lamCF C β) = lamOrbit C (lamCF C β) := by
    rw [s02c_sconj_image_lamOrbit C (sconjLam C) (lamCF C β)]
    exact (s02c_lamOrbit_eq_of_lamEquiv C hsconjmem).symm
  have h4L : (lamOrbit C (lamCF C β)).ncard = 4 := horb.trans h4
  -- split on the `s`-fixedness of the third member
  by_cases hfix : sconj C ξ = ξ
  · by_cases hξ4 : (lamOrbit C ξ).ncard = 4
    · exact noThirdSfixedFour D C hcompat hS3 f hf (f (lamCF C β)) hχpm
        (lamCF C β) hνmem hβs (Or.inr horb) h4L hinv ξ hξ hξ1 hξ2 hfix hξ4
    · exact noThirdSfixedNeFour D C hcompat hS3 f hf (f (lamCF C β)) hχpm
        (lamCF C β) hνmem hβs (Or.inr horb) h4L hinv ξ hξ hξ1 hξ2 hfix hξ4
  · exact l34_no_third_nonfixed D C hcompat hS3 f hf (f (lamCF C β)) hχpm
      (lamCF C β) hνmem hβs ξ hξ hξ1 hξ2 hfix

end Work.BG
