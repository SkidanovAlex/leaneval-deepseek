import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma33Case2

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16

/-- The correction term `Ssum` of BG Theorem 3.2's counting identity, in the configuration where
`𝒮(χ) = bset C f χ` consists of three distinct `s`-fixed characters `e₁, e₂, e₃` with
`|Λe₁| = D.n` and `|Λe₂| = |Λe₃| = 4`: then `Ssum C f χ = 1/D.n + 1/4 + 1/4`.
Exact analogue of the proved `Work.BG.Ssum_eq_three_div` (same file), which treats the case
`|Λeᵢ| = D.n` for all three; the proof is the same rewrite via `Ssum_term_ofReal`,
`bset_classify_of_three`, `bsetInd_of_mem`/`bsetInd_of_notMem` and `cOrbitR = 0` on `s`-fixed
characters. -/
theorem cef_Ssum_eq {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ → OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    (e₁ e₂ e₃ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)
    (h₁ : (e₁ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) ∈ Work.GW2.C16.bset C f χ)
    (h₂ : (e₂ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) ∈ Work.GW2.C16.bset C f χ)
    (h₃ : (e₃ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) ∈ Work.GW2.C16.bset C f χ)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hs₁ : Work.BG.sconj C (e₁ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) = (e₁ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ))
    (hs₂ : Work.BG.sconj C (e₂ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) = (e₂ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ))
    (hs₃ : Work.BG.sconj C (e₃ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) = (e₃ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ))
    (ho₁ : (Work.BG.lamOrbit C (e₁ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)).ncard = D.n)
    (ho₂ : (Work.BG.lamOrbit C (e₂ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)).ncard = 4)
    (ho₃ : (Work.BG.lamOrbit C (e₃ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)).ncard = 4)
    (hle : (Work.GW2.C16.bset C f χ).ncard ≤ 3) :
    Work.BG.Ssum C f χ = ((((1 : ℝ) / (D.n : ℝ) + 1 / 4 + 1 / 4) : ℝ) : ℂ) := by
  classical
  obtain ⟨-, hclass⟩ :=
    bset_classify_of_three C f χ e₁ e₂ e₃ h₁ h₂ h₃ h12 h13 h23 hle
  have hc1 : cOrbitR C (e₁ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    rw [cOrbitR]
    split_ifs with hh
    · exact absurd hs₁ hh.2
    · rfl
  have hc2 : cOrbitR C (e₂ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    rw [cOrbitR]
    split_ifs with hh
    · exact absurd hs₂ hh.2
    · rfl
  have hc3 : cOrbitR C (e₃ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    rw [cOrbitR]
    split_ifs with hh
    · exact absurd hs₃ hh.2
    · rfl
  have hv1 : bsetInd C f χ e₁ * (1 + cOrbitR C (e₁ : ClassFunction ↥C.P.H0 ℂ)) /
      ((lamOrbit C (e₁ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 1 / (D.n : ℝ) := by
    rw [bsetInd_of_mem h₁, hc1, ho₁]
    norm_num
  have hv2 : bsetInd C f χ e₂ * (1 + cOrbitR C (e₂ : ClassFunction ↥C.P.H0 ℂ)) /
      ((lamOrbit C (e₂ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 1 / 4 := by
    rw [bsetInd_of_mem h₂, hc2, ho₂]
    norm_num
  have hv3 : bsetInd C f χ e₃ * (1 + cOrbitR C (e₃ : ClassFunction ↥C.P.H0 ℂ)) /
      ((lamOrbit C (e₃ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 1 / 4 := by
    rw [bsetInd_of_mem h₃, hc3, ho₃]
    norm_num
  have hterm : Ssum C f χ = (((∑ ν : IrreducibleCharacter ↥C.P.H0,
      bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
        ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) : ℝ) : ℂ) := by
    rw [Ssum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun ν _ => Ssum_term_ofReal C f hf χ hχ ν
  have hF : (∑ ν : IrreducibleCharacter ↥C.P.H0,
      bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
        ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) =
        1 / (D.n : ℝ) + 1 / 4 + 1 / 4 := by
    have hzero : ∀ ν : IrreducibleCharacter ↥C.P.H0,
        ν ∉ ({e₁, e₂, e₃} : Finset (IrreducibleCharacter ↥C.P.H0)) →
        bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
          ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 0 := by
      intro ν hν
      have hmem : (ν : ClassFunction ↥C.P.H0 ℂ) ∉ bset C f χ := by
        intro hb
        rcases hclass ν hb with h | h | h
        · exact hν (by simp [h])
        · exact hν (by simp [h])
        · exact hν (by simp [h])
      rw [bsetInd_of_notMem (ν := ν) hmem]
      ring
    have hsum_eq : (∑ ν : IrreducibleCharacter ↥C.P.H0,
        bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
          ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) =
        ∑ ν ∈ ({e₁, e₂, e₃} : Finset (IrreducibleCharacter ↥C.P.H0)),
          bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) :=
      (Finset.sum_subset (Finset.subset_univ _) (fun ν _ hν => hzero ν hν)).symm
    have hthree : (∑ ν ∈ ({e₁, e₂, e₃} : Finset (IrreducibleCharacter ↥C.P.H0)),
          bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) =
        bsetInd C f χ e₁ * (1 + cOrbitR C (e₁ : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (e₁ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) +
          (bsetInd C f χ e₂ * (1 + cOrbitR C (e₂ : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (e₂ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) +
          (bsetInd C f χ e₃ * (1 + cOrbitR C (e₃ : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (e₃ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ))) := by
      rw [Finset.sum_insert (show e₁ ∉ ({e₂, e₃} : Finset _) by simp [h12, h13]),
        Finset.sum_insert (show e₂ ∉ ({e₃} : Finset _) by simp [h23]), Finset.sum_singleton]
    rw [hsum_eq, hthree, hv1, hv2, hv3]
    ring
  rw [hterm, hF]

end Work.BG
