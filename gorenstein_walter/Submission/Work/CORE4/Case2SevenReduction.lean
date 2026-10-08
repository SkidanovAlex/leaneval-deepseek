import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Layer
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.SevenX.piF_le_pi_K0_of_witness

/-!
# The reduction of §4 (7)'s second conjunct to `π(F) ⊆ π(K₀)`

`Submission.Work.CORE4.Case2Seven` (this area) proves, *given* Bender's `X`-argument
`π(F(U)) = π(K₀F)`, that the second conjunct of `Case2SevenFacts` (`π(K₀) = π(F(U))`) is
equivalent to `π(F) ⊆ π(K₀)`.  The `X`-argument itself is
`Submission.Work.CORE4.SevenX.piFU_le_pi_K0F` (proved), and `π(F) ⊆ π(K₀)` is derived from
Bender's (6)-paragraph witness `∃ g ∉ M, F^g ≤ F(U) ∩ M` by
`Submission.Work.CORE4.SevenX.piF_le_pi_K0_of_witness` (proved).

This file combines the three, giving the unconditional equivalence, and the resulting statement
that the conjunct *fails* whenever `K₀ = ⊥`.  The witness itself is *not* a consequence of the
(1)–(6) data (see `NOTES_CASE2SEVEN.md`).

The two lemmas here have to live outside `Case2Seven.lean` because the two `SevenX` modules
import it (they use `card_K0_sup_F` and `K0_inf_F_eq_bot`).
-/

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-- **Unconditional form of `conj2_iff_piF`**, using the `X`-argument
`Work.CORE4.SevenX.piFU_le_pi_K0F` (`π(F(U)) ⊆ π(K₀F)`): the second conjunct of
`Case2SevenFacts` is *equivalent* to `π(F) ⊆ π(K₀)`, with no extra hypothesis. -/
theorem conj2_iff_piF_uncond (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D)
    (h2 : Work.GW2.Case2 B) :
    (primesOf D.K0 = B.piFU) ↔ primesOf D.F ⊆ primesOf D.K0 := by
  have hsplit : primesOf (D.K0 ⊔ D.F) = primesOf D.K0 ∪ primesOf D.F :=
    primesOf_sup_of_card _ _ (card_K0_sup_F I hbc B D hpre)
  have hK0le : primesOf D.K0 ⊆ B.piFU := by
    show primesOf D.K0 ⊆ primesOf (Work.GW2.fittingIn B.U)
    exact Nat.primeFactors_mono
      (Subgroup.card_dvd_of_le (inf_le_left : D.K0 ≤ Work.GW2.fittingIn B.U))
      (show Nat.card ↥(Work.GW2.fittingIn B.U) ≠ 0 from Nat.card_pos.ne')
  constructor
  · intro h p hp
    have hpFU : p ∈ B.piFU := by
      show p ∈ primesOf (Work.GW2.fittingIn B.U)
      exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le (D.F_le_fitting B))
        (show Nat.card ↥(Work.GW2.fittingIn B.U) ≠ 0 from Nat.card_pos.ne') hp
    rw [← h] at hpFU
    exact hpFU
  · intro h
    refine le_antisymm hK0le ?_
    intro p hpFU
    have hp' : p ∈ primesOf (D.K0 ⊔ D.F) :=
      Work.CORE4.SevenX.piFU_le_pi_K0F I G hbc B h2 D hpre hpFU
    rw [hsplit] at hp'
    rcases hp' with h1 | h1
    · exact h1
    · exact h h1

/-- Consequently (and unconditionally): if `K₀ = ⊥`, the leaf's second conjunct **fails**.
This is the machine-checked statement that the leaf needs a hypothesis forcing `K₀ ≠ ⊥`. -/
theorem conj2_fails_of_K0_eq_bot_uncond (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D)
    (h2 : Work.GW2.Case2 B) (hbot : D.K0 = ⊥) :
    primesOf D.K0 ≠ B.piFU := by
  intro h
  have hle : primesOf D.F ⊆ primesOf D.K0 :=
    (conj2_iff_piF_uncond I hbc B D hpre h2).mp h
  have hF1 : Nat.card ↥D.F = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpF : p ∈ primesOf D.F := by
      rw [primesOf]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.card_pos.ne'⟩
    have hpk : p ∈ primesOf D.K0 := hle hpF
    rw [hbot] at hpk
    rw [primesOf, (Subgroup.card_eq_one (H := (⊥ : Subgroup G))).mpr rfl,
      Nat.primeFactors_one] at hpk
    exact absurd hpk (by simp)
  exact Case2Pre.F_ne B D hpre ((Subgroup.card_eq_one (H := D.F)).mp hF1)


end Work.CORE4
