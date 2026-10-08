import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.glaubValue
import Submission.Work.BG.CharBridge
import Submission.Work.GLUE.Defs
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.hatInjCore
import Submission.Work.BG.hatInjCountAlt
import Submission.Work.BG.hatInjParity
import Submission.Work.BG.hatInjRestrictIrr
import Submission.Work.BG.hatInjRestrictSigma
import Submission.Work.BG.hatInjRestrictInj
import Submission.Work.BG.hatInjBIdent

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem hatInj {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) :
    Work.GW2.C23.HatInjProp D C := by
  classical
  intro hc hn ν hν μ hμ θ hθν hθμ
  -- `ν|_U` and `μ|_U` are irreducible, `σ`-invariant characters of `U`
  have hαirr : IsIrreducibleCharacter (restrictU C ν) := hatInjRestrictIrr (D := D) C hc hn hν
  have hαinv : ∀ u : ↥C.P.U, restrictU C ν (sigmaU C u) = restrictU C ν u :=
    hatInjRestrictSigma (D := D) C hc hn hν
  have hα'irr : IsIrreducibleCharacter (restrictU C μ) := hatInjRestrictIrr (D := D) C hc hn hμ
  have hα'inv : ∀ u : ↥C.P.U, restrictU C μ (sigmaU C u) = restrictU C μ u :=
    hatInjRestrictSigma (D := D) C hc hn hμ
  -- they agree modulo `2` on the fixed subgroup `C_U(σ) ≤ B`
  have hcong : ∀ c : ↥(fixedSubgroup (sigmaU C)),
      AlgIntModTwo (restrictU C ν c) (restrictU C μ c) := by
    intro c
    have hB : (((c : ↥(fixedSubgroup (sigmaU C))) : ↥C.P.U) : G) ∈ D.B :=
      hatInjBIdent (D := D) C hc hn (c : ↥C.P.U) c.2
    have h1 := hθν.2 (⟨(((c : ↥(fixedSubgroup (sigmaU C))) : ↥C.P.U) : G), C.P.U_le_H0 c.1.2⟩ :
      ↥C.P.H0) hB
    have h2 := hθμ.2 (⟨(((c : ↥(fixedSubgroup (sigmaU C))) : ↥C.P.U) : G), C.P.U_le_H0 c.1.2⟩ :
      ↥C.P.H0) hB
    rw [restrictU_apply, restrictU_apply]
    exact h1.trans h2.symm
  -- the abstract core
  have hcount : Nat.card (SigmaInvIrr ↥C.P.U (sigmaU C))
      = Nat.card (IrreducibleCharacter ↥(fixedSubgroup (sigmaU C))) :=
    hatInjCountAlt (odd_card_U_of_compat hc) (sigmaU C) (sigmaU_mul_self C)
  have hparity : ∀ β : IrreducibleCharacter ↥(fixedSubgroup (sigmaU C)),
      Odd (Nat.card {α : SigmaInvIrr ↥C.P.U (sigmaU C) //
        OddMult (sigmaU C) (α : IrreducibleCharacter ↥C.P.U) β}) :=
    fun β => hatInjParity (odd_card_U_of_compat hc) (sigmaU C) (sigmaU_mul_self C) β
  have hres : restrictU C ν = restrictU C μ :=
    glauberman_injective (odd_card_U_of_compat hc) (sigmaU C) (sigmaU_mul_self C)
      hcount hparity hαirr hαinv hα'irr hα'inv hcong
  exact hatInjRestrictInj (D := D) C hc hn hν hμ hres

end Work.BG
