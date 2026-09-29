import Mathlib
import Submission.Work.IntLib.evCA.Defs
import Submission.Work.IntLib.evCA.readAEv
import Submission.Work.IntLib.evCA.flagAEv

/-!
# `IntLib` / `evCarryAddAny`: the setup phase

`evCASetupEv` runs the setup phase `progSetup` of the `evCarryAddAny` word (`readA`: move the
reversed value encoding of `h` from `aA` to `aB`; `flagA`: compute the initial loop flag; `set rKa`:
clear the carry).  It establishes the loop invariant `EvC.addP b W h.bits LO X' ... 0`, where
`X'` is the state function that has the marker `gmk aA` on `aA` (the digit's encoding having been
consumed).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

theorem evCASetupEv (main : HvdH.Cmd) (h b : ℕ) (W LO : List Bool) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph) (As Ws Os Cs A2s Bs : List HvdH.Glyph)
    (hA : X aA = (Val.enc (.int (h : ℤ))).reverse ++ Shift.gmk aA :: As)
    (hW : X aW = W.map Glyph.bit ++ Shift.gmk aW :: Ws)
    (hO : X aO = LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os)
    (hC : X aCW = Unary b (Shift.gmk aCW :: Cs))
    (hB : X aB = Shift.gmk aB :: Bs)
    (h2 : X a2 = Shift.gmk a2 :: A2s) :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main EvCA.progSetup ⟨g, X⟩ s' n ∧
      n ≤ 5 * (h.size + 3) + 14 ∧
      EvC.addP b W h.bits LO (EvCA.XA X As) Ws Os Cs A2s Bs 0 s' ∧
      s'.stk aA = Shift.gmk aA :: As ∧
      (∀ j : Stk, j ≠ aA → j ≠ aW → j ≠ aB → j ≠ aO → j ≠ a2 → j ≠ aCW → s'.stk j = X j) := by
  obtain ⟨s1, m1, hev1, hm1, hA1, hB1, hfr1⟩ := evCA.readAEv main g X h As Bs hA hB
  have hstr1 : EvC.strP W h.bits Ws Bs 0 s1 := by
    refine ⟨?_, ?_⟩
    · show s1.stk aW = (W.drop 0).map Glyph.bit ++ Shift.gmk aW :: Ws
      rw [hfr1 aW (by decide) (by decide), hW]
      simp
    · show s1.stk aB = (h.bits.drop 0).map Glyph.bit ++ Glyph.iend :: Shift.gmk aB :: Bs
      rw [hB1]
      simp
  obtain ⟨s2, m2, hev2, hm2, hLa2, hfr2⟩ :=
    evCA.flagAEv main W h.bits Ws Bs 0 s1 hstr1 (Nat.zero_le _)
  have hev3 : Work.Layout.Ev main (.set EvC.rKa (Glyph.bit false)) s2
      ⟨Function.update s2.reg EvC.rKa (Glyph.bit false), s2.stk⟩ 1 :=
    Work.Layout.ev_set' main EvC.rKa (Glyph.bit false) s2.reg s2.stk
  have hev : Work.Layout.Ev main EvCA.progSetup ⟨g, X⟩
      ⟨Function.update s2.reg EvC.rKa (Glyph.bit false), s2.stk⟩ (m1 + (m2 + 1)) :=
    Work.Layout.Ev.seqs_cons hev1 (Work.Layout.Ev.seqs_cons hev2 hev3)
  refine ⟨⟨Function.update s2.reg EvC.rKa (Glyph.bit false), s2.stk⟩, m1 + (m2 + 1), hev, ?_,
    ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · omega
  · show s2.stk aW = (W.drop 0).map Glyph.bit ++ Shift.gmk aW :: Ws
    rw [hfr2 aW, hfr1 aW (by decide) (by decide), hW]
    simp
  · show s2.stk aB = (h.bits.drop 0).map Glyph.bit ++ Glyph.iend :: Shift.gmk aB :: Bs
    rw [hfr2 aB, hB1]
    simp
  · show s2.stk aO = ((EvC.accF W h.bits false 0).take b).reverse.map Glyph.bit ++
      LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os
    rw [hfr2 aO, hfr1 aO (by decide) (by decide), hO, EvC.accF_zero]
    simp
  · show s2.stk a2 = ((EvC.accF W h.bits false 0).drop b).reverse.map Glyph.bit ++
      Shift.gmk a2 :: A2s
    rw [hfr2 a2, hfr1 a2 (by decide) (by decide), h2, EvC.accF_zero]
    simp
  · show s2.stk aCW = Unary (b - 0) (Shift.gmk aCW :: Cs)
    rw [hfr2 aCW, hfr1 aCW (by decide) (by decide), hC]
    simp
  · intro j hjW hjB hjO hj2 hjC
    rw [hfr2 j]
    by_cases hja : j = aA
    · subst hja
      rw [hA1, EvCA.XA_self]
    · rw [hfr1 j hja hjB, EvCA.XA_ne X As hja]
  · show (Function.update s2.reg EvC.rKa (Glyph.bit false)) EvC.rKa =
      Glyph.bit (EvC.carryC W h.bits false 0)
    rw [Function.update_self, EvC.carryC_zero]
  · show (Function.update s2.reg EvC.rKa (Glyph.bit false)) EvC.rLa = EvC.addFlag W h.bits 0
    rw [Function.update_of_ne (by decide : EvC.rLa ≠ EvC.rKa)]
    exact hLa2
  · show s2.stk aA = Shift.gmk aA :: As
    rw [hfr2 aA, hA1]
  · intro j hjA hjW hjB hjO hj2 hjC
    rw [hfr2 j, hfr1 j hjA hjB]

end Work.IntLib
