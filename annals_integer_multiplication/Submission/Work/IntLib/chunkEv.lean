import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.evReadValue
import Submission.Work.IntLib.evChainMove
import Submission.Work.IntLib.evZeroChain
import Submission.Work.IntLib.evEmit
import Submission.Work.IntLib.evMainLoop
import Submission.Work.IntLib.evPrologue
import Submission.Work.IntLib.evEpilogue
import Submission.Work.IntLib.evalChunksArith
import Submission.Work.IntLib.unaryCopyGen
import Submission.Work.IntLib.evCarryAddAny
import Submission.Work.IntLib.evArith
import Submission.Work.IntLib.evArithNil
import Submission.Work.IntLib.evArithNeAlt
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base

/-!
# Assembly of the `evalPoly` word

`chunkWord_poly` is the second conjunct of `Work.IntLib.chunkWord`: the program
`seqs [peek aC rX, ite rX nil zeroProg (seqs [prologue, loop, epilogue])]` maps the stack
`intList hs :: int b :: rest` to `int (evalChunks hs b) :: rest` in
`O(Σ isz h + hs.length*(b+1) + isz b + 1)` steps.

The cost bookkeeping is split off into `evArithNe` / `evArithNil` (pure arithmetic about
`polyBudget` and `polyK`); here only the three phase costs are substituted into them.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.IntLib

open HvdH
open Work.Layout

/-- `encs` of a cons cell. -/
theorem encs_cons_poly (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := by
  simp [encs]

theorem evVal_zero (hs : List ℕ) (b : ℕ) :
    Work.IntLib.evVal hs b 0 ([] : List Bool) ([] : List Bool) := by
  refine ⟨by simp, by simp, ?_⟩
  simp [HvdH.evalChunks, Work.IntLib.ofBits]

theorem chunkWord_poly : ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (hs : List ℕ) (b : ℕ),
    1 ≤ b → (∀ h ∈ hs, h < 2 ^ (3 * b)) →
    HvdH.WordR main p (fun vs => ∃ rest, vs = HvdH.intList hs :: .int b :: rest)
      (fun vs out => ∃ rest, vs = HvdH.intList hs :: .int b :: rest ∧
        out = .int (HvdH.evalChunks hs b) :: rest)
      (fun _ => K * ((hs.map fun h => HvdH.isz (h : ℤ)).sum + hs.length * (b + 1) +
        HvdH.isz (b : ℤ) + 1)) := by
  obtain ⟨readGadA, KR, hreadA⟩ := evReadValue aA (by decide)
  obtain ⟨readGadL, KRL, hreadL⟩ := evReadValue aL (by decide)
  obtain ⟨chainProg, KCM, hchain⟩ := evChainMove aL (by decide) readGadL KRL hreadL
  obtain ⟨readGadR, KRR, hreadR⟩ := evReadValue aR (by decide)
  obtain ⟨addProg, KA, hadd⟩ := evCarryAddAny
  obtain ⟨copyProg, KC, hcopy⟩ := unaryCopyGen aCB aCW (by decide)
  obtain ⟨zeroProg, KZ, hzero⟩ := evZeroChain
  obtain ⟨emitProg, KE, hem⟩ := evEmit
  obtain ⟨prolProg, KP, hprol⟩ := evPrologue chainProg readGadR KCM KRR hchain hreadR
  obtain ⟨epiProg, KEP, hepi⟩ := evEpilogue emitProg KE hem
  -- the two read gadgets (for `aA` and for `aR`) have their own constants; the final constant is
  -- chosen with `KR + KRR`, which dominates both.
  refine ⟨seqs [.peek aC rX, .ite rX Glyph.nil zeroProg
      (seqs [prolProg, evLoopP readGadA copyProg addProg, epiProg])],
    polyK KP KCM (KR + KRR) KEP KE KC KA KZ, ?_⟩
  intro main hs b hb hh vs hPre s R hstk0
  obtain ⟨rest, rfl⟩ := hPre
  set Y : Stk → List Glyph := Function.update s.stk 0 (encs rest ++ R) with hY
  have hY0 : Y 0 = encs rest ++ R := by rw [hY]; exact Function.update_self ..
  have hYne : ∀ k : Stk, k ≠ 0 → Y k = s.stk k := by
    intro k hk; rw [hY]; exact Function.update_of_ne hk _ _
  have hs0 : s.stk 0 = Val.enc (intList hs) ++ Val.enc (.int (b : ℤ)) ++ Y 0 := by
    rw [hstk0, hY0]
    simp [encs, List.append_assoc]
  -- the branch test
  set sP : State := ⟨Function.update s.reg rX ((s.stk 0).headD Glyph.eos), s.stk⟩ with hsPdef
  have hevP : Ev main (.peek aC rX) s sP 1 := by
    rw [hsPdef]; exact ev_peek' main aC rX s.reg s.stk
  have hsPstk : sP.stk = s.stk := by rw [hsPdef]
  have hsPreg : sP.reg rX = (s.stk 0).headD Glyph.eos := by
    rw [hsPdef]
    show Function.update s.reg rX ((s.stk 0).headD Glyph.eos) rX = (s.stk 0).headD Glyph.eos
    exact Function.update_self ..
  by_cases hne : hs = []
  · -- ################ the empty chain ################
    subst hne
    have hhead : (s.stk 0).headD Glyph.eos = Glyph.nil := by
      rw [hs0]
      rfl
    have hreg : sP.reg rX = Glyph.nil := by rw [hsPreg]; exact hhead
    have hzin : sP.stk 0 = [Glyph.nil] ++ Val.enc (.int (b : ℤ)) ++ (encs rest ++ R) := by
      rw [hsPstk, hs0, hY0]
      simp [intList, ofList, Val.enc, List.append_assoc]
    obtain ⟨s1, n1, hev1, hn1, hstk1, hfr1⟩ :=
      hzero main sP.reg sP.stk b (encs rest ++ R) hzin
    have hevITE : Ev main (.ite rX Glyph.nil zeroProg
        (seqs [prolProg, evLoopP readGadA copyProg addProg, epiProg])) sP s1 (n1 + 1) :=
      Ev.iteT hreg hev1
    have e_all : Ev main (seqs [.peek aC rX, .ite rX Glyph.nil zeroProg
        (seqs [prolProg, evLoopP readGadA copyProg addProg, epiProg])]) s s1 (1 + (n1 + 1)) :=
      Ev.seqs_cons hevP hevITE
    obtain ⟨n, heval, hn⟩ := e_all
    have hz : HvdH.evalChunks ([] : List ℕ) b = 0 := by simp [HvdH.evalChunks]
    refine ⟨.int (HvdH.evalChunks [] b) :: rest, s1, n, ⟨rest, rfl, rfl⟩, heval, ?_, ?_, ?_⟩
    · -- cost
      have hn' : n ≤ n1 + 2 := by omega
      have haz : n1 + 2 ≤ polyK KP KCM (KR + KRR) KEP KE KC KA KZ * polyBudget ([] : List ℕ) b :=
        evArithNil KP KCM (KR + KRR) KEP KE KC KA KZ n1 b hn1
      exact le_trans hn' haz
    · -- stack 0
      rw [hstk1, hz]
      simp [encs_cons_poly, List.append_assoc]
    · -- frame
      intro k hk
      rw [hfr1 k hk, hsPstk]
  · -- ################ the non-empty chain ################
    have hex : ∃ a t, hs = a :: t := by
      cases hs with
      | nil => exact absurd rfl hne
      | cons a t => exact ⟨a, t, rfl⟩
    obtain ⟨a, t, rfl⟩ := hex
    have hhead : (s.stk 0).headD Glyph.eos = Glyph.cons := by
      rw [hs0]
      rfl
    have hreg : sP.reg rX ≠ Glyph.nil := by
      rw [hsPreg, hhead]
      exact fun hc => by cases hc
    have hXk : ∀ k : Stk, k ≠ 0 → sP.stk k = Y k := by
      intro k hk; rw [hsPstk, ← hYne k hk]
    have hpin : sP.stk 0 = Val.enc (intList (a :: t)) ++ Val.enc (.int (b : ℤ)) ++ Y 0 := by
      rw [hsPstk]; exact hs0
    -- phase 1: the prologue
    obtain ⟨s1, n1, hev1, hn1, hs1⟩ := hprol main sP.reg sP.stk b (a :: t) hne Y hpin hXk
    -- phase 2: the main loop
    obtain ⟨s2, n2, hev2, hn2, W', LO', hs2, hinv2⟩ :=
      evMainLoop main readGadA copyProg addProg KR KC KA b hb (a :: t) hne hh
        (hreadA main) (hcopy main) (hadd b main) Y [] [] s1.reg (evVal_zero (a :: t) b)
    have hev2' : Ev main (evLoopP readGadA copyProg addProg) s1 s2 n2 := hs1.symm ▸ hev2
    -- phase 3: the epilogue
    obtain ⟨s3, n3, hev3, hn3, hstk3, hfr3⟩ :=
      hepi main s2.reg W' LO' b (a :: t) Y hinv2
    have hev3' : Ev main epiProg s2 s3 n3 := hs2.symm ▸ hev3
    -- assemble the program
    have hinner : Ev main (seqs [prolProg, evLoopP readGadA copyProg addProg, epiProg])
        sP s3 (n1 + (n2 + n3)) :=
      Ev.seqs_cons hev1 (Ev.seqs_cons hev2' hev3')
    have hevITE : Ev main (.ite rX Glyph.nil zeroProg
        (seqs [prolProg, evLoopP readGadA copyProg addProg, epiProg])) sP s3
        (n1 + n2 + n3 + 1) :=
      Ev.mono (Ev.iteF hreg hinner) (by omega)
    have e_all : Ev main (seqs [.peek aC rX, .ite rX Glyph.nil zeroProg
        (seqs [prolProg, evLoopP readGadA copyProg addProg, epiProg])]) s s3
        (1 + (n1 + n2 + n3 + 1)) :=
      Ev.seqs_cons hevP hevITE
    obtain ⟨n, heval, hn⟩ := e_all
    refine ⟨.int (HvdH.evalChunks (a :: t) b) :: rest, s3, n, ⟨rest, rfl, rfl⟩, heval, ?_, ?_, ?_⟩
    · -- cost
      obtain ⟨hLOlen, hWlen, -⟩ := hinv2
      have hn' : n ≤ n1 + n2 + n3 + 2 := by omega
      have hLO' : LO'.length ≤ (a :: t).length * (b + 1) := by
        rw [hLOlen]
        calc b * (a :: t).length = (a :: t).length * b := Nat.mul_comm _ _
          _ ≤ (a :: t).length * (b + 1) := Nat.mul_le_mul_left _ (by omega)
      have hc1 : KCM + KRR + 1 ≤ KCM + (KR + KRR) + 1 := by omega
      have hc2 : 10 * KR + 10 * KC + 40 * KA + 50
          ≤ 10 * (KR + KRR) + 10 * KC + 40 * KA + 50 := by omega
      have hw1 : n1 ≤ KP * (KCM + (KR + KRR) + 1) *
          (((a :: t).map fun h => h.size).sum + (a :: t).length * (b + 2) + HvdH.isz (b : ℤ) + 100) :=
        le_trans hn1 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left KP hc1))
      have hw2 : n2 ≤ (10 * (KR + KRR) + 10 * KC + 40 * KA + 50) *
          (((a :: t).map fun h => h.size).sum + (a :: t).length * (b + 2) + 1) :=
        le_trans hn2 (Nat.mul_le_mul_right _ hc2)
      have haz : n1 + n2 + n3 + 2
          ≤ polyK KP KCM (KR + KRR) KEP KE KC KA KZ * polyBudget (a :: t) b :=
        evArithNeAlt KP KCM (KR + KRR) KEP KE KC KA KZ (a :: t) b W'.length LO'.length
          n1 n2 n3 hne hWlen hLO' hw1 hw2 hn3
      exact le_trans hn' haz
    · -- stack 0
      rw [hstk3, hY0]
      simp [encs_cons_poly, List.append_assoc]
    · -- frame
      intro k hk
      rw [hfr3 k hk, hYne k hk]

end Work.IntLib
