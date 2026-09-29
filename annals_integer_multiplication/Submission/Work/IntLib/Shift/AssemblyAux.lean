import Mathlib
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Shift.Loop
import Submission.Work.IntLib.Shift.incRgn_ev

/-!
# `IntLib` / shift words: auxiliary evaluations for the final value-level assembly

The three `WordR` specifications of `shlProg`, `shrTProg`, `shrFProg` (see `Assembly.lean`) need two
extra evaluations which are *not* part of the main loops:

* `finishShl` / `finishShr` in their *empty magnitude* branch (`sM` holds only its frame marker):
  the answer is `.int 0`;
* `incIf`: the conditional magnitude increment used by `shrF` to turn the truncated quotient
  `|a| / 2^k` into the ceiling `⌈|a|/2^k⌉`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH

/-! ## The common prefix of `finishShl` and `finishShr` -/

/-- The common prefix of `finishShl` and `finishShr`: read the region of `sM`, and if it is empty
push `pos :: [iend]` (the encoding of `.int 0`), in cost `6`.  The `else` branch is abstracted
over, so that both `finishShl` and `finishShr` are instances. -/
theorem finishThen_ev (main : Cmd) (s : State) (br : Cmd) (T0 Rj JM : List Glyph)
    (hM : s.stk sM = gmk sM :: JM) (h0 : s.stk 0 = T0 ++ Rj) :
    ∃ (s' : State) (n : ℕ),
      Eval main (.seq (.peek sM rY)
        (.ite rY (gmk sM) (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY]) br)) s s' n ∧
      n ≤ 6 ∧ s'.stk 0 = (Glyph.pos :: [Glyph.iend]) ++ T0 ++ Rj ∧
      (∀ j : Stk, j ≠ 0 → s'.stk j = s.stk j) := by
  have hhead : (s.stk sM).headD .eos = gmk sM := by rw [hM]; rfl
  have hpeek : Ev main (.peek sM rY) s ⟨Function.update s.reg rY (gmk sM), s.stk⟩ 1 := by
    have h := ev_peek_st main sM rY s
    rwa [hhead] at h
  have hreg : (⟨Function.update s.reg rY (gmk sM), s.stk⟩ : State).reg rY = gmk sM :=
    Function.update_self rY _ s.reg
  have hp1 : Ev main (pushC 0 Glyph.iend rY) ⟨Function.update s.reg rY (gmk sM), s.stk⟩
      ⟨Function.update (Function.update s.reg rY (gmk sM)) rY Glyph.iend,
        Function.update s.stk 0 (Glyph.iend :: s.stk 0)⟩ 2 :=
    ev_pushC main 0 Glyph.iend rY _ _
  have hp2 : Ev main (pushC 0 Glyph.pos rY)
      ⟨Function.update (Function.update s.reg rY (gmk sM)) rY Glyph.iend,
        Function.update s.stk 0 (Glyph.iend :: s.stk 0)⟩
      ⟨Function.update (Function.update (Function.update s.reg rY (gmk sM)) rY Glyph.iend) rY Glyph.pos,
        Function.update (Function.update s.stk 0 (Glyph.iend :: s.stk 0)) 0
          (Glyph.pos :: Glyph.iend :: s.stk 0)⟩ 2 :=
    ev_pushC main 0 Glyph.pos rY _ _
  have hbr : Ev main (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY])
      ⟨Function.update s.reg rY (gmk sM), s.stk⟩
      ⟨Function.update (Function.update (Function.update s.reg rY (gmk sM)) rY Glyph.iend) rY Glyph.pos,
        Function.update (Function.update s.stk 0 (Glyph.iend :: s.stk 0)) 0
          (Glyph.pos :: Glyph.iend :: s.stk 0)⟩ 4 := by
    rw [seqs_pair]
    exact Ev.seq' hp1 hp2 (by omega)
  have hite : Ev main (.ite rY (gmk sM)
      (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY]) br)
      ⟨Function.update s.reg rY (gmk sM), s.stk⟩
      ⟨Function.update (Function.update (Function.update s.reg rY (gmk sM)) rY Glyph.iend) rY Glyph.pos,
        Function.update (Function.update s.stk 0 (Glyph.iend :: s.stk 0)) 0
          (Glyph.pos :: Glyph.iend :: s.stk 0)⟩ 5 :=
    Ev.iteT hreg hbr
  have hbody : Ev main (seqs [.peek sM rY,
      .ite rY (gmk sM) (seqs [pushC 0 Glyph.iend rY, pushC 0 Glyph.pos rY]) br]) s
      ⟨Function.update (Function.update (Function.update s.reg rY (gmk sM)) rY Glyph.iend) rY Glyph.pos,
        Function.update (Function.update s.stk 0 (Glyph.iend :: s.stk 0)) 0
          (Glyph.pos :: Glyph.iend :: s.stk 0)⟩ 6 := by
    rw [seqs_pair]
    exact Ev.seq' hpeek hite (by omega)
  obtain ⟨n, he, hn⟩ := hbody
  refine ⟨_, n, he, by omega, ?_, ?_⟩
  · show (Function.update (Function.update s.stk 0 (Glyph.iend :: s.stk 0)) 0
        (Glyph.pos :: Glyph.iend :: s.stk 0)) 0 = _
    rw [Function.update_self, h0]
    rfl
  · intro j hj
    show (Function.update (Function.update s.stk 0 (Glyph.iend :: s.stk 0)) 0
        (Glyph.pos :: Glyph.iend :: s.stk 0)) j = s.stk j
    rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- `finishShl` on the empty magnitude region: the answer is `.int 0`. -/
theorem finishShl_zero_ev (main : Cmd) (s : State) (T0 Rj JM : List Glyph)
    (hM : s.stk sM = gmk sM :: JM) (h0 : s.stk 0 = T0 ++ Rj) :
    ∃ (s' : State) (n : ℕ), Eval main finishShl s s' n ∧ n ≤ 6 ∧
      s'.stk 0 = (Glyph.pos :: [Glyph.iend]) ++ T0 ++ Rj ∧
      (∀ j : Stk, j ≠ 0 → s'.stk j = s.stk j) := by
  obtain ⟨s', n, he, hn, h0', hfr⟩ :=
    finishThen_ev main s
      (seqs [pushC 0 Glyph.iend rY, drain sM sT (gmk sM) rZ rJ, drain sT 0 (gmk sT) rZ rJ,
        drain sA 0 (gmk sA) rZ rJ, .pop sSg rY, .push 0 rY]) T0 Rj JM hM h0
  exact ⟨s', n, he, by omega, h0', hfr⟩

/-- `finishShr` on the empty magnitude region: the answer is `.int 0`. -/
theorem finishShr_zero_ev (main : Cmd) (s : State) (T0 Rj JM : List Glyph)
    (hM : s.stk sM = gmk sM :: JM) (h0 : s.stk 0 = T0 ++ Rj) :
    ∃ (s' : State) (n : ℕ), Eval main finishShr s s' n ∧ n ≤ 6 ∧
      s'.stk 0 = (Glyph.pos :: [Glyph.iend]) ++ T0 ++ Rj ∧
      (∀ j : Stk, j ≠ 0 → s'.stk j = s.stk j) := by
  obtain ⟨s', n, he, hn, h0', hfr⟩ :=
    finishThen_ev main s
      (seqs [pushC 0 Glyph.iend rY, drain sM sT (gmk sM) rZ rJ, drain sT 0 (gmk sT) rZ rJ,
        .pop sSg rY, .push 0 rY]) T0 Rj JM hM h0
  exact ⟨s', n, he, by omega, h0', hfr⟩

/-! ## `incIf` -/

/-- `incIf`: increment the magnitude region of `sM` iff the sign glyph of `a` is `neg` and some
dropped bit was `true`. -/
theorem incIf_ev (main : Cmd) (s : State) (Bs : List Bool) (JM JT : List Glyph)
    (hM : s.stk sM = Bs.map Glyph.bit ++ gmk sM :: JM)
    (hT : s.stk sT = gmk sT :: JT) :
    ∃ (s' : State) (n : ℕ), Eval main incIf s s' n ∧ n ≤ 12 * (Bs.length + 1) + 34 ∧
      s'.stk sM = (if (s.stk sSg).headD .eos = Glyph.neg ∧ s.reg rD = gAny then
          incList Bs else Bs).map Glyph.bit ++ gmk sM :: JM ∧
      s'.stk sT = gmk sT :: JT ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT → s'.stk j = s.stk j) := by
  have hskip : ∀ (u : State), Ev main (.skip : Cmd) u u 1 := fun u => ⟨1, Eval.skip u, le_rfl⟩
  by_cases hc : ((s.stk sSg).headD .eos = Glyph.neg ∧ s.reg rD = gAny)
  · obtain ⟨hSg, hDr⟩ := hc
    have hpeek : Ev main (.peek sSg rX) s ⟨Function.update s.reg rX Glyph.neg, s.stk⟩ 1 := by
      have h := ev_peek_st main sSg rX s
      rwa [hSg] at h
    have hreg : (⟨Function.update s.reg rX Glyph.neg, s.stk⟩ : State).reg rX = Glyph.neg :=
      Function.update_self rX _ s.reg
    have hregD : (⟨Function.update s.reg rX Glyph.neg, s.stk⟩ : State).reg rD = gAny := by
      show Function.update s.reg rX Glyph.neg rD = gAny
      rw [Function.update_of_ne (by decide : rD ≠ rX)]
      exact hDr
    obtain ⟨s2, n2, he2, hn2, hM2, hT2, _, hfr2⟩ :=
      incRgn_ev main Bs JM JT ⟨Function.update s.reg rX Glyph.neg, s.stk⟩ hM hT
    have hite2 : Ev main (.ite rD gAny incRgn .skip)
        ⟨Function.update s.reg rX Glyph.neg, s.stk⟩ s2 (n2 + 1) :=
      Ev.iteT hregD ⟨n2, he2, le_rfl⟩
    have hite1 : Ev main (.ite rX Glyph.neg (.ite rD gAny incRgn .skip) .skip)
        ⟨Function.update s.reg rX Glyph.neg, s.stk⟩ s2 (n2 + 2) :=
      Ev.iteT hreg hite2
    have hbody : Ev main incIf s s2 (n2 + 3) := by
      rw [incIf, seqs_pair]
      exact Ev.seq' hpeek hite1 (by omega)
    obtain ⟨n, he, hn⟩ := hbody
    refine ⟨s2, n, he, by omega, ?_, ?_, ?_⟩
    · rw [if_pos ⟨hSg, hDr⟩]; exact hM2
    · exact hT2
    · intro j hj1 hj2; exact hfr2 j hj1 hj2
  · have hpeek : Ev main (.peek sSg rX) s
        ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ 1 :=
      ev_peek_st main sSg rX s
    by_cases hSg : (s.stk sSg).headD .eos = Glyph.neg
    · -- the sign matches but no bit was dropped: the increment is skipped
      have hne : ¬ ((s.stk sSg).headD .eos = Glyph.neg ∧ s.reg rD = gAny) := fun h => hc ⟨hSg, h.2⟩
      have hreg : (⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ : State).reg rX
          = Glyph.neg := by
        show Function.update s.reg rX ((s.stk sSg).headD .eos) rX = Glyph.neg
        rw [Function.update_self]
        exact hSg
      have hneD : (⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ : State).reg rD
          ≠ gAny := by
        show Function.update s.reg rX ((s.stk sSg).headD .eos) rD ≠ gAny
        rw [Function.update_of_ne (by decide : rD ≠ rX)]
        intro h
        exact hc ⟨hSg, h⟩
      have hite2 : Ev main (.ite rD gAny incRgn .skip)
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ 2 :=
        Ev.iteF hneD (hskip _)
      have hite1 : Ev main (.ite rX Glyph.neg (.ite rD gAny incRgn .skip) .skip)
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ 3 :=
        Ev.iteT hreg hite2
      have hbody : Ev main incIf s
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ 4 := by
        rw [incIf, seqs_pair]
        exact Ev.seq' hpeek hite1 (by omega)
      obtain ⟨n, he, hn⟩ := hbody
      refine ⟨_, n, he, by omega, ?_, ?_, ?_⟩
      · rw [if_neg hne]
        show s.stk sM = Bs.map Glyph.bit ++ gmk sM :: JM
        exact hM
      · show s.stk sT = gmk sT :: JT
        exact hT
      · intro j hj1 hj2; rfl
    · -- the sign does not match: the whole increment is skipped
      have hne : ¬ ((s.stk sSg).headD .eos = Glyph.neg ∧ s.reg rD = gAny) := fun h => hSg h.1
      have hne0 : (⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ : State).reg rX
          ≠ Glyph.neg := by
        show Function.update s.reg rX ((s.stk sSg).headD .eos) rX ≠ Glyph.neg
        rw [Function.update_self]
        exact hSg
      have hite1 : Ev main (.ite rX Glyph.neg (.ite rD gAny incRgn .skip) .skip)
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ 2 :=
        Ev.iteF hne0 (hskip _)
      have hbody : Ev main incIf s
          ⟨Function.update s.reg rX ((s.stk sSg).headD .eos), s.stk⟩ 3 := by
        rw [incIf, seqs_pair]
        exact Ev.seq' hpeek hite1 (by omega)
      obtain ⟨n, he, hn⟩ := hbody
      refine ⟨_, n, he, by omega, ?_, ?_, ?_⟩
      · rw [if_neg hne]
        show s.stk sM = Bs.map Glyph.bit ++ gmk sM :: JM
        exact hM
      · show s.stk sT = gmk sT :: JT
        exact hT
      · intro j hj1 hj2; rfl

end Shift
end Work.IntLib
