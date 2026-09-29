import Mathlib
import Submission.Work.IntLib.evCarryDefs

/-!
# `IntLib` / `evCarryAdd`: the loop-flag phase `EvC.flagA`

`EvC.flagA` is the third part of one iteration of the ripple-addition loop:

* peek the window stack `aW`; if it only carries its frame marker `Shift.gmk aW` (the window is
  exhausted), peek the digit stack `aB`; if that carries the `iend` terminator (the digit is
  exhausted too) set the loop flag `rLa` to `Shift.gStop`, else to `Shift.gGo`;
* otherwise (a window bit is still present) set `Shift.gGo`.

Hence, whenever the two bit streams of the addition are at position `k`
(`EvC.strP W hbits Ws Bs k s`), `flagA` leaves the stacks untouched and sets
`rLa = EvC.addFlag W hbits k ≤ 5` steps.

The proof factors through the general evaluation lemma `flagAGen` (which computes the resulting
register value as a function of the two stack heads) and the purely list-theoretic lemma
`flagAVal_eq` (which identifies that function with `EvC.addFlag` under `strP`).
-/

namespace Work.IntLib.evCA

open HvdH

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The inner block of `flagA` -/

/-- The inner block `peek aB rTa; if rTa = iend then set rLa gStop else set rLa gGo`, when the
digit stack `aB` is exhausted. -/
theorem flagInnerEv_stop (main : Cmd) (s : State)
    (h : (s.stk Work.IntLib.aB).headD Glyph.eos = Glyph.iend) :
    ∃ (s' : State) (n : ℕ),
      Work.Layout.Ev main (Cmd.seq (Cmd.peek Work.IntLib.aB EvC.rTa)
          (Cmd.ite EvC.rTa Glyph.iend (Cmd.set EvC.rLa Shift.gStop) (Cmd.set EvC.rLa Shift.gGo)))
        s s' n ∧
      n ≤ 3 ∧ s'.reg EvC.rLa = Shift.gStop ∧ (∀ j : Stk, s'.stk j = s.stk j) := by
  refine ⟨⟨Function.update (Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aB).headD Glyph.eos))
      EvC.rLa Shift.gStop, s.stk⟩, 3, ?_, by norm_num, ?_, fun j => rfl⟩
  · exact Work.Layout.Ev.seq (Work.Layout.ev_peek main Work.IntLib.aB EvC.rTa s)
      (Work.Layout.Ev.iteT (c := Glyph.iend) (by simpa using h)
        (Work.Layout.ev_set main EvC.rLa Shift.gStop
          ⟨Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aB).headD Glyph.eos), s.stk⟩))
  · simp

/-- The inner block `peek aB rTa; if rTa = iend then set rLa gStop else set rLa gGo`, when the
digit stack `aB` still carries a bit. -/
theorem flagInnerEv_go (main : Cmd) (s : State)
    (h : (s.stk Work.IntLib.aB).headD Glyph.eos ≠ Glyph.iend) :
    ∃ (s' : State) (n : ℕ),
      Work.Layout.Ev main (Cmd.seq (Cmd.peek Work.IntLib.aB EvC.rTa)
          (Cmd.ite EvC.rTa Glyph.iend (Cmd.set EvC.rLa Shift.gStop) (Cmd.set EvC.rLa Shift.gGo)))
        s s' n ∧
      n ≤ 3 ∧ s'.reg EvC.rLa = Shift.gGo ∧ (∀ j : Stk, s'.stk j = s.stk j) := by
  refine ⟨⟨Function.update (Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aB).headD Glyph.eos))
      EvC.rLa Shift.gGo, s.stk⟩, 3, ?_, by norm_num, ?_, fun j => rfl⟩
  · exact Work.Layout.Ev.seq (Work.Layout.ev_peek main Work.IntLib.aB EvC.rTa s)
      (Work.Layout.Ev.iteF (c := Glyph.iend) (by simpa using h)
        (Work.Layout.ev_set main EvC.rLa Shift.gGo
          ⟨Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aB).headD Glyph.eos), s.stk⟩))
  · simp

/-! ## `flagA` as a function of the two stack heads -/

/-- `flagA` runs in at most `5` steps, never touches a stack, and sets `rLa` to
`gStop` exactly when the window stream `aW` is exhausted and the digit stream `aB` is exhausted,
and to `gGo` otherwise. -/
theorem flagAGen (main : Cmd) (s : State) :
    ∃ (s' : State) (n : ℕ),
      Work.Layout.Ev main EvC.flagA s s' n ∧ n ≤ 5 ∧
      s'.reg EvC.rLa =
        (if (s.stk Work.IntLib.aW).headD Glyph.eos = Shift.gmk Work.IntLib.aW then
           (if (s.stk Work.IntLib.aB).headD Glyph.eos = Glyph.iend then Shift.gStop else Shift.gGo)
         else Shift.gGo) ∧
      (∀ j : Stk, s'.stk j = s.stk j) := by
  by_cases hp : (s.stk Work.IntLib.aW).headD Glyph.eos = Shift.gmk Work.IntLib.aW
  · by_cases hq : (s.stk Work.IntLib.aB).headD Glyph.eos = Glyph.iend
    · obtain ⟨s', n, he, hle, hreg, hstk⟩ := flagInnerEv_stop main
        ⟨Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aW).headD Glyph.eos), s.stk⟩
        (by simpa using hq)
      refine ⟨s', 1 + (n + 1), ?_, by omega, ?_, ?_⟩
      · simp only [EvC.flagA, Work.Layout.seqs]
        exact Work.Layout.Ev.seq (Work.Layout.ev_peek main Work.IntLib.aW EvC.rTa s)
          (Work.Layout.Ev.iteT (c := Shift.gmk Work.IntLib.aW) (by simpa using hp) he)
      · rw [ite_eq_left hp, ite_eq_left hq]
        exact hreg
      · simpa using hstk
    · obtain ⟨s', n, he, hle, hreg, hstk⟩ := flagInnerEv_go main
        ⟨Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aW).headD Glyph.eos), s.stk⟩
        (by simpa using hq)
      refine ⟨s', 1 + (n + 1), ?_, by omega, ?_, ?_⟩
      · simp only [EvC.flagA, Work.Layout.seqs]
        exact Work.Layout.Ev.seq (Work.Layout.ev_peek main Work.IntLib.aW EvC.rTa s)
          (Work.Layout.Ev.iteT (c := Shift.gmk Work.IntLib.aW) (by simpa using hp) he)
      · rw [ite_eq_left hp, ite_eq_right hq]
        exact hreg
      · simpa using hstk
  · refine ⟨⟨Function.update (Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aW).headD Glyph.eos))
        EvC.rLa Shift.gGo, s.stk⟩, 3, ?_, by norm_num, ?_, fun j => rfl⟩
    · simp only [EvC.flagA, Work.Layout.seqs]
      exact Work.Layout.Ev.seq (Work.Layout.ev_peek main Work.IntLib.aW EvC.rTa s)
        (Work.Layout.Ev.iteF (c := Shift.gmk Work.IntLib.aW) (by simpa using hp)
          (Work.Layout.ev_set main EvC.rLa Shift.gGo
            ⟨Function.update s.reg EvC.rTa ((s.stk Work.IntLib.aW).headD Glyph.eos), s.stk⟩))
    · rw [ite_eq_right hp]
      simp

/-! ## Identifying the computed flag with `EvC.addFlag` -/

/-- Under the stream invariant `strP` at position `k`, the flag computed by `flagA` (as a function
of the two stack heads, see `flagAGen`) is `EvC.addFlag W hbits k`. -/
theorem flagAVal_eq (W hbits : List Bool) (Ws Bs : List Glyph) (k : ℕ) (s : State)
    (hstr : EvC.strP W hbits Ws Bs k s) (hk : k ≤ EvC.addN W hbits) :
    (if (s.stk Work.IntLib.aW).headD Glyph.eos = Shift.gmk Work.IntLib.aW then
       (if (s.stk Work.IntLib.aB).headD Glyph.eos = Glyph.iend then Shift.gStop else Shift.gGo)
     else Shift.gGo) = EvC.addFlag W hbits k := by
  obtain ⟨hW, hB⟩ := hstr
  rw [hW, hB]
  have h1 : (((W.drop k).map Glyph.bit ++ Shift.gmk Work.IntLib.aW :: Ws).headD Glyph.eos
      = Shift.gmk Work.IntLib.aW) ↔ W.drop k = [] := by
    cases W.drop k with
    | nil => simp
    | cons b tl => simp [Shift.bit_ne_gmk]
  have h2 : (((hbits.drop k).map Glyph.bit ++ Glyph.iend :: Shift.gmk Work.IntLib.aB :: Bs).headD
      Glyph.eos = Glyph.iend) ↔ hbits.drop k = [] := by
    cases hbits.drop k with
    | nil => simp
    | cons b tl => simp
  simp only [h1, h2]
  by_cases hw : W.drop k = []
  · by_cases hb : hbits.drop k = []
    · have hWl : W.length ≤ k := by
        have h3 : (W.drop k).length = 0 := List.length_eq_zero_iff.mpr hw
        rw [List.length_drop] at h3; omega
      have hBl : hbits.length ≤ k := by
        have h3 : (hbits.drop k).length = 0 := List.length_eq_zero_iff.mpr hb
        rw [List.length_drop] at h3; omega
      rw [ite_eq_left hw, ite_eq_left hb]
      rw [EvC.addFlag_of_le (W := W) (hbits := hbits) (k := k) (by simp only [EvC.addN]; omega)]
    · have hBl : k < hbits.length := by
        have h3 : (hbits.drop k).length ≠ 0 := fun hh => hb (List.length_eq_zero_iff.mp hh)
        rw [List.length_drop] at h3; omega
      rw [ite_eq_left hw, ite_eq_right hb]
      rw [EvC.addFlag_of_lt (W := W) (hbits := hbits) (k := k) (by simp only [EvC.addN]; omega)]
  · have hWl : k < W.length := by
      have h3 : (W.drop k).length ≠ 0 := fun hh => hw (List.length_eq_zero_iff.mp hh)
      rw [List.length_drop] at h3; omega
    rw [ite_eq_right hw]
    rw [EvC.addFlag_of_lt (W := W) (hbits := hbits) (k := k) (by simp only [EvC.addN]; omega)]

/-! ## The target lemma -/

theorem flagAEv (main : HvdH.Cmd) (W hbits : List Bool) (Ws Bs : List HvdH.Glyph) (k : ℕ)
    (s : HvdH.State) (hstr : Work.IntLib.EvC.strP W hbits Ws Bs k s)
    (hk : k ≤ Work.IntLib.EvC.addN W hbits) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main Work.IntLib.EvC.flagA s s' n ∧ n ≤ 5 ∧
      s'.reg Work.IntLib.EvC.rLa = Work.IntLib.EvC.addFlag W hbits k ∧
      (∀ j : HvdH.Stk, s'.stk j = s.stk j) := by
  obtain ⟨s', n, he, hle, hreg, hstk⟩ := flagAGen main s
  refine ⟨s', n, he, hle, ?_, hstk⟩
  rw [hreg]
  exact flagAVal_eq W hbits Ws Bs k s hstr hk

end Work.IntLib.evCA
