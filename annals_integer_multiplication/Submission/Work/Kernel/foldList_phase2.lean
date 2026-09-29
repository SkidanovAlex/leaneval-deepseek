import Mathlib
import Submission.Work.Kernel.foldListDefs

namespace Work.Kernel

open HvdH
open Work.Layout

/-! ## Phase 2 helpers -/

/-- State bookkeeping: register `foldList_rG` of the state obtained from `g` by first writing
`foldList_rG` and then `foldList_rL`. -/
theorem foldList_p2_reg_rG {g : Reg → Glyph} {X : Stk → List Glyph} {a c : Glyph} :
    (⟨Function.update (Function.update g foldList_rG a) foldList_rL c, X⟩ : State).reg foldList_rG
      = a := by
  show (Function.update (Function.update g foldList_rG a) foldList_rL c) foldList_rG = a
  rw [Function.update_of_ne (show foldList_rG ≠ foldList_rL by decide), Function.update_self]

/-- Same, for the register `foldList_rL`. -/
theorem foldList_p2_reg_rL {g : Reg → Glyph} {X : Stk → List Glyph} {a c : Glyph} :
    (⟨Function.update (Function.update g foldList_rG a) foldList_rL c, X⟩ : State).reg foldList_rL
      = c := by
  show (Function.update (Function.update g foldList_rG a) foldList_rL c) foldList_rL = c
  rw [Function.update_self]

/-- Same, for the stacks (they are untouched). -/
theorem foldList_p2_stk {g : Reg → Glyph} {X : Stk → List Glyph} {a c : Glyph} (k : Stk) :
    (⟨Function.update (Function.update g foldList_rG a) foldList_rL c, X⟩ : State).stk k = X k :=
  rfl

/-- The two leading commands of `foldList_prog2` (`peek` then the flag-setting `ite`) turn any state
whose stack `1` is `encs xs.reverse ++ foldList_tag :: A0` and whose stack `2` is
`foldList_tag :: B0` into a state satisfying the loop invariant `foldList_P2` at index `0`. -/
theorem foldList_p2_init (main : Cmd) (xs : List Val) (A0 B0 : List Glyph) (s : State)
    (hs1 : s.stk 1 = encs xs.reverse ++ foldList_tag :: A0)
    (hs2 : s.stk 2 = foldList_tag :: B0) :
    ∃ X1 X0, Ev main (.peek (1 : Stk) foldList_rG) s X1 1 ∧
      Ev main (.ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
        (.set foldList_rL Glyph.cons)) X1 X0 2 ∧
      foldList_P2 xs A0 B0 s 0 X0 := by
  have hhd : (s.stk 1).headD Glyph.eos
      = (encs xs.reverse ++ foldList_tag :: A0).headD Glyph.eos := by rw [hs1]
  by_cases h : xs.reverse = []
  · -- the remaining list is empty: the peeked glyph is the frame marker
    have hxs : xs = [] := List.reverse_eq_nil_iff.mp h
    subst hxs
    have hhead : (s.stk 1).headD Glyph.eos = foldList_tag := by rw [hhd]; rfl
    refine ⟨_, ⟨Function.update (Function.update s.reg foldList_rG ((s.stk 1).headD Glyph.eos))
        foldList_rL Glyph.eos, s.stk⟩, ev_peek main 1 foldList_rG s, ?_, ?_⟩
    · refine Ev.iteT ?_ (ev_set main foldList_rL Glyph.eos _)
      show (Function.update s.reg foldList_rG ((s.stk 1).headD Glyph.eos)) foldList_rG
        = foldList_tag
      rw [Function.update_self]; exact hhead
    · unfold foldList_P2
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs1]; rfl
      · rw [hs2]; rfl
      · intro k _ _ _; rfl
      · rw [foldList_p2_reg_rG]
      · rw [foldList_p2_reg_rL]; simp
  · -- elements remain: the peeked glyph is not the frame marker, so `rL` becomes `cons`
    have hhead : (s.stk 1).headD Glyph.eos ≠ foldList_tag := fun hh =>
      h ((foldList_headD_encs_eq_tag_iff xs.reverse A0).mp (by rw [← hhd]; exact hh))
    have hxsne : xs ≠ [] := fun hh => h (by rw [hh]; rfl)
    have hpos : 0 < xs.length := List.length_pos_iff.mpr hxsne
    refine ⟨_, ⟨Function.update (Function.update s.reg foldList_rG ((s.stk 1).headD Glyph.eos))
        foldList_rL Glyph.cons, s.stk⟩, ev_peek main 1 foldList_rG s, ?_, ?_⟩
    · refine Ev.iteF ?_ (ev_set main foldList_rL Glyph.cons _)
      show (Function.update s.reg foldList_rG ((s.stk 1).headD Glyph.eos)) foldList_rG
        ≠ foldList_tag
      rw [Function.update_self]; exact hhead
    · unfold foldList_P2
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs1]; rfl
      · rw [hs2]; rfl
      · intro k _ _ _; rfl
      · rw [foldList_p2_reg_rG]
      · rw [foldList_p2_reg_rL]; simp [hpos]

/-- One iteration of `foldList_body2` maps `foldList_P2 i` to `foldList_P2 (i+1)` for `i < xs.length`,
within the uniform budget `16 * (L + 1) + 4`, and the loop flag is `cons` at such a state. -/
theorem foldList_p2_step (main : Cmd) (xs : List Val) (A0 B0 : List Glyph) (s : State) (L : ℕ)
    (hL : ∀ x ∈ xs, vsz x ≤ L) (i : ℕ) (hi : i < xs.length) (X : State)
    (hX : foldList_P2 xs A0 B0 s i X) :
    X.reg foldList_rL = Glyph.cons ∧
      ∃ X', foldList_P2 xs A0 B0 s (i + 1) X' ∧
        Ev main foldList_body2 X X' (16 * (L + 1) + 4) := by
  unfold foldList_P2 at hX
  obtain ⟨h0, h1, h2, hfr, hG, hR⟩ := hX
  have hi' : i < (xs.reverse).length := by simpa using hi
  have hrl : X.reg foldList_rL = Glyph.cons := by rw [hR]; simp [hi]
  refine ⟨hrl, ?_⟩
  have hdrop : (xs.reverse).drop i
      = (xs.reverse).getD i Val.nil :: (xs.reverse).drop (i + 1) :=
    foldList_drop_eq_getD_cons xs.reverse i hi'
  have hhead_ne : X.reg foldList_rG ≠ foldList_tag := by
    rw [hG, h1, hdrop]
    exact foldList_headD_encs_ne_tag _ _ _
  have ha : X.stk 1 = ((xs.reverse).getD i Val.nil).enc
      ++ (encs ((xs.reverse).drop (i + 1)) ++ foldList_tag :: A0) := by
    rw [h1, hdrop, encs_cons, List.append_assoc]
  obtain ⟨Y, n1, hev1, hn1, hY1, hY2, hY3, hY4, hYfr⟩ :=
    mvVal_ev_full (main := main) (a := (1 : Stk)) (b := (2 : Stk)) (c := (3 : Stk))
      (d := (4 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := X.reg) (X := X.stk) (v := (xs.reverse).getD i Val.nil)
      (A := encs ((xs.reverse).drop (i + 1)) ++ foldList_tag :: A0) (B := X.stk 2) ha rfl
  have hv : vsz ((xs.reverse).getD i Val.nil) ≤ L :=
    hL _ (by rw [← List.mem_reverse]; exact foldList_getD_mem hi')
  have hYfr' : ∀ k, k ≠ 1 → k ≠ 2 → Y.stk k = X.stk k := by
    intro k hk1 hk2
    by_cases h3 : k = 3
    · subst h3; exact hY3
    by_cases h4 : k = 4
    · subst h4; exact hY4
    · exact hYfr k hk1 hk2 h3 h4
  have hYhd : (Y.stk 1).headD Glyph.eos
      = (encs ((xs.reverse).drop (i + 1)) ++ foldList_tag :: A0).headD Glyph.eos := by rw [hY1]
  by_cases hA : (xs.reverse).drop (i + 1) = []
  · -- only the frame marker is left on stack 1
    have hYtag : (Y.stk 1).headD Glyph.eos = foldList_tag := by rw [hYhd, hA]; rfl
    have hnlt : ¬ (i + 1 < xs.length) := by
      have hle : xs.length ≤ i + 1 := by
        have := List.drop_eq_nil_iff.mp hA
        simpa [List.length_reverse] using this
      omega
    refine ⟨⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
        foldList_rL Glyph.eos, Y.stk⟩, ?_, ?_⟩
    · unfold foldList_P2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Y.stk 0 = s.stk 0
        rw [hYfr' 0 (by decide) (by decide)]; exact h0
      · show Y.stk 1 = encs ((xs.reverse).drop (i + 1)) ++ foldList_tag :: A0
        rw [hY1]
      · show Y.stk 2 = encs (((xs.reverse).take (i + 1)).reverse) ++ foldList_tag :: B0
        rw [hY2, h2, foldList_take_reverse_succ (xs.reverse) i hi', encs_cons, List.append_assoc]
      · intro k hk0 hk1 hk2
        show Y.stk k = s.stk k
        rw [hYfr' k hk1 hk2]; exact hfr k hk0 hk1 hk2
      · rw [foldList_p2_reg_rG]
      · rw [foldList_p2_reg_rL]; simp [hnlt]
    · have hZtag : (⟨Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos), Y.stk⟩
          : State).reg foldList_rG = foldList_tag := by
        show (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos)) foldList_rG
          = foldList_tag
        rw [Function.update_self]; exact hYtag
      have hite : Ev main (.ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
          (.set foldList_rL Glyph.cons))
          ⟨Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos), Y.stk⟩
          ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
            foldList_rL Glyph.eos, Y.stk⟩ 2 :=
        Ev.iteT hZtag (ev_set main foldList_rL Glyph.eos _)
      have hinner : Ev main (seqs [mvVal (1 : Stk) (2 : Stk) (3 : Stk) (4 : Stk),
          .peek (1 : Stk) foldList_rG,
          .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
            (.set foldList_rL Glyph.cons)]) X
          ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
            foldList_rL Glyph.eos, Y.stk⟩ (n1 + 3) := by
        have h2' : Ev main (seqs [.peek (1 : Stk) foldList_rG,
            .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
              (.set foldList_rL Glyph.cons)]) Y
            ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
              foldList_rL Glyph.eos, Y.stk⟩ 3 := by
          simpa [seqs] using Ev.seq (ev_peek main 1 foldList_rG Y) hite
        simpa [seqs] using Ev.seq hev1 h2'
      exact (Ev.iteF hhead_ne hinner).mono (by omega)
  · -- elements remain
    have hpos : i + 1 < xs.length := by
      by_contra hh
      have hle : xs.length ≤ i + 1 := by omega
      exact hA (List.drop_eq_nil_iff.mpr (by simpa [List.length_reverse] using hle))
    obtain ⟨v2, rest2, hrest2⟩ := List.exists_cons_of_ne_nil hA
    have hYne : (Y.stk 1).headD Glyph.eos ≠ foldList_tag := by
      rw [hYhd, hrest2]
      exact foldList_headD_encs_ne_tag v2 rest2 (foldList_tag :: A0)
    refine ⟨⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
        foldList_rL Glyph.cons, Y.stk⟩, ?_, ?_⟩
    · unfold foldList_P2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Y.stk 0 = s.stk 0
        rw [hYfr' 0 (by decide) (by decide)]; exact h0
      · show Y.stk 1 = encs ((xs.reverse).drop (i + 1)) ++ foldList_tag :: A0
        rw [hY1]
      · show Y.stk 2 = encs (((xs.reverse).take (i + 1)).reverse) ++ foldList_tag :: B0
        rw [hY2, h2, foldList_take_reverse_succ (xs.reverse) i hi', encs_cons, List.append_assoc]
      · intro k hk0 hk1 hk2
        show Y.stk k = s.stk k
        rw [hYfr' k hk1 hk2]; exact hfr k hk0 hk1 hk2
      · rw [foldList_p2_reg_rG]
      · rw [foldList_p2_reg_rL]; simp [hpos]
    · have hZne : (⟨Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos), Y.stk⟩
          : State).reg foldList_rG ≠ foldList_tag := by
        show (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos)) foldList_rG
          ≠ foldList_tag
        rw [Function.update_self]; exact hYne
      have hite : Ev main (.ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
          (.set foldList_rL Glyph.cons))
          ⟨Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos), Y.stk⟩
          ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
            foldList_rL Glyph.cons, Y.stk⟩ 2 :=
        Ev.iteF hZne (ev_set main foldList_rL Glyph.cons _)
      have hinner : Ev main (seqs [mvVal (1 : Stk) (2 : Stk) (3 : Stk) (4 : Stk),
          .peek (1 : Stk) foldList_rG,
          .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
            (.set foldList_rL Glyph.cons)]) X
          ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
            foldList_rL Glyph.cons, Y.stk⟩ (n1 + 3) := by
        have h2' : Ev main (seqs [.peek (1 : Stk) foldList_rG,
            .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
              (.set foldList_rL Glyph.cons)]) Y
            ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 1).headD Glyph.eos))
              foldList_rL Glyph.cons, Y.stk⟩ 3 := by
          simpa [seqs] using Ev.seq (ev_peek main 1 foldList_rG Y) hite
        simpa [seqs] using Ev.seq hev1 h2'
      exact (Ev.iteF hhead_ne hinner).mono (by omega)

/-- At `foldList_P2 xs.length` the loop flag is no longer `cons`, so the loop stops. -/
theorem foldList_p2_stop (xs : List Val) (A0 B0 : List Glyph) (s : State) (X : State)
    (hX : foldList_P2 xs A0 B0 s xs.length X) : X.reg foldList_rL ≠ Glyph.cons := by
  unfold foldList_P2 at hX
  obtain ⟨-, -, -, -, -, hR⟩ := hX
  rw [hR]
  simp

/-- The trailing `pop` of `foldList_prog2`: from `foldList_P2 xs.length` it removes the frame
marker of stack `1` and leaves the required output state. -/
theorem foldList_p2_pop (main : Cmd) (xs : List Val) (A0 B0 : List Glyph) (s : State) (Y : State)
    (hY : foldList_P2 xs A0 B0 s xs.length Y) :
    ∃ Z, Ev main (.pop (1 : Stk) foldList_rS) Y Z 1 ∧
      Z.stk 0 = s.stk 0 ∧ Z.stk 1 = A0 ∧
      Z.stk 2 = encs xs ++ foldList_tag :: B0 ∧
      (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → Z.stk k = s.stk k) := by
  unfold foldList_P2 at hY
  obtain ⟨h0, h1, h2, hfr, -, -⟩ := hY
  refine ⟨_, ev_pop main 1 foldList_rS Y, ?_, ?_, ?_, ?_⟩
  · show (Function.update Y.stk (1 : Stk) (Y.stk 1).tail) 0 = s.stk 0
    rw [Function.update_of_ne (show (0 : Stk) ≠ 1 by decide)]; exact h0
  · show (Function.update Y.stk (1 : Stk) (Y.stk 1).tail) 1 = A0
    rw [Function.update_self, h1, ← List.length_reverse, List.drop_length]
    rfl
  · show (Function.update Y.stk (1 : Stk) (Y.stk 1).tail) 2
      = encs xs ++ foldList_tag :: B0
    rw [Function.update_of_ne (show (2 : Stk) ≠ 1 by decide), h2, ← List.length_reverse,
      foldList_take_reverse_length, List.reverse_reverse]
  · intro k hk0 hk1 hk2
    show (Function.update Y.stk (1 : Stk) (Y.stk 1).tail) k = s.stk k
    rw [Function.update_of_ne (show k ≠ (1 : Stk) from hk1)]
    exact hfr k hk0 hk1 hk2

/-- **Phase 2 of `Work.Kernel.foldList`** (revised: the loop now runs exactly `xs.length` times).

`Work.Kernel.foldList_prog2` (defined in `Submission/Work/Kernel/foldListDefs.lean`, together with
`foldList_tag = Glyph.mk 5`, `foldList_rG`, `foldList_rL`, `foldList_rS`, `foldList_P2`,
`foldList_loopEv`, `foldList_headD_enc_append_ne_tag`, `foldList_headD_encs_eq_tag_iff`,
`foldList_drop_eq_getD_cons`, `foldList_take_reverse_succ`, `foldList_getD_mem`) is

```
seqs [.peek 1 foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons),
      .loop foldList_rL Glyph.cons foldList_body2, .pop 1 foldList_rS]
```
with `foldList_body2 = .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
   (seqs [Work.Layout.mvVal 1 2 3 4, .peek 1 foldList_rG,
          .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons)])`.

Stack `1` holds the elements of `xs` in reverse order above the frame marker; the program moves them
one by one (`mvVal 1 2 3 4`, cost `≤ 16 * (vsz x + 1)`, scratch `3`, `4` restored) to stack `2`,
which therefore ends holding `encs xs ++ foldList_tag :: B0`.  The flag `foldList_rL` is refreshed at
the **end** of every body from the freshly peeked glyph, so the loop runs exactly `xs.length` bodies
(`xs.length + 1` tests) — the previous version needed one extra marker-detecting iteration.
`foldList_headD_enc_append_ne_tag` says the head of a value encoding is never the marker;
`foldList_headD_encs_eq_tag_iff` says the marker is on top exactly when the remaining list is empty.
Loop invariant `foldList_P2` (rL = cons iff `i < xs.length`), unrolled with `foldList_loopEv`
(uniform body budget `16 * (L + 1) + 4`), then `Ev.seq`/`Ev.mono`.
Helpers must be named with the prefix `foldList_p2_`. -/
theorem foldList_phase2 (main : HvdH.Cmd) (xs : List HvdH.Val) (A0 B0 : List HvdH.Glyph)
    (s : HvdH.State) (L : ℕ) (hL : ∀ x ∈ xs, HvdH.vsz x ≤ L)
    (hs1 : s.stk 1 = HvdH.encs xs.reverse ++ Work.Kernel.foldList_tag :: A0)
    (hs2 : s.stk 2 = Work.Kernel.foldList_tag :: B0) :
    ∃ s', Work.Layout.Ev main Work.Kernel.foldList_prog2 s s'
        (xs.length * (16 * (L + 1) + 5) + 5) ∧
      s'.stk 0 = s.stk 0 ∧
      s'.stk 1 = A0 ∧
      s'.stk 2 = HvdH.encs xs ++ Work.Kernel.foldList_tag :: B0 ∧
      (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → s'.stk k = s.stk k) := by
  obtain ⟨X1, X0, hpeek, hite, hP0⟩ := foldList_p2_init main xs A0 B0 s hs1 hs2
  obtain ⟨Y, hloop, hPend⟩ := foldList_loopEv main foldList_rL Glyph.cons foldList_body2
    xs.length (foldList_P2 xs A0 B0 s) (16 * (L + 1) + 4) X0 hP0
    (fun i hi X hX => foldList_p2_step main xs A0 B0 s L hL i hi X hX)
    (fun X hX => foldList_p2_stop xs A0 B0 s X hX)
  obtain ⟨Z, hpop, hZ0, hZ1, hZ2, hZfr⟩ := foldList_p2_pop main xs A0 B0 s Y hPend
  have hloop' : Ev main (seqs [.loop foldList_rL Glyph.cons foldList_body2,
      .pop (1 : Stk) foldList_rS]) X0 Z
      (xs.length * (16 * (L + 1) + 4) + xs.length + 1 + 1) := by
    simpa [seqs] using Ev.seq hloop hpop
  have hrest : Ev main (seqs [.ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
      (.set foldList_rL Glyph.cons), .loop foldList_rL Glyph.cons foldList_body2,
      .pop (1 : Stk) foldList_rS]) X1 Z
      (2 + (xs.length * (16 * (L + 1) + 4) + xs.length + 1 + 1)) :=
    Ev.seqs_cons hite hloop'
  have htot : Ev main (seqs [.peek (1 : Stk) foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons),
      .loop foldList_rL Glyph.cons foldList_body2, .pop (1 : Stk) foldList_rS]) s Z
      (1 + (2 + (xs.length * (16 * (L + 1) + 4) + xs.length + 1 + 1))) :=
    Ev.seqs_cons hpeek hrest
  have hmain : Ev main foldList_prog2 s Z
      (1 + (2 + (xs.length * (16 * (L + 1) + 4) + xs.length + 1 + 1))) := by
    simpa [foldList_prog2] using htot
  refine ⟨Z, hmain.mono ?_, hZ0, hZ1, hZ2, hZfr⟩
  have hE : 1 + (2 + (xs.length * (16 * (L + 1) + 4) + xs.length + 1 + 1))
      = xs.length * (16 * (L + 1) + 5) + 5 := by ring
  exact le_of_eq hE

end Work.Kernel
