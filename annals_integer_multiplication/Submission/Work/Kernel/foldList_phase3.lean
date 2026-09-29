import Mathlib
import Submission.Work.Kernel.foldListDefs

set_option autoImplicit false

namespace Work.Kernel

open HvdH
open Work.Layout

/-! ## Helpers for phase 3 of `Work.Kernel.foldList` -/

/-- `peek 2 foldList_rG` followed by the flag-setting `ite` (the same two commands as the head of
`foldList_prog3` and of `foldList_body3`): the resulting state has the same stacks as the input,
`foldList_rG` holds the leading glyph of stack `2`, and `foldList_rL` is set to `Glyph.eos` exactly
when that glyph is the frame marker. -/
theorem foldList_p3_peek_ite (main : Cmd) (Y : State) :
    ∃ Z1 Z, Ev main (.peek (2 : Stk) foldList_rG) Y Z1 1 ∧
      Ev main (.ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
        (.set foldList_rL Glyph.cons)) Z1 Z 2 ∧
      Z.stk = Y.stk ∧ Z.reg foldList_rG = (Y.stk 2).headD Glyph.eos ∧
      Z.reg foldList_rL
        = (if (Y.stk 2).headD Glyph.eos = foldList_tag then Glyph.eos else Glyph.cons) := by
  by_cases h : (Y.stk 2).headD Glyph.eos = foldList_tag
  · refine ⟨⟨Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos), Y.stk⟩,
      ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos))
        foldList_rL Glyph.eos, Y.stk⟩, ev_peek main 2 foldList_rG Y, ?_, rfl, ?_, ?_⟩
    · refine Ev.iteT ?_ (ev_set main foldList_rL Glyph.eos _)
      show (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos)) foldList_rG
        = foldList_tag
      rw [Function.update_self]; exact h
    · show (Function.update (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos))
          foldList_rL Glyph.eos) foldList_rG = (Y.stk 2).headD Glyph.eos
      rw [Function.update_apply, if_neg (by decide : foldList_rG ≠ foldList_rL),
        Function.update_self]
    · show (Function.update (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos))
          foldList_rL Glyph.eos) foldList_rL
        = (if (Y.stk 2).headD Glyph.eos = foldList_tag then Glyph.eos else Glyph.cons)
      rw [Function.update_self, if_pos h]
  · refine ⟨⟨Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos), Y.stk⟩,
      ⟨Function.update (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos))
        foldList_rL Glyph.cons, Y.stk⟩, ev_peek main 2 foldList_rG Y, ?_, rfl, ?_, ?_⟩
    · refine Ev.iteF ?_ (ev_set main foldList_rL Glyph.cons _)
      show (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos)) foldList_rG
        ≠ foldList_tag
      rw [Function.update_self]; exact h
    · show (Function.update (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos))
          foldList_rL Glyph.cons) foldList_rG = (Y.stk 2).headD Glyph.eos
      rw [Function.update_apply, if_neg (by decide : foldList_rG ≠ foldList_rL),
        Function.update_self]
    · show (Function.update (Function.update Y.reg foldList_rG ((Y.stk 2).headD Glyph.eos))
          foldList_rL Glyph.cons) foldList_rL
        = (if (Y.stk 2).headD Glyph.eos = foldList_tag then Glyph.eos else Glyph.cons)
      rw [Function.update_self, if_neg h]

/-- The two leading commands of `foldList_prog3 q` (`peek` then the flag-setting `ite`) turn a state
whose stack `0` is `encs acc ++ R` and whose stack `2` is `encs xs ++ foldList_tag :: B0` into a
state satisfying the loop invariant `foldList_P3` at index `0`. -/
theorem foldList_p3_init (main : Cmd) (xs : List Val) (I : ℕ → List Val → Prop) (acc : List Val)
    (R B0 : List Glyph) (s : State) (hI : I 0 acc) (hs0 : s.stk 0 = encs acc ++ R)
    (hs2 : s.stk 2 = encs xs ++ foldList_tag :: B0) :
    ∃ Z1 Z, Ev main (.peek (2 : Stk) foldList_rG) s Z1 1 ∧
      Ev main (.ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
        (.set foldList_rL Glyph.cons)) Z1 Z 2 ∧ foldList_P3 xs R I B0 s 0 Z := by
  obtain ⟨Z1, Z, hpeek, hite, hZstk, hZrG, hZrL⟩ := foldList_p3_peek_ite main s
  refine ⟨Z1, Z, hpeek, hite, ?_⟩
  have hhead : (s.stk 2).headD Glyph.eos = foldList_tag ↔ xs = [] := by
    rw [hs2]; exact foldList_headD_encs_eq_tag_iff xs B0
  simp only [foldList_P3]
  refine ⟨⟨acc, hI, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hZstk, hs0]
  · rw [hZstk]; simpa using hs2
  · intro k hk0 hk2
    rw [hZstk]
  · rw [hZrG, hZstk]
  · rw [hZrL]
    by_cases hx : xs = []
    · rw [if_pos (hhead.mpr hx)]
      have hlt : ¬ ((0 : ℕ) < xs.length) := by rw [hx]; simp
      rw [if_neg hlt]
    · rw [if_neg (fun hh => hx (hhead.mp hh))]
      rw [if_pos (List.length_pos_iff.mpr hx)]

/-- One iteration of `foldList_body3 q` maps `foldList_P3 i` to `foldList_P3 (i+1)` for
`i < xs.length`, within the uniform budget `16 * (L + 1) + c + 4`; at such a state the loop flag is
`Glyph.cons`.  The body moves the next element on top of the accumulator (`mvVal`, budget
`16 * (L + 1)`), runs `q` through its `WordR` hypothesis (budget `c`) on the raw frame `R`, and
refreshes the flag from the freshly peeked glyph of stack `2`. -/
theorem foldList_p3_step (main q : Cmd) (xs : List Val) (I : ℕ → List Val → Prop)
    (R B0 : List Glyph) (s : State) (c L : ℕ) (hL : ∀ x ∈ xs, vsz x ≤ L)
    (hq : ∀ i a, i < xs.length → I i a →
      WordR main q (fun vs => vs = xs.getD i Val.nil :: a) (fun _ out => I (i + 1) out)
        (fun _ => c))
    (i : ℕ) (hi : i < xs.length) (X : State) (hX : foldList_P3 xs R I B0 s i X) :
    X.reg foldList_rL = Glyph.cons ∧
      ∃ X', foldList_P3 xs R I B0 s (i + 1) X' ∧
        Ev main (foldList_body3 q) X X' (16 * (L + 1) + c + 4) := by
  simp only [foldList_P3] at hX
  obtain ⟨⟨a, hIa, h0⟩, h2, hfr, hG, hR⟩ := hX
  have hrl : X.reg foldList_rL = Glyph.cons := by rw [hR, if_pos hi]
  refine ⟨hrl, ?_⟩
  -- split off the next element of the remaining list
  have hdrop : xs.drop i = xs.getD i Val.nil :: xs.drop (i + 1) :=
    foldList_drop_eq_getD_cons xs i hi
  have ha : X.stk 2 = (xs.getD i Val.nil).enc ++
      (encs (xs.drop (i + 1)) ++ foldList_tag :: B0) := by
    rw [h2, hdrop, encs_cons, List.append_assoc]
  have hhead_ne : X.reg foldList_rG ≠ foldList_tag := by
    rw [hG, h2, hdrop]
    exact foldList_headD_encs_ne_tag (xs.getD i Val.nil) (xs.drop (i + 1))
      (foldList_tag :: B0)
  -- move the element on top of the accumulator: stack `0` becomes `encs (x :: a) ++ R`
  obtain ⟨Y, n1, hev1, hn1, hY2, hY0, hY3, hY4, hYfr⟩ :=
    mvVal_ev_full (main := main) (a := (2 : Stk)) (b := (0 : Stk)) (c := (3 : Stk))
      (d := (4 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := X.reg) (X := X.stk) (v := xs.getD i Val.nil)
      (A := encs (xs.drop (i + 1)) ++ foldList_tag :: B0) (B := X.stk 0) ha rfl
  have hY0' : Y.stk 0 = encs (xs.getD i Val.nil :: a) ++ R := by
    rw [hY0, h0, encs_cons, List.append_assoc]
  -- run `q` on the exposed element with the same raw frame `R`
  obtain ⟨out, s₂, n2, hPost, hev2, hn2, hs2₀, hs2fr⟩ :=
    hq i a hi hIa (xs.getD i Val.nil :: a) rfl Y R hY0'
  -- refresh the flag from the new top of stack `2`
  obtain ⟨Z1, Z, hpeek, hite, hZstk, hZrG, hZrL⟩ := foldList_p3_peek_ite main s₂
  have hrefresh : Ev main (seqs [.peek (2 : Stk) foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
        (.set foldList_rL Glyph.cons)]) s₂ Z 3 :=
    Ev.seq hpeek hite
  have hinner : Ev main (seqs [mvVal (2 : Stk) (0 : Stk) (3 : Stk) (4 : Stk), q,
      .peek (2 : Stk) foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
        (.set foldList_rL Glyph.cons)]) X Z (n1 + (n2 + 3)) := by
    show Ev main (.seq (mvVal (2 : Stk) (0 : Stk) (3 : Stk) (4 : Stk))
      (.seq q (.seq (.peek (2 : Stk) foldList_rG) (.ite foldList_rG foldList_tag
        (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons))))) X Z (n1 + (n2 + 3))
    exact Ev.seq hev1 (Ev.seq ⟨n2, hev2, le_rfl⟩ hrefresh)
  have hbody : Ev main (foldList_body3 q) X Z (n1 + (n2 + 3) + 1) := Ev.iteF hhead_ne hinner
  have hn1' : n1 ≤ 16 * (L + 1) := by
    have hv : vsz (xs.getD i Val.nil) ≤ L := hL _ (foldList_getD_mem hi)
    omega
  have hn2c : n2 ≤ c := hn2
  refine ⟨Z, ?_, hbody.mono (by omega)⟩
  -- the invariant at `i + 1`
  have hs₂2 : s₂.stk 2 = encs (xs.drop (i + 1)) ++ foldList_tag :: B0 := by
    rw [hs2fr 2 (by decide), hY2]
  have hYX : ∀ k : Stk, k ≠ 0 → k ≠ 2 → Y.stk k = X.stk k := by
    intro k hk0 hk2
    by_cases h3 : k = 3
    · rw [h3]; exact hY3
    · by_cases h4 : k = 4
      · rw [h4]; exact hY4
      · exact hYfr k hk2 hk0 h3 h4
  have hheadiff : (s₂.stk 2).headD Glyph.eos = foldList_tag ↔ xs.drop (i + 1) = [] := by
    rw [hs₂2]; exact foldList_headD_encs_eq_tag_iff (xs.drop (i + 1)) B0
  have hZval : Z.reg foldList_rL
      = (if xs.drop (i + 1) = [] then Glyph.eos else Glyph.cons) := by
    rw [hZrL]
    by_cases hA : xs.drop (i + 1) = []
    · rw [if_pos (hheadiff.mpr hA), if_pos hA]
    · rw [if_neg (fun hh => hA (hheadiff.mp hh)), if_neg hA]
  have hFLAG : (if xs.drop (i + 1) = [] then Glyph.eos else Glyph.cons)
      = (if i + 1 < xs.length then Glyph.cons else Glyph.eos) := by
    by_cases hA : xs.drop (i + 1) = []
    · have hlt : ¬ (i + 1 < xs.length) := by rw [List.drop_eq_nil_iff] at hA; omega
      rw [if_pos hA, if_neg hlt]
    · have hlt : i + 1 < xs.length := by rw [List.drop_eq_nil_iff] at hA; omega
      rw [if_neg hA, if_pos hlt]
  simp only [foldList_P3]
  refine ⟨⟨out, hPost, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hZstk]; exact hs2₀
  · rw [hZstk]; exact hs₂2
  · intro k hk0 hk2
    rw [hZstk, hs2fr k hk0, hYX k hk0 hk2, hfr k hk0 hk2]
  · rw [hZrG, hZstk]
  · rw [hZval, hFLAG]

/-- At `foldList_P3 xs.length` the loop flag is no longer `cons`, so the loop stops. -/
theorem foldList_p3_stop (xs : List Val) (R : List Glyph) (I : ℕ → List Val → Prop)
    (B0 : List Glyph) (s X : State) (hX : foldList_P3 xs R I B0 s xs.length X) :
    X.reg foldList_rL ≠ Glyph.cons := by
  simp only [foldList_P3] at hX
  obtain ⟨-, -, -, -, hR⟩ := hX
  rw [hR]
  simp

/-- The trailing `pop` of `foldList_prog3 q`: from `foldList_P3 xs.length` it removes the frame
marker of stack `2` and leaves the required output state. -/
theorem foldList_p3_pop (main : Cmd) (xs : List Val) (I : ℕ → List Val → Prop)
    (R B0 : List Glyph) (s Y : State) (hY : foldList_P3 xs R I B0 s xs.length Y) :
    ∃ Z, Ev main (.pop (2 : Stk) foldList_rS) Y Z 1 ∧
      (∃ a, I xs.length a ∧ Z.stk 0 = encs a ++ R) ∧
      Z.stk 2 = B0 ∧
      (∀ k, k ≠ 0 → k ≠ 2 → Z.stk k = s.stk k) := by
  simp only [foldList_P3] at hY
  obtain ⟨⟨a, hIa, h0⟩, h2, hfr, -, -⟩ := hY
  refine ⟨_, ev_pop main 2 foldList_rS Y, ⟨a, hIa, ?_⟩, ?_, ?_⟩
  · show (Function.update Y.stk (2 : Stk) (Y.stk 2).tail) 0 = encs a ++ R
    rw [Function.update_apply, if_neg (by decide : (0 : Stk) ≠ 2)]
    exact h0
  · show (Function.update Y.stk (2 : Stk) (Y.stk 2).tail) 2 = B0
    rw [Function.update_self, h2, foldList_drop_length]
    rfl
  · intro k hk0 hk2
    show (Function.update Y.stk (2 : Stk) (Y.stk 2).tail) k = s.stk k
    rw [Function.update_apply, if_neg hk2]
    exact hfr k hk0 hk2

/-- **Phase 3 of `Work.Kernel.foldList`** (revised: the loop now runs exactly `xs.length` times; the
per-element budget has one unit of slack, so the plain `Work.Layout.mvVal_ev_full` bound
`16 * (vsz x + 1) ≤ 16 * (L + 1)` suffices).

`Work.Kernel.foldList_prog3 q` (defined in `Submission/Work/Kernel/foldListDefs.lean`, together with
`foldList_tag = Glyph.mk 5`, `foldList_rG`, `foldList_rL`, `foldList_rS`, `foldList_P3`,
`foldList_loopEv`, `foldList_headD_enc_append_ne_tag`, `foldList_headD_encs_eq_tag_iff`,
`foldList_drop_eq_getD_cons`, `foldList_getD_mem`) is

```
seqs [.peek 2 foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons),
      .loop foldList_rL Glyph.cons (foldList_body3 q), .pop 2 foldList_rS]
```
with `foldList_body3 q = .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
   (seqs [Work.Layout.mvVal 2 0 3 4, q, .peek 2 foldList_rG,
          .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons)])`.

Stack `2` holds the elements of `xs` in order above the frame marker and stack `0` holds the
accumulator `acc` with `I 0 acc`.  Each iteration moves the next element (`mvVal 2 0 3 4`, cost
`≤ 16 * (vsz x + 1)`) on top of the accumulator, so stack `0` is exactly
`encs (xs.getD i .nil :: a) ++ R` when `q` runs; `q`'s `WordR` (hypothesis `hq`, run with the same raw
frame `R`) returns `a'` with `I (i+1) a'`.  The flag `foldList_rL` is refreshed at the **end** of
every body from the freshly peeked glyph, so the loop runs exactly `xs.length` bodies
(`xs.length + 1` tests) — the previous version needed one extra marker-detecting iteration.
`foldList_headD_enc_append_ne_tag` says the head of a value encoding is never the marker;
`foldList_headD_encs_eq_tag_iff` says the marker is on top exactly when the remaining list is empty.
Loop invariant `foldList_P3` (rL = cons iff `i < xs.length`), unrolled with `foldList_loopEv`
(uniform body budget `16 * (L + 1) + c + 4`), then `Ev.seq`/`Ev.mono`.
Helpers must be named with the prefix `foldList_p3_`. -/
theorem foldList_phase3 (main q : HvdH.Cmd) (xs : List HvdH.Val) (I : ℕ → List HvdH.Val → Prop)
    (acc : List HvdH.Val) (R : List HvdH.Glyph) (B0 : List HvdH.Glyph) (s : HvdH.State) (c L : ℕ)
    (hL : ∀ x ∈ xs, HvdH.vsz x ≤ L)
    (hq : ∀ i a, i < xs.length → I i a →
      HvdH.WordR main q (fun vs => vs = xs.getD i HvdH.Val.nil :: a)
        (fun _ out => I (i + 1) out) (fun _ => c))
    (hs0 : s.stk 0 = HvdH.encs acc ++ R) (hI : I 0 acc)
    (hs2 : s.stk 2 = HvdH.encs xs ++ Work.Kernel.foldList_tag :: B0) :
    ∃ s', Work.Layout.Ev main (Work.Kernel.foldList_prog3 q) s s'
        (xs.length * (16 * (L + 1) + c + 5) + 5) ∧
      (∃ a, I xs.length a ∧ s'.stk 0 = HvdH.encs a ++ R) ∧
      s'.stk 2 = B0 ∧
      (∀ k, k ≠ 0 → k ≠ 2 → s'.stk k = s.stk k) := by
  -- the leading `peek`/`ite`: they install `foldList_P3 0`
  obtain ⟨Z1, Z0, hpeek, hite, hP0⟩ :=
    foldList_p3_init main xs I acc R B0 s hI hs0 hs2
  -- the loop, unrolled along `foldList_P3` with the uniform budget `16 * (L + 1) + c + 4`
  obtain ⟨Y, hloop, hPend⟩ := foldList_loopEv main foldList_rL Glyph.cons (foldList_body3 q)
    xs.length (foldList_P3 xs R I B0 s) (16 * (L + 1) + c + 4) Z0 hP0
    (fun i hi X hX => foldList_p3_step main q xs I R B0 s c L hL hq i hi X hX)
    (fun X hX => foldList_p3_stop xs R I B0 s X hX)
  -- the trailing `pop`, which removes the frame marker of stack `2`
  obtain ⟨Z, hpop, hZ0, hZ2, hZfr⟩ := foldList_p3_pop main xs I R B0 s Y hPend
  have htail : Ev main (seqs [.loop foldList_rL Glyph.cons (foldList_body3 q),
      .pop (2 : Stk) foldList_rS]) Z0 Z
      (xs.length * (16 * (L + 1) + c + 4) + xs.length + 1 + 1) := by
    simpa [seqs] using Ev.seq hloop hpop
  have htail2 : Ev main (seqs [.ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
      (.set foldList_rL Glyph.cons), .loop foldList_rL Glyph.cons (foldList_body3 q),
      .pop (2 : Stk) foldList_rS]) Z1 Z
      (2 + (xs.length * (16 * (L + 1) + c + 4) + xs.length + 1 + 1)) :=
    Ev.seqs_cons hite htail
  have htot : Ev main (seqs [.peek (2 : Stk) foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons),
      .loop foldList_rL Glyph.cons (foldList_body3 q), .pop (2 : Stk) foldList_rS]) s Z
      (1 + (2 + (xs.length * (16 * (L + 1) + c + 4) + xs.length + 1 + 1))) :=
    Ev.seqs_cons hpeek htail2
  have hmain : Ev main (foldList_prog3 q) s Z
      (1 + (2 + (xs.length * (16 * (L + 1) + c + 4) + xs.length + 1 + 1))) := by
    simpa [foldList_prog3] using htot
  exact ⟨Z, hmain.mono (le_of_eq (by ring)), hZ0, hZ2, hZfr⟩

end Work.Kernel
