import Mathlib
import Submission.Work.Kernel.foldListDefs
import Submission.Work.Kernel.foldList_p1_body_raw

namespace Work.Kernel

open HvdH
open Work.Layout

/-! ## Helpers for phase 1 of `Work.Kernel.foldList`

These are the invariant bookkeeping lemmas for `foldList_prog1`; the raw `Ev` statement for a single
iteration of the body is `Work.Kernel.foldList_p1_body_raw` (proved in
`Submission/Work/Kernel/foldList_p1_body_raw.lean`).
-/

/-- Unfolding of the encoding of `ofList (x :: rest)`: the leading `cons` of the list encoding, then
the encoding of the exposed element, then the encoding of the rest on top of the accumulator. -/
theorem foldList_p1_encs_ofList_cons (x : Val) (rest acc : List Val) (R : List Glyph) :
    encs (ofList (x :: rest) :: acc) ++ R
      = Glyph.cons :: (x.enc ++ (encs (ofList rest :: acc) ++ R)) := by
  simp [ofList, encs, Val.enc, List.append_assoc]

/-- The invariant `foldList_P1` holds after the initial `peek` of `foldList_prog1`. -/
theorem foldList_p1_init (xs acc : List Val) (R A0 : List Glyph) (s : State)
    (hs0 : s.stk 0 = encs (ofList xs :: acc) ++ R) (hs1 : s.stk 1 = foldList_tag :: A0) :
    foldList_P1 xs acc R A0 s 0
      ⟨Function.update s.reg foldList_rG ((s.stk 0).headD Glyph.eos), s.stk⟩ := by
  unfold foldList_P1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hs0
  · show s.stk 1 = encs ((xs.take 0).reverse) ++ foldList_tag :: A0
    rw [hs1]; simp [encs]
  · intro k _ _; rfl
  · simpa [hs0] using foldList_headD_ofList xs acc R

/-- Once all of `xs` has been peeled off, the test register no longer holds `cons`, so the loop of
`foldList_prog1` stops. -/
theorem foldList_p1_stop (xs acc : List Val) (R A0 : List Glyph) (s X : State)
    (hX : foldList_P1 xs acc R A0 s xs.length X) : X.reg foldList_rG ≠ Glyph.cons := by
  obtain ⟨-, -, -, hr⟩ := hX
  rw [hr, foldList_drop_length]
  decide

/-- One iteration of the loop of `foldList_prog1`: the test succeeds, the body runs to the next
invariant state within the uniform budget `16 * (L + 1) + 2`. -/
theorem foldList_p1_step (main : Cmd) (xs acc : List Val) (R A0 : List Glyph) (s X : State)
    (L i : ℕ) (hL : ∀ x ∈ xs, vsz x ≤ L) (hi : i < xs.length)
    (hX : foldList_P1 xs acc R A0 s i X) :
    X.reg foldList_rG = Glyph.cons ∧
      ∃ X', foldList_P1 xs acc R A0 s (i + 1) X' ∧
        Ev main foldList_body1 X X' (16 * (L + 1) + 2) := by
  obtain ⟨hX0, hX1, hXf, hXr⟩ := hX
  have hdrop : xs.drop i = xs.getD i Val.nil :: xs.drop (i + 1) :=
    foldList_drop_eq_getD_cons xs i hi
  have hne : xs.drop i ≠ [] := by
    intro h
    have hlen : (xs.drop i).length = 0 := by rw [h]; rfl
    rw [List.length_drop] at hlen
    omega
  have hxmem : xs.getD i Val.nil ∈ xs := foldList_getD_mem hi
  have hxv : vsz (xs.getD i Val.nil) ≤ L := hL _ hxmem
  have hX0' : X.stk 0 = Glyph.cons :: ((xs.getD i Val.nil).enc ++
      (encs (ofList (xs.drop (i + 1)) :: acc) ++ R)) := by
    rw [hX0, hdrop, foldList_p1_encs_ofList_cons]
  obtain ⟨X', hEv, h0', h1', hr', hf'⟩ :=
    foldList_p1_body_raw main X (xs.getD i Val.nil) (xs.drop (i + 1)) acc R (X.stk 1) L
      hxv hX0' rfl
  refine ⟨?_, X', ?_, hEv⟩
  · simpa [hne] using hXr
  · unfold foldList_P1
    rw [foldList_take_reverse_succ xs i hi]
    refine ⟨h0', ?_, ?_, hr'⟩
    · rw [h1', hX1, encs_cons]
      simp only [List.append_assoc]
    · intro k hk0 hk1; rw [hf' k hk0 hk1, hXf k hk0 hk1]

/-- **Phase 1 of `Work.Kernel.foldList`.**  `Work.Kernel.foldList_prog1` (defined in
`Submission/Work/Kernel/foldListDefs.lean`, along with `foldList_tag`, `foldList_rG`, `foldList_rS`,
`foldList_P1`, `foldList_loopEv`, `foldList_headD_ofList`, `foldList_drop_eq_getD_cons`,
`foldList_take_reverse_succ`, `foldList_getD_mem`) is the program
`seqs [.peek 0 foldList_rG, .loop foldList_rG Glyph.cons foldList_body1, .pop 0 foldList_rS]` with
`foldList_body1 = seqs [.pop 0 foldList_rS, Work.Layout.mvVal 0 1 3 4, .peek 0 foldList_rG]`.

It dismantles the `cons`-chain `ofList xs` sitting on top of `acc` on stack `0`: each iteration drops
the leading `Glyph.cons` of the remaining list's encoding, moves the exposed element (`mvVal`, cost
`≤ 16 * (vsz x + 1)`, scratch stacks `3`, `4` restored) to stack `1`, and peeks the new leading glyph
of stack `0` — `Glyph.cons` exactly while the remaining list is nonempty, `Glyph.nil` once it is
`[]`; the trailing `pop` removes that `nil`.  Loop invariant = `foldList_P1`, unrolled with
`foldList_loopEv` (uniform per-iteration budget `16 * (L + 1) + 2`), then `Ev.seq`/`Ev.mono`.
Helpers in this file must be named with the prefix `foldList_p1_`. -/
theorem foldList_phase1 (main : HvdH.Cmd) (xs acc : List HvdH.Val) (R : List HvdH.Glyph)
    (A0 : List HvdH.Glyph) (s : HvdH.State) (L : ℕ)
    (hL : ∀ x ∈ xs, HvdH.vsz x ≤ L)
    (hs0 : s.stk 0 = HvdH.encs (HvdH.ofList xs :: acc) ++ R)
    (hs1 : s.stk 1 = Work.Kernel.foldList_tag :: A0) :
    ∃ s', Work.Layout.Ev main Work.Kernel.foldList_prog1 s s'
        (xs.length * (16 * (L + 1) + 4) + 4) ∧
      s'.stk 0 = HvdH.encs acc ++ R ∧
      s'.stk 1 = HvdH.encs xs.reverse ++ Work.Kernel.foldList_tag :: A0 ∧
      (∀ k, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  -- initial `peek`: it loads the leading glyph of `ofList xs` and does not move any stack
  have hpeek : Ev main (.peek (0 : Stk) foldList_rG) s
      ⟨Function.update s.reg foldList_rG ((s.stk 0).headD Glyph.eos), s.stk⟩ 1 :=
    ev_peek' main 0 foldList_rG s.reg s.stk
  -- the loop, unrolled along `foldList_P1` with the uniform budget `16 * (L + 1) + 2`
  obtain ⟨sL, hLev, hLP⟩ := foldList_loopEv main foldList_rG Glyph.cons foldList_body1 xs.length
    (foldList_P1 xs acc R A0 s) (16 * (L + 1) + 2)
    ⟨Function.update s.reg foldList_rG ((s.stk 0).headD Glyph.eos), s.stk⟩
    (foldList_p1_init xs acc R A0 s hs0 hs1)
    (fun i hi X hX => foldList_p1_step main xs acc R A0 s X L i hL hi hX)
    (fun X hX => foldList_p1_stop xs acc R A0 s X hX)
  obtain ⟨hL0, hL1, hLf, -⟩ := hLP
  -- the surviving `nil` on top of the accumulator
  have hL0' : sL.stk 0 = Glyph.nil :: (encs acc ++ R) := by
    rw [hL0, foldList_drop_length]
    simp [ofList, encs, Val.enc]
  -- trailing `pop`, which removes that `nil`
  have hpop : Ev main (.pop (0 : Stk) foldList_rS) sL
      ⟨Function.update sL.reg foldList_rS ((sL.stk 0).headD Glyph.eos),
        Function.update sL.stk 0 (sL.stk 0).tail⟩ 1 :=
    ev_pop' main 0 foldList_rS sL.reg sL.stk
  have hfull : Ev main foldList_prog1 s
      ⟨Function.update sL.reg foldList_rS ((sL.stk 0).headD Glyph.eos),
        Function.update sL.stk 0 (sL.stk 0).tail⟩
      (1 + ((xs.length * (16 * (L + 1) + 2) + xs.length + 1) + 1)) := by
    unfold foldList_prog1
    simp only [seqs]
    exact Ev.seq hpeek (Ev.seq hLev hpop)
  refine ⟨_, hfull.mono ?_, ?_, ?_, ?_⟩
  · nlinarith
  · show (Function.update sL.stk 0 (sL.stk 0).tail) 0 = encs acc ++ R
    rw [Function.update_self, hL0']
    rfl
  · show (Function.update sL.stk 0 (sL.stk 0).tail) 1 = encs xs.reverse ++ foldList_tag :: A0
    rw [Function.update_of_ne (by decide : (1 : Stk) ≠ 0), hL1, foldList_take_reverse_length]
  · intro k hk0 hk1
    show (Function.update sL.stk 0 (sL.stk 0).tail) k = s.stk k
    rw [Function.update_of_ne hk0, hLf k hk0 hk1]

end Work.Kernel
