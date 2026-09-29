import Mathlib
import Submission.Work.Layout.Take.Basic
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.Take.walkBody_cons
import Submission.Work.Layout.Take.walkBody_nil

/-!
# `walkProg_x` walks the `cons`-chain `ofList xs` on stack `0`

`walkProg_x` (`Submission/Work/Layout/Take/Defs.lean`) is the second phase of `LayoutLib.take`
/`drop`: it walks the list `ofList xs` on stack `0`, moving every element to `sS` (so the first
element ends deepest and `sS` shows `xs.reverse`) and pushing one unary unit `gU` per element on
`sD`; the list and its `nil` terminator are consumed.  The frame markers sitting below the data on
`sS`/`sD` are untouched, and the scratch stacks `sX`, `sY` of `mvVal` are restored, so the phase can
be iterated / chained.

The proof is a straightforward induction on `xs` (`walk_loop`), each step being one iteration of
`walkBody` (`walkBody_cons`, `walkBody_nil`) using the full-strength mover
`Work.Layout.mvVal_ev_full`, which additionally records that its scratch stacks are restored.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Layout.Take

open HvdH
open Work.Layout

theorem enc_ofList_flatMap (vs : List Val) :
    (ofList vs).enc = List.flatMap (fun v => Glyph.cons :: v.enc) vs ++ [Glyph.nil] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      show (Val.cons v (ofList vs)).enc = _
      rw [Val.enc, ih, List.flatMap_cons]
      simp [List.append_assoc]

theorem sum_map_affine (xs : List Val) :
    (xs.map (fun v => 16 * vsz v + 22)).sum = 16 * (xs.map vsz).sum + 22 * xs.length := by
  induction xs with
  | nil => simp
  | cons v t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem walk_loop (main : Cmd) (xs : List Val) (L : List Glyph)
    (g : Reg → Glyph) (X : Stk → List Glyph)
    (h0 : X 0 = List.flatMap (fun v => Glyph.cons :: v.enc) xs ++ (Glyph.nil :: L))
    (hg : g rG = gCont_x) :
    ∃ s', loopRuns main rG gCont_x walkBody (xs.length + 1) ⟨g, X⟩ s'
        (4 + (xs.map (fun v => 16 * vsz v + 22)).sum) ∧
      s'.stk 0 = L ∧ s'.stk sS = encs xs.reverse ++ X sS ∧
      s'.stk sD = List.replicate xs.length gU ++ X sD ∧
      s'.reg rG = Glyph.eos ∧
      (∀ j, j ≠ 0 → j ≠ sS → j ≠ sD → s'.stk j = X j) := by
  induction xs generalizing g X with
  | nil =>
      have h0' : X 0 = Glyph.nil :: L := by simpa using h0
      obtain ⟨s', n, hev, hn, hstk, hreg, hfr⟩ := walkBody_nil main L g X h0'
      have hruns : loopRuns main rG gCont_x walkBody (([] : List Val).length + 1) ⟨g, X⟩ s'
          (4 + (([] : List Val).map (fun v => 16 * vsz v + 22)).sum) := by
        simpa using loopRuns.one hg (hev.mono hn)
      refine ⟨s', hruns, hstk, ?_, ?_, hreg, ?_⟩
      · simpa [Work.Kernel.encs_nil, List.reverse_nil] using hfr sS (by decide)
      · simpa using hfr sD (by decide)
      · intro j hj0 hjS hjD; exact hfr j hj0
  | cons v t ih =>
      have h0' : X 0 = Glyph.cons :: (v.enc ++ (List.flatMap (fun v => Glyph.cons :: v.enc) t
          ++ (Glyph.nil :: L))) := by
        rw [h0, List.flatMap_cons, List.append_assoc, List.cons_append]
      obtain ⟨s1, n1, hev1, hn1, hstk1, hsS1, hsD1, hreg1, hfr1⟩ :=
        walkBody_cons main v (List.flatMap (fun v => Glyph.cons :: v.enc) t
          ++ (Glyph.nil :: L)) g X h0' hg
      obtain ⟨s2, hrun2, hstk2, hsS2, hsD2, hreg2, hfr2⟩ := ih s1.reg s1.stk hstk1 hreg1
      have hC : (16 * (vsz v + 1) + 5) + (4 + (t.map (fun v => 16 * vsz v + 22)).sum) + 1 ≤
          4 + ((v :: t).map (fun v => 16 * vsz v + 22)).sum := by
        simp only [List.map_cons, List.sum_cons]; omega
      have hruns : loopRuns main rG gCont_x walkBody ((v :: t).length + 1) ⟨g, X⟩ s2
          (4 + ((v :: t).map (fun v => 16 * vsz v + 22)).sum) :=
        loopRuns.succ' hg (hev1.mono hn1) hrun2 hC
      refine ⟨s2, hruns, hstk2, ?_, ?_, hreg2, ?_⟩
      · rw [hsS2, hsS1, List.reverse_cons, Work.Kernel.encs_append, Work.Kernel.encs_cons, Work.Kernel.encs_nil]
        simp only [List.append_assoc, List.append_nil]
      · rw [hsD2, hsD1, List.length_cons, List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      · intro j hj0 hjS hjD
        rw [hfr2 j hj0 hjS hjD, hfr1 j hj0 hjS hjD]

/-- `walkProg_x` (`Submission/Work/Layout/Take/Defs.lean`) walks the `cons`-chain `ofList xs` on
stack `0`, moving every element to `sS` (the first element of the list ends deepest, so `sS` shows
`xs.reverse`) and pushing one unary unit `gU` per element on `sD`; the list (and its `nil`
terminator) is consumed and the frame markers of `sS` and `sD` (which sit below the data) are
untouched.  `HvdH.encs ys` is the concatenation of the encodings of the values in `ys`.

Useful: `Work.Layout.mvVal_ev` (in `Submission/Work/Layout/Move.lean`) moves one value from stack
`0` to `sS`; note that it restores its own scratch stacks `sX`, `sY` only through `mvA_ev`/`mvB_ev`,
so you may have to prove a stronger variant of it (as the proof of `mvVal_ev` itself does).
Also `HvdH.encs_cons`, `HvdH.encs_append`, `Work.Layout.one_le_vsz`, the `Ev` primitives of
`Submission/Work/Layout/Base.lean`. -/
theorem walk_ev (main : HvdH.Cmd) (xs : List HvdH.Val) (L : List HvdH.Glyph)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = (HvdH.ofList xs).enc ++ L) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.walkProg_x ⟨g, X⟩ s' n ∧
      n ≤ 30 * (xs.length + (xs.map HvdH.vsz).sum + 1) ∧
      s'.stk 0 = L ∧ s'.stk Work.Layout.sS = HvdH.encs xs.reverse ++ X Work.Layout.sS ∧
      s'.stk Work.Layout.sD = List.replicate xs.length Work.Layout.gU ++ X Work.Layout.sD ∧
      (∀ j, j ≠ 0 → j ≠ Work.Layout.sS → j ≠ Work.Layout.sD → s'.stk j = X j) := by
  have h0' : X 0 = List.flatMap (fun v => Glyph.cons :: v.enc) xs ++ (Glyph.nil :: L) := by
    rw [h0, enc_ofList_flatMap]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨s₁, hrun, hstk, hsS, hsD, hreg, hfr⟩ :=
    walk_loop main xs L (Function.update g rG gCont_x) X h0' (Function.update_self rG gCont_x g)
  have hloop : Ev main (.loop rG gCont_x walkBody) ⟨Function.update g rG gCont_x, X⟩ s₁
      (4 + (xs.map (fun v => 16 * vsz v + 22)).sum + 1) :=
    loopRuns.eval hrun (by rw [hreg]; decide)
  have hset : Ev main (.set rG gCont_x) ⟨g, X⟩ ⟨Function.update g rG gCont_x, X⟩ 1 :=
    ev_set' main rG gCont_x g X
  have hmain : Ev main walkProg_x ⟨g, X⟩ s₁
      (1 + (4 + (xs.map (fun v => 16 * vsz v + 22)).sum + 1)) := by
    unfold walkProg_x
    simp only [seqs]
    exact Ev.seq' hset hloop (by omega)
  refine ⟨s₁, _, hmain, ?_, hstk, hsS, hsD, hfr⟩
  · rw [sum_map_affine]
    omega

end Work.Layout.Take
