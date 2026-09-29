import Mathlib
import Submission.Work.Transform.pwBase
import Submission.Work.Transform.pwMaxDefs
import Submission.Work.Transform.pwMaxLoop
import Submission.Work.Transform.pwMaxStep
import Submission.Work.Transform.pwMaxScr

namespace Work.Transform

/-- The "parameter word" max phase: given the encoding of the list `intList ms` of positive
integers (a `cons`-chain of `Val.int` encodings ending in `nil`) above the frame marker `gM` on stack
`src`, and an empty running maximum (just the marker `gM`, above the tail `mxTail`) on stack `mx`,
compute the bits of `lmax ms` (least significant first, as `Computability.encodeNat (lmax ms)`) above
the marker and the tail on `mx`.

Sketch of a correct implementation (what matters is the cost: every element must be handled in time
proportional to its *own* bit length, never to the length of the current maximum).  For each element
`x = Val.int t` of the list:
* pop the leading `cons` glyph and run `Pw.storeMag src sp ds rA rB`, which pops the sign of `x`
  (onto `ds`) and moves the bits of `x` (most significant first) above a fresh `gM` onto `sp`,
  consuming `x`'s encoding from `src` up to its `iend`;
* `Pw.copyMarked2 sp spc tmp rA rB` (keeping `sp`), then `Pw.revMarked spc sA rA rB` to get the bits
  least significant first above a fresh `gM` on `sA`, then compare `t` with the current maximum by a
  *buffered* lockstep scan of `sA` against `mx` (buffers `bA`, `bB`): this costs
  `O (min (size t) (size m) + 1)`;
* if the flag is `gGt` (`t` strictly larger) then `t` becomes the new maximum: drain `mx` and the
  buffers and move the bits from `sp` to `mx` with `Pw.tLoop sp gM mx r` (this reverses the
  most-significant-first stored bits into the least-significant-first order wanted on `mx`);
  otherwise `t` loses: push the consumed prefix of the maximum back from the buffer `bB` (this
  restores `mx` exactly, and the remaining bits of the old maximum are the ones still on `mx`);
* drain the leftover on `sA`, the buffers and the `gM`s they carry, pop the sign glyph from `ds`, and
  pop the `gM` markers of `sp`/`spc`, so that all scratch stacks are restored at the end. -/
theorem pwMaxPhase (src mx : HvdH.Stk) : src ≠ mx → ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (ms : List ℕ) (below mxTail : List HvdH.Glyph) (s : HvdH.State),
      (∀ t ∈ ms, 0 < t) →
      s.stk src = (HvdH.intList ms).enc ++ Work.Transform.Pw.gM :: below →
      s.stk mx = Work.Transform.Pw.gM :: mxTail →
      ∃ s' n, HvdH.Eval main prog s s' n ∧ n ≤ K * (ms.sum + 1) ∧
        s'.stk src = Work.Transform.Pw.gM :: below ∧
        s'.stk mx = (Computability.encodeNat (HvdH.lmax ms)).map HvdH.Glyph.bit
            ++ Work.Transform.Pw.gM :: mxTail ∧
        (∀ j : HvdH.Stk, j ≠ src → j ≠ mx → s'.stk j = s.stk j) := by
  intro h
  obtain ⟨S⟩ := pwMaxScr src mx h
  obtain ⟨elem, Ke, helem⟩ := Pw.pwMaxStep src mx h S
  obtain ⟨K, hK⟩ := Pw.pwMaxLoop src mx h elem Ke helem
  refine ⟨Pw.loopOf elem src, 2 * K, ?_⟩
  intro main ms below mxTail s hpos hsrc hmx
  have hmx' : s.stk mx = (Computability.encodeNat 0).map HvdH.Glyph.bit
      ++ Pw.gM :: mxTail := by
    rw [Pw.mx_encodeNat_zero]; simpa using hmx
  obtain ⟨s', n, e, hn, h1, h2, h3⟩ :=
    hK main ms 0 below mxTail s hpos hsrc hmx'
  refine ⟨s', n, e, ?_, h1, ?_, h3⟩
  · -- cost: `ms.length ≤ ms.sum`
    have hL : ms.length ≤ ms.sum := Pw.mx_length_le_sum ms hpos
    have hle : K * (ms.sum + ms.length + 2) ≤ 2 * K * (ms.sum + 1) := by
      have h2'' : ms.sum + ms.length + 2 ≤ 2 * (ms.sum + 1) := by omega
      calc K * (ms.sum + ms.length + 2) ≤ K * (2 * (ms.sum + 1)) :=
            Nat.mul_le_mul_left K h2''
        _ = 2 * K * (ms.sum + 1) := by ring
    exact le_trans hn hle
  · rw [h2, max_eq_right (Nat.zero_le (HvdH.lmax ms))]

end Work.Transform
