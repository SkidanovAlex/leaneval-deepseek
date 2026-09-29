import Submission.Work.IntLib.SqrtGcd.sqrtSetupJunk
import Submission.Work.IntLib.SqrtGcd.sqrtFinishEval
import Submission.Work.IntLib.SqrtGcd.sqrtLoopLen
import Submission.Work.IntLib.SqrtGcd.evalStkLen

/-!
# The square-root word

`Work.IntLib.SG.sqrtWord` : `int z :: rest ↦ int (Nat.sqrt z.toNat) :: rest` for `0 ≤ z`, at cost
`K · isz z ^ 2`.  It runs the three phases of `SG.sqrtProg`

* `sqrtSetup` — parse the magnitude of the input onto the (padded, even-length) radicand region
  `sA` (`sqrtSetupJunk`),
* `sqrtLoop`  — the restoring bit-pair square root, leaving the root (least significant first) on
  `sC` and the leftover remainder on `sB` (`SqrtGcd.Len.sqrtLoopEvalLen`),
* `sqrtFinish ;; sqrtClean` — emit the root as a value on stack 0 and restore the scratch stacks
  (`sqrtFinishEvalGen`).

The *sizes* of the data produced by the first two phases are not part of their statements; they are
recovered from their costs by `Eval.stk_length_le` (`evalStkLen.lean`): a run of cost `m` adds at
most `m` glyphs to any stack, and each phase of this program pushes its output above a fresh marker,
so the radicand region holds `≤ m₁ + 1` bits and the root/remainder regions `≤ m₂` bits each.  With
the (quadratic) cost bounds of the phases this gives the quadratic bound with the huge-but-finite
constant `K = 10^14`; no effort is spent on a tight constant.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

theorem sqrtWord :
    ∃ (p : Cmd) (K : ℕ), ∀ main, UnOp main p (fun a => 0 ≤ a)
      (fun a => (Nat.sqrt a.toNat : ℤ)) (fun a => K * isz a ^ 2) := by
  refine ⟨sqrtProg, 100000000000000, ?_⟩
  intro main vs hpre s R hR
  obtain ⟨z, rest, rfl, hz⟩ := hpre
  have hR' : s.stk 0 = (Val.int z).enc ++ (encs rest ++ R) := by
    rw [hR, Work.Kernel.encs_cons, List.append_assoc]
  -- ## the three phases
  obtain ⟨s1, m1, hev1, hm1, ⟨bs, hA1, hbslen, hbsval⟩, h01, hB1, hC1, hP1, hQ1, hR1, hS1,
    hfr1⟩ :=
    Work.IntLib.SqrtGcd.sqrtSetupJunk main z hz (encs rest ++ R) s hR'
  obtain ⟨s2, m2, hev2, hm2, hA2, ⟨rl, hC2, hval2⟩, ⟨bl, hB2⟩, hP2, hQ2, hR2, hS2, hfr2⟩ :=
    Work.IntLib.SqrtGcd.Len.sqrtLoopEvalLen main bs (s.stk sA) (s.stk sB) (s.stk sC)
      (s.stk sP) (s.stk sQ) (s.stk sR) (s.stk sS) s1 hA1 hB1 hC1 hP1 hQ1 hR1 hS1 hbslen
  have h02 : s2.stk 0 = encs rest ++ R :=
    (hfr2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h01
  obtain ⟨s3, m3, hev3, hm3, h03, hA3, hB3, hC3, hP3, hQ3, hR3, hS3, hfr3⟩ :=
    Work.IntLib.SqrtGcd.sqrtFinishEvalGen main rl bl (encs rest ++ R) (s.stk sA) (s.stk sB)
      (s.stk sC) (s.stk sP) (s.stk sQ) (s.stk sR) (s.stk sS) s2 h02 hA2 hB2 hC2 hP2 hQ2 hR2 hS2
  refine ⟨.int (Nat.sqrt z.toNat) :: rest, s3, m1 + (m2 + m3), ⟨z, rest, rfl, rfl⟩,
    Eval.seq hev1 (Eval.seq hev2 hev3), ?_, ?_, ?_⟩
  · -- ## cost: the sizes of the data regions are bounded by the costs of the phases
    have hn : 2 ≤ isz z := by rw [isz_eq]; omega
    have hnn : 4 ≤ isz z * isz z := Nat.mul_le_mul hn hn
    have hsq : isz z ≤ isz z * isz z := by nlinarith [hn, hnn]
    have hbs : bs.length + 1 ≤ m1 := by
      have hlen := Work.IntLib.SqrtGcd.Eval.stk_length_le hev1 sA
      rw [hA1] at hlen
      simp only [List.length_append, List.length_map, List.length_cons] at hlen
      omega
    have hbs1 : bs.length + 1 ≤ 101 + 100 * isz z := by omega
    have hbs2 : (bs.length + 1) * (bs.length + 1)
        ≤ (101 + 100 * isz z) * (101 + 100 * isz z) := Nat.mul_le_mul hbs1 hbs1
    have hm2' : m2 ≤ 100000 * (101 + 100 * isz z) * (101 + 100 * isz z) + 100000 := by
      nlinarith [hm2, hbs2]
    have hrl : rl.length ≤ m2 :=
      Work.IntLib.SqrtGcd.length_of_region_le_cost hev2 sC (Glyph.mk sC) (s.stk sC) rl hC1 hC2
    have hbl : bl.length ≤ m2 :=
      Work.IntLib.SqrtGcd.length_of_region_le_cost hev2 sB (Glyph.mk sB) (s.stk sB) bl hB1 hB2
    have hm3' : m3 ≤ 100 + (2 * m2 + 1) * 100 := by nlinarith [hm3, hrl, hbl]
    have hcost : m1 + (m2 + m3) ≤ 100000000000000 * isz z ^ 2 := by
      nlinarith [hm1, hm2', hm3', hn, hnn, hsq]
    simpa only [unCost, pow_two] using hcost
  · -- ## the emitted value is the square root
    have hsqrt : (ofBits rl : ℕ) = Nat.sqrt z.toNat := by rw [hval2, hbsval]
    have hV : (Val.int ((ofBits rl : ℕ) : ℤ)).enc = (Val.int (Nat.sqrt z.toNat : ℤ)).enc := by
      rw [hsqrt]
    rw [h03, Work.Kernel.encs_cons, List.append_assoc, hV]
  · -- ## the frame
    intro k hk
    by_cases h1 : k = sA
    · rw [h1, hA3]
    by_cases h2 : k = sB
    · rw [h2, hB3]
    by_cases h3 : k = sC
    · rw [h3, hC3]
    by_cases h4 : k = sP
    · rw [h4, hP3]
    by_cases h5 : k = sQ
    · rw [h5, hQ3]
    by_cases h6 : k = sR
    · rw [h6, hR3]
    by_cases h7 : k = sS
    · rw [h7, hS3]
    · exact (hfr3 k hk h1 h2 h3 h4 h5 h6 h7).trans
        ((hfr2 k h1 h2 h3 h4 h5 h6 h7).trans (hfr1 k hk h1 h2 h3 h4 h5 h6 h7))

end SG
end Work.IntLib
