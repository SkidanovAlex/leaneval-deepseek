import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.loopCombFixedDefs

/-!
# Kernel: the `loop` combinator with the auxiliary hypothesis `1 ≤ m` (historical)

NOTE (v2/v3): the current `KernelLib.loop` field keeps the bound `(m + 1) * (c + K) + K` and has no
hypothesis on `m`; it is proved in `Submission/Work/Kernel/loopV2.lean`, which instantiates this file
at `m + 1` and weakens the hypothesis (the program `Work.Kernel.loopCombFixed_comb` here is the one
that `loopV2` uses).  This file remains as the reusable auxiliary result.

See `Submission/Work/Kernel/loopRefute.lean` (historical only) for the refutation of the *v1* text.

Here we build the repaired combinator `loopCombFixed_comb` (program in
`Submission/Work/Kernel/loopCombFixedDefs.lean`) and prove its spec by strong induction on the
number of remaining rounds: a body run at index `i` either stops (flag `int 0`, so the output
satisfies `F`) or continues (flag `int 1`, yielding `I (i+1)`, which the hypothesis only allows
when `i + 1 < m`).  Hence the chain `I 0 → I 1 → …` can never pass index `m - 1`, and at most `m`
rounds are run.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-! ## Elementary facts about the canonical result states -/

@[simp] theorem loopCombFixed_tPop_stk0 (s : State) (r : Reg) :
    (State.tPop s 0 r).stk 0 = (s.stk 0).tail := by simp [State.tPop]

@[simp] theorem loopCombFixed_tPop_reg (s : State) (r : Reg) :
    (State.tPop s 0 r).reg r = (s.stk 0).headD Glyph.eos := by simp [State.tPop]

theorem loopCombFixed_tPop_stk_ne (s : State) (r : Reg) {k : Stk} (hk : k ≠ 0) :
    (State.tPop s 0 r).stk k = s.stk k := by simp [State.tPop, hk]

@[simp] theorem loopCombFixed_tSet_reg (s : State) (r : Reg) (g : Glyph) :
    (State.tSet s r g).reg r = g := by simp [State.tSet]

@[simp] theorem loopCombFixed_tSet_stk (s : State) (r : Reg) (g : Glyph) (k : Stk) :
    (State.tSet s r g).stk k = s.stk k := rfl

/-! ## One round of the do-while -/

theorem loopCombFixed_bodySpec_local (main q : Cmd) (I : ℕ → List Val → Prop)
    (F : List Val → Prop) (c m i : ℕ) (vs : List Val) (R : List Glyph) (s0 : State)
    (hq : ∀ (j : ℕ) (w : List Val), I j w → WordR main q (fun u => u = w)
      (fun _ out => ∃ t, (out = Val.int 0 :: t ∧ F t) ∨
        (out = Val.int 1 :: t ∧ I (j + 1) t ∧ j + 1 < m)) (fun _ => c))
    (hI : I i vs) (hs0 : s0.stk 0 = encs vs ++ R) :
    ∃ (out : List Val) (s' : State) (n : ℕ),
      Eval main (loopCombFixed_body q) s0 s' n ∧ n ≤ c + 5 ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = s0.stk k) ∧
      ((s'.reg 0 ≠ Glyph.eos ∧ s'.stk 0 = encs out ++ R ∧ F out) ∨
       (s'.reg 0 = Glyph.eos ∧ s'.stk 0 = encs out ++ R ∧ I (i + 1) out ∧ i + 1 < m)) := by
  obtain ⟨out0, sA, nA, hPost, hEvA, hnA, hstkA, hothA⟩ := hq i vs hI vs rfl s0 R hs0
  rcases hPost with ⟨t, ⟨hout0, hFt⟩ | ⟨hout1, hIt, hlt⟩⟩
  · -- the flag is `int 0`: pop its two glyphs and stop
    have hA : sA.stk 0 = [Glyph.pos, Glyph.iend] ++ encs t ++ R := by rw [hstkA, hout0]; rfl
    have h1stk : (State.tPop sA 0 1).stk 0 = [Glyph.iend] ++ encs t ++ R := by
      rw [loopCombFixed_tPop_stk0, hA]; rfl
    have h2stk : (State.tPop (State.tPop sA 0 1) 0 1).stk 0 = encs t ++ R := by
      rw [loopCombFixed_tPop_stk0, h1stk]; rfl
    have h2reg : (State.tPop (State.tPop sA 0 1) 0 1).reg 1 = Glyph.iend := by
      rw [loopCombFixed_tPop_reg, h1stk]; rfl
    refine ⟨t, State.tSet (State.tPop (State.tPop sA 0 1) 0 1) 0 Glyph.iend, nA + 4,
      ?_, ?_, ?_, Or.inl ⟨?_, ?_, hFt⟩⟩
    · refine eval_seq hEvA ?_
      exact eval_seq (eval_pop main 0 1 sA)
        (eval_seq (eval_pop main 0 1 (State.tPop sA 0 1))
          (eval_iteT h2reg (eval_set main 0 Glyph.iend (State.tPop (State.tPop sA 0 1) 0 1))))
    · have h1 : nA ≤ c := hnA; omega
    · intro k hk
      rw [loopCombFixed_tSet_stk, loopCombFixed_tPop_stk_ne (State.tPop sA 0 1) 1 hk,
        loopCombFixed_tPop_stk_ne sA 1 hk]
      exact hothA k hk
    · rw [loopCombFixed_tSet_reg]; decide
    · rw [loopCombFixed_tSet_stk]; exact h2stk
  · -- the flag is `int 1`: pop its three glyphs and continue
    have hA : sA.stk 0 = [Glyph.pos, Glyph.bit true, Glyph.iend] ++ encs t ++ R := by
      rw [hstkA, hout1]; rfl
    have h1stk : (State.tPop sA 0 1).stk 0 = [Glyph.bit true, Glyph.iend] ++ encs t ++ R := by
      rw [loopCombFixed_tPop_stk0, hA]; rfl
    have h2stk : (State.tPop (State.tPop sA 0 1) 0 1).stk 0 = [Glyph.iend] ++ encs t ++ R := by
      rw [loopCombFixed_tPop_stk0, h1stk]; rfl
    have h3stk : (State.tPop (State.tPop (State.tPop sA 0 1) 0 1) 0 1).stk 0 = encs t ++ R := by
      rw [loopCombFixed_tPop_stk0, h2stk]; rfl
    have h2reg : (State.tPop (State.tPop sA 0 1) 0 1).reg 1 = Glyph.bit true := by
      rw [loopCombFixed_tPop_reg, h1stk]; rfl
    have hne : (State.tPop (State.tPop sA 0 1) 0 1).reg 1 ≠ Glyph.iend := by
      rw [h2reg]; decide
    refine ⟨t, State.tSet (State.tPop (State.tPop (State.tPop sA 0 1) 0 1) 0 1) 0 Glyph.eos,
      nA + 5, ?_, ?_, ?_, Or.inr ⟨?_, ?_, hIt, hlt⟩⟩
    · refine eval_seq hEvA ?_
      exact eval_seq (eval_pop main 0 1 sA)
        (eval_seq (eval_pop main 0 1 (State.tPop sA 0 1))
          (eval_iteF hne (eval_seq
            (eval_pop main 0 1 (State.tPop (State.tPop sA 0 1) 0 1))
            (eval_set main 0 Glyph.eos
              (State.tPop (State.tPop (State.tPop sA 0 1) 0 1) 0 1)))))
    · have h1 : nA ≤ c := hnA; omega
    · intro k hk
      rw [loopCombFixed_tSet_stk, loopCombFixed_tPop_stk_ne _ 1 hk,
        loopCombFixed_tPop_stk_ne _ 1 hk, loopCombFixed_tPop_stk_ne sA 1 hk]
      exact hothA k hk
    · rw [loopCombFixed_tSet_reg]
    · rw [loopCombFixed_tSet_stk]; exact h3stk

/-! ## The combinator -/

theorem loopCombFixed : ∃ (comb : HvdH.Cmd → HvdH.Cmd) (K : ℕ),
    ∀ (main q : HvdH.Cmd) (I : ℕ → List HvdH.Val → Prop) (F : List HvdH.Val → Prop) (c m : ℕ),
      1 ≤ m →
      (∀ i vs, I i vs → HvdH.WordR main q (fun w => w = vs)
        (fun _ out => ∃ vs', (out = HvdH.Val.int 0 :: vs' ∧ F vs') ∨
          (out = HvdH.Val.int 1 :: vs' ∧ I (i + 1) vs' ∧ i + 1 < m)) (fun _ => c)) →
      HvdH.WordR main (comb q) (I 0) (fun _ out => F out) (fun _ => m * (c + K) + K) := by
  refine ⟨loopCombFixed_comb, 6, ?_⟩
  intro main q I F c m hle hq vs hI s R hR
  set sE : State := s.updReg 0 Glyph.eos with hsE
  have hrE : sE.reg 0 = Glyph.eos := by rw [hsE]; simp
  have hsE0 : sE.stk 0 = encs vs ++ R := by rw [hsE]; simpa using hR
  have hlt0 : (0 : ℕ) < m := by omega
  have key : ∀ (n i : ℕ) (vs : List Val) (R : List Glyph) (s0 : State),
      m - i ≤ n → i < m → s0.reg 0 = Glyph.eos → I i vs → s0.stk 0 = encs vs ++ R →
      ∃ (out : List Val) (s' : State) (nn : ℕ),
        F out ∧ Eval main (Cmd.loop 0 Glyph.eos (loopCombFixed_body q)) s0 s' nn ∧
        nn ≤ (m - i) * (c + 6) + 1 ∧ s'.stk 0 = encs out ++ R ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = s0.stk k) := by
    intro n
    induction n with
    | zero =>
        intro i vs R s0 hle' hi hr hI' hs
        exact absurd hle' (by omega)
    | succ n ih =>
        intro i vs R s0 hle' hi hr hI' hs
        obtain ⟨out1, s1, n1, hEv1, hn1, hfr1, hdisj⟩ :=
          loopCombFixed_bodySpec_local main q I F c m i vs R s0 hq hI' hs
        rcases hdisj with ⟨hstop, hs1, hF1⟩ | ⟨hcont, hs1, hIt, hlt⟩
        · refine ⟨out1, s1, n1 + 2, hF1, ?_, ?_, hs1, hfr1⟩
          · exact Eval.loopT hr hEv1 (Eval.loopF hstop)
          · have h1 : n1 ≤ c + 5 := hn1
            have hmi : 1 ≤ m - i := by omega
            have h3 : c + 6 ≤ (m - i) * (c + 6) := by
              have h := Nat.mul_le_mul_right (c + 6) hmi
              simpa using h
            omega
        · obtain ⟨out2, s2, n2, hF2, hEv2, hn2, hs2, hfr2⟩ :=
            ih (i + 1) out1 R s1 (by omega) hlt hcont hIt hs1
          refine ⟨out2, s2, n1 + n2 + 1, hF2, ?_, ?_, hs2, ?_⟩
          · exact Eval.loopT hr hEv1 hEv2
          · have h1 : n1 ≤ c + 5 := hn1
            have h2 : n2 ≤ (m - (i + 1)) * (c + 6) + 1 := hn2
            have hmi : m - i = (m - (i + 1)) + 1 := by omega
            rw [hmi]
            nlinarith [h1, h2]
          · intro k hk
            rw [hfr2 k hk, hfr1 k hk]
  obtain ⟨out, s', n, hF, hEv, hn, hstk, hfr⟩ := key (m - 0) 0 vs R sE (le_refl _) hlt0 hrE hI hsE0
  refine ⟨out, s', 1 + n, hF, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq (Eval.set 0 Glyph.eos s) hEv
  · have h0 : m - 0 = m := by omega
    have h1 : n ≤ m * (c + 6) + 1 := by rw [h0] at hn; exact hn
    show 1 + n ≤ m * (c + 6) + 6
    omega
  · exact hstk
  · intro k hk
    rw [hfr k hk, hsE]
    simp

end Work.Kernel
