import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.ifNil

/-!
# Resample: the sentinel-driven `WordM` do-while (`wmLoopSent`)

The loop of `Work.Resample.wmLoopSent` runs `q` while the head glyph of the stack `src` is not
`Glyph.nil` (the encoding of the sentinel value `Val.nil`).  This file contains the program and its
correctness/cost proof, by the same strong induction on the number of remaining rounds as
`Submission/Work/Kernel/loopCombFixed.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Resample

open HvdH

/-! ## The program -/

/-- One round: peek the head glyph of `src`; if it is `Glyph.nil` (the sentinel) stop the loop
(`r0 := iend`), else run `q` and continue (`r0 := eos`). -/
def wmLoopSent_body (src : Stk) (q : Cmd) : Cmd :=
  Cmd.seq (Cmd.peek src 1)
    (Cmd.ite 1 Glyph.nil (Cmd.set 0 Glyph.iend) (Cmd.seq q (Cmd.set 0 Glyph.eos)))

/-- The sentinel-driven do-while: arm the test register `0` and run the loop. -/
def wmLoopSent_comb (src : Stk) (q : Cmd) : Cmd :=
  Cmd.seq (Cmd.set 0 Glyph.eos) (Cmd.loop 0 Glyph.eos (wmLoopSent_body src q))

/-! ## Elementary facts about lists and encodings -/

theorem wmLoopSent_headD_append {α : Type} (l₁ l₂ : List α) (a : α) (h : l₁ ≠ []) :
    (l₁ ++ l₂).headD a = l₁.headD a := by
  cases l₁ with
  | nil => exact absurd rfl h
  | cons x xs => rfl

/-- No value encodes to the empty word. -/
theorem wmLoopSent_enc_ne_nil (v : Val) : v.enc ≠ [] := by
  cases v <;> simp [Val.enc]

/-- A stack of values encodes to the empty word only if it is empty. -/
theorem wmLoopSent_encs_eq_nil_iff (l : List Val) : encs l = [] ↔ l = [] := by
  induction l with
  | nil => simp [encs]
  | cons v t ih =>
    rw [Work.Kernel.encs_cons]
    constructor
    · intro h
      exact absurd (List.append_eq_nil_iff.mp h).1 (wmLoopSent_enc_ne_nil v)
    · intro h
      exact absurd h (List.cons_ne_nil v t)

theorem wmLoopSent_encs_ne_nil_iff (l : List Val) : encs l ≠ [] ↔ l ≠ [] := by
  constructor
  · intro h hl; exact h ((wmLoopSent_encs_eq_nil_iff l).mpr hl)
  · intro h hl; exact h ((wmLoopSent_encs_eq_nil_iff l).mp hl)

/-- The head of `encs l ++ B` is the head of `encs l` when `l` is non-empty (this is why the paper's
hypothesis `a src ≠ []` is needed). -/
theorem wmLoopSent_headD_encs_append (l : List Val) (hl : l ≠ []) (B : List Glyph) :
    (encs l ++ B).headD Glyph.eos = (encs l).headD Glyph.eos := by
  cases l with
  | nil => exact absurd rfl hl
  | cons v t =>
    rw [Work.Kernel.encs_cons, List.append_assoc]
    rw [wmLoopSent_headD_append v.enc (encs t ++ B) Glyph.eos (wmLoopSent_enc_ne_nil v),
      wmLoopSent_headD_append v.enc (encs t) Glyph.eos (wmLoopSent_enc_ne_nil v)]

/-! ## The two outcomes of one round -/

/-- The stopping round: the head glyph of `src` is the sentinel `Glyph.nil`, so the body only sets
the test register `0` to `iend` (cost 3) and leaves every stack untouched. -/
theorem wmLoopSent_body_stop (src : Stk) (hsrc : src ≠ 0) (main q : Cmd)
    (a : Stk → List Val) (s0 : State) (Bg : Stk → List Glyph)
    (hk0 : ∀ k : Stk, k ≠ 0 → s0.stk k = encs (a k) ++ Bg k)
    (hstop : (encs (a src)).headD Glyph.eos = Glyph.nil) :
    ∃ (s' : State) (n : ℕ), Eval main (wmLoopSent_body src q) s0 s' n ∧ n ≤ 3 ∧
      s'.stk 0 = s0.stk 0 ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = s0.stk k) ∧
      s'.reg 0 ≠ Glyph.eos := by
  have hne : a src ≠ [] := by
    intro h; rw [h] at hstop; simp [encs] at hstop
  have hsrcstk : s0.stk src = encs (a src) ++ Bg src := hk0 src hsrc
  have hhead : (s0.stk src).headD Glyph.eos = Glyph.nil := by
    rw [hsrcstk, wmLoopSent_headD_encs_append (a src) hne (Bg src)]; exact hstop
  have hpeekreg : (State.tPeek s0 src 1).reg 1 = Glyph.nil := by
    show (s0.stk src).headD Glyph.eos = Glyph.nil
    exact hhead
  refine ⟨State.tSet (State.tPeek s0 src 1) 0 Glyph.iend, 3, ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq (Eval.peek src 1 s0) (Eval.iteT hpeekreg (Eval.set 0 Glyph.iend _))
  · omega
  · show (State.tPeek s0 src 1).stk 0 = s0.stk 0
    rfl
  · intro k hk
    show (State.tPeek s0 src 1).stk k = s0.stk k
    rfl
  · show Glyph.iend ≠ Glyph.eos
    exact fun h => Glyph.noConfusion h

/-- The continuing round: the head glyph of `src` is not `Glyph.nil` (and `a src ≠ []`), so the body
runs `q` (cost `c`) and sets the test register `0` to `eos` (total cost `≤ c + 3`). -/
theorem wmLoopSent_body_cont (src : Stk) (hsrc : src ≠ 0) (main q : Cmd)
    (I : ℕ → List Val → (Stk → List Val) → Prop) (c m i : ℕ)
    (vs : List Val) (a : Stk → List Val) (s0 : State) (R : List Glyph) (Bg : Stk → List Glyph)
    (hq : ∀ (i : ℕ) (vs : List Val) (a : Stk → List Val), I i vs a → i < m →
      WordM main q (fun w b => w = vs ∧ b = a) (fun _ _ out b => I (i + 1) out b)
        (fun _ _ => c))
    (hI : I i vs a) (hlt : i < m)
    (hcont : a src ≠ [] ∧ (encs (a src)).headD Glyph.eos ≠ Glyph.nil)
    (hs0 : s0.stk 0 = encs vs ++ R)
    (hk0 : ∀ k : Stk, k ≠ 0 → s0.stk k = encs (a k) ++ Bg k) :
    ∃ (out : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
      I (i + 1) out b ∧ Eval main (wmLoopSent_body src q) s0 s' n ∧ n ≤ c + 3 ∧
      s'.stk 0 = encs out ++ R ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k) ∧
      s'.reg 0 = Glyph.eos := by
  have hsrcstk : s0.stk src = encs (a src) ++ Bg src := hk0 src hsrc
  have hhead : (s0.stk src).headD Glyph.eos ≠ Glyph.nil := by
    rw [hsrcstk, wmLoopSent_headD_encs_append (a src) hcont.1 (Bg src)]; exact hcont.2
  have hpeekreg : (State.tPeek s0 src 1).reg 1 ≠ Glyph.nil := by
    show (s0.stk src).headD Glyph.eos ≠ Glyph.nil
    exact hhead
  obtain ⟨out, b, s', n, hI1, hev, hn, hs', hk'⟩ :=
    hq i vs a hI hlt vs a ⟨rfl, rfl⟩ (State.tPeek s0 src 1) R Bg
      (by show s0.stk 0 = encs vs ++ R; exact hs0)
      (by intro k hk; show s0.stk k = encs (a k) ++ Bg k; exact hk0 k hk)
  refine ⟨out, b, State.tSet s' 0 Glyph.eos, 1 + (n + 1 + 1), hI1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq (Eval.peek src 1 s0)
      (Eval.iteF hpeekreg (Eval.seq hev (Eval.set 0 Glyph.eos s')))
  · have hn' : n ≤ c := hn
    omega
  · show s'.stk 0 = encs out ++ R
    exact hs'
  · intro k hk
    show s'.stk k = encs (b k) ++ Bg k
    exact hk' k hk
  · show Glyph.eos = Glyph.eos
    rfl

/-! ## The combinator -/

/-- Sentinel-driven `WordM` do-while: while the head glyph of stack `src` is not `Glyph.nil`, run
`q`.  The loop stops at round `m`, on which the sentinel `Val.nil` (whose encoding is the single
glyph `Glyph.nil`) is on top of `src`; `I i` is the invariant after `i` rounds and `F` the exit
assertion.  The body is only required for `i < m`.  Program:
`set r eos ;; loop r eos ((peek src r') ;; ite r' Glyph.nil (set r iend) (q ;; set r eos))`,
which uses only registers and a `peek` of stack `src`.  (The hypothesis `a src ≠ []` on the
continuing rounds is needed because `peek` reads `encs (a src) ++ Bg src`, whose head is the head of
`encs (a src)` only when the latter is nonempty.  Prove by the same strong induction as
`Kernel/loopCombFixed.lean`.  Cost: `q` runs `m` times, every round pays a `peek`, an `ite` and a
`set`, so `K = 5` suffices.) -/
theorem wmLoopSent (src : HvdH.Stk) (hsrc : src ≠ 0) :
    ∃ (comb : HvdH.Cmd → HvdH.Cmd) (K : ℕ),
      ∀ (main q : HvdH.Cmd) (I : ℕ → List HvdH.Val → (HvdH.Stk → List HvdH.Val) → Prop)
        (F : List HvdH.Val → (HvdH.Stk → List HvdH.Val) → Prop) (c m : ℕ),
        (∀ i vs a, I i vs a → i < m → Work.Resample.WordM main q (fun w b => w = vs ∧ b = a)
          (fun _ _ out b => I (i + 1) out b) (fun _ _ => c)) →
        (∀ i vs a, I i vs a → i < m → a src ≠ [] ∧
          (HvdH.encs (a src)).headD HvdH.Glyph.eos ≠ HvdH.Glyph.nil) →
        (∀ vs a, I m vs a → (HvdH.encs (a src)).headD HvdH.Glyph.eos = HvdH.Glyph.nil) →
        (∀ vs a, I m vs a → F vs a) →
        Work.Resample.WordM main (comb q) (I 0) (fun _ _ out b => F out b)
          (fun _ _ => (m + 1) * (c + K) + K) := by
  refine ⟨wmLoopSent_comb src, 5, ?_⟩
  intro main q I F c m hq hcont hstop hexit
  intro vs a hI s R Bg hs0 hk0
  have key : ∀ (n i : ℕ) (vs : List Val) (a : Stk → List Val) (R : List Glyph)
      (Bg : Stk → List Glyph) (s0 : State),
      m - i ≤ n → i ≤ m → s0.reg 0 = Glyph.eos → I i vs a → s0.stk 0 = encs vs ++ R →
      (∀ k : Stk, k ≠ 0 → s0.stk k = encs (a k) ++ Bg k) →
      ∃ (out : List Val) (b : Stk → List Val) (s' : State) (nn : ℕ),
        F out b ∧ Eval main (Cmd.loop 0 Glyph.eos (wmLoopSent_body src q)) s0 s' nn ∧
        nn ≤ (m - i) * (c + 4) + 5 ∧ s'.stk 0 = encs out ++ R ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k) := by
    intro n
    induction n with
    | zero =>
      intro i vs a R Bg s0 hle himle hr hI' hs hk
      have his : i = m := by omega
      obtain ⟨s', n1, hev, hn1, hs'0, hs'k, hreg⟩ :=
        wmLoopSent_body_stop src hsrc main q a s0 Bg hk (hstop vs a (his ▸ hI'))
      refine ⟨vs, a, s', n1 + 1 + 1, hexit vs a (his ▸ hI'),
        Eval.loopT hr hev (Eval.loopF hreg), ?_, ?_, ?_⟩
      · have h0 : m - i = 0 := by omega
        rw [h0]; omega
      · rw [hs'0]; exact hs
      · intro k hk'; rw [hs'k k hk']; exact hk k hk'
    | succ n ih =>
      intro i vs a R Bg s0 hle himle hr hI' hs hk
      by_cases hlt : i < m
      · obtain ⟨out1, b1, s1, n1, hI1, hev1, hn1, hs1, hk1, hreg1⟩ :=
          wmLoopSent_body_cont src hsrc main q I c m i vs a s0 R Bg hq hI' hlt
            (hcont i vs a hI' hlt) hs hk
        obtain ⟨out2, b2, s2, n2, hF2, hev2, hn2, hs2, hk2⟩ :=
          ih (i + 1) out1 b1 R Bg s1 (by omega) (by omega) hreg1 hI1 hs1 hk1
        refine ⟨out2, b2, s2, n1 + n2 + 1, hF2, Eval.loopT hr hev1 hev2, ?_, hs2, hk2⟩
        have hmi : m - i = (m - (i + 1)) + 1 := by omega
        have h1 : n1 ≤ c + 3 := hn1
        have h2 : n2 ≤ (m - (i + 1)) * (c + 4) + 5 := hn2
        rw [hmi]
        nlinarith [h1, h2]
      · have his : i = m := by omega
        obtain ⟨s', n1, hev, hn1, hs'0, hs'k, hreg⟩ :=
          wmLoopSent_body_stop src hsrc main q a s0 Bg hk (hstop vs a (his ▸ hI'))
        refine ⟨vs, a, s', n1 + 1 + 1, hexit vs a (his ▸ hI'),
          Eval.loopT hr hev (Eval.loopF hreg), ?_, ?_, ?_⟩
        · have h0 : m - i = 0 := by omega
          rw [h0]; omega
        · rw [hs'0]; exact hs
        · intro k hk'; rw [hs'k k hk']; exact hk k hk'
  obtain ⟨out, b, s', nn, hF, hev, hn, hs', hk'⟩ :=
    key m 0 vs a R Bg (s.updReg 0 Glyph.eos) (by omega) (by omega)
      (by show Glyph.eos = Glyph.eos; rfl) hI
      (by show s.stk 0 = encs vs ++ R; exact hs0)
      (by intro k hk; show s.stk k = encs (a k) ++ Bg k; exact hk0 k hk)
  refine ⟨out, b, s', 1 + nn, hF, Eval.seq (Eval.set 0 Glyph.eos s) hev, ?_, hs', hk'⟩
  have h1 : nn ≤ m * (c + 4) + 5 := by
    have h0 : m - 0 = m := by omega
    rw [h0] at hn; exact hn
  nlinarith [h1]

end Work.Resample
