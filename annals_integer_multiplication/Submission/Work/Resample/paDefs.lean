import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.specs
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.tensorAux
import Submission.Work.Resample.axisIter_length
import Submission.Work.Resample.axisIter_disc
import Submission.Work.Resample.axisIter_getD_fxTensorRec
import Submission.Work.IntLib.Shift.Base
import Submission.Work.ConvR.basic
import Submission.Work.MainP.ss_prod_le_ts_prod

/-!
# The tensoring program `Ã` (paper Theorem 4.1, `A` half): shared framework and definitions

This file fixes everything the program `progA` of `Submission.Work.Resample.progTensorA` needs on
the *bookkeeping* side:

* `paMark` — the raw boundary marker `Glyph.mk 0` which the program keeps on stack 0 between the
  accumulating scratch data and the honest suffix of the value stack.
* `WordP`/`WordPI`/`WordPe` — Hoare triples with an explicit marker, a value list `rest` below the
  marker and explicit value lists on every non-zero stack (the `WordM` bookkeeping of
  `Work.Resample.pbDefs` extended by the marker).  `WordPI` is the input form (no marker yet, the
  program inserts it), `WordP` the invariant form, `WordPe` the output form (the marker is removed
  again and `rest` reappears in the value stack).
* `PAInv` — the between-axes invariant of the program: the array `axisIter ss ts Φ j zs0` on top of
  stack 0, the dimension data on stacks 2–5 and the running outer product `A_j` on stack 6.
* `PAMid` — the intermediate state between the two halves of one axis step.
* `PABr` — the per-axis budget.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## The marker -/

/-- Boundary marker on stack 0 of the `Ã` program: `Glyph.mk 0` (so that
`Work.IntLib.Shift.clearAll 0` recognises it). -/
def paMark : Glyph := Glyph.mk 0

/-- No `Glyph.mk` occurs in the encoding of a value. -/
theorem noMark_enc (v : Val) (i : Stk) : Glyph.mk i ∉ v.enc := by
  induction v with
  | int z =>
    intro hmem
    simp only [Val.enc] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · by_cases hz : z < 0
      · rw [ite_eq_left hz] at h; exact absurd h (by intro h'; cases h')
      · rw [ite_eq_right hz] at h; exact absurd h (by intro h'; cases h')
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨b, _, hb⟩ := List.mem_map.mp h
        exact absurd hb (by intro h'; cases h')
      · exact absurd (List.mem_singleton.mp h) (by intro h'; cases h')
  | nil =>
    intro h
    simp only [Val.enc, List.mem_singleton] at h
    exact absurd h (by intro h'; cases h')
  | cons a b iha ihb =>
    intro hmem
    simp only [Val.enc, List.mem_cons] at hmem
    rcases hmem with h | h
    · exact absurd h (by intro h'; cases h')
    · exact (List.mem_append.mp h).elim iha ihb

/-- No `Glyph.mk` occurs in an encoding of a list of values. -/
theorem noMark_encs (vs : List Val) (i : Stk) : Glyph.mk i ∉ encs vs := by
  induction vs with
  | nil => simp [encs]
  | cons v vs ih =>
    intro h
    rw [Work.Kernel.encs_cons] at h
    rcases List.mem_append.mp h with h | h
    · exact noMark_enc v i h
    · exact ih h

theorem paMark_ne_enc (v : Val) : paMark ∉ v.enc := noMark_enc v 0

theorem paMark_ne_encs (vs : List Val) : paMark ∉ encs vs := noMark_encs vs 0

/-- The `Eval` of "push the marker on stack 0". -/
theorem paPushMark_ev (main : Cmd) (r : Reg) (s : State) :
    ∃ s' n, Eval main (.seq (.set r paMark) (.push 0 r)) s s' n ∧ n ≤ 2 ∧
      s'.stk 0 = paMark :: s.stk 0 ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k) := by
  have h1 : Eval main (.set r paMark) s ⟨Function.update s.reg r paMark, s.stk⟩ 1 := Eval.set r paMark s
  have h2 : Eval main (.push 0 r) ⟨Function.update s.reg r paMark, s.stk⟩
      ⟨Function.update s.reg r paMark, Function.update s.stk 0 (paMark :: s.stk 0)⟩ 1 := by
    have h := Eval.push (main := main) 0 r (⟨Function.update s.reg r paMark, s.stk⟩ : State)
    simpa using h
  refine ⟨_, _, Eval.seq h1 h2, by simp, ?_, ?_⟩
  · simp
  · intro k hk
    simp [Function.update_of_ne hk]

/-! ## Hoare triples with an explicit marker -/

/-- `WordP main p Pre Post C`: `p` transforms a state whose stack 0 is `encs vs ++ paMark ::
(encs rest ++ R0)` (with `Pre vs rest a`) into one whose stack 0 is `encs out ++ paMark ::
(encs rest ++ R0)` (with `Post vs rest a out b`), at cost `≤ C vs rest a`; the non-zero stacks are
described by the value lists `a`/`b` on top of a fixed raw suffix `Bg`.  The part below the marker
never changes. -/
def WordP (main p : Cmd) (Pre : List Val → List Val → (Stk → List Val) → Prop)
    (Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop)
    (C : List Val → List Val → (Stk → List Val) → ℕ) : Prop :=
  ∀ vs rest a, Pre vs rest a → ∀ (s : State) (R0 : List Glyph) (Bg : Stk → List Glyph),
    s.stk 0 = encs vs ++ paMark :: (encs rest ++ R0) →
    (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
    ∃ (out : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
      Post vs rest a out b ∧ Eval main p s s' n ∧ n ≤ C vs rest a ∧
      s'.stk 0 = encs out ++ paMark :: (encs rest ++ R0) ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)

/-- `WordPI`: input form without a marker (the program inserts it). -/
def WordPI (main p : Cmd) (Pre : List Val → (Stk → List Val) → Prop)
    (Post : List Val → (Stk → List Val) → List Val → List Val → (Stk → List Val) → Prop)
    (C : List Val → (Stk → List Val) → ℕ) : Prop :=
  ∀ vs a, Pre vs a → ∀ (s : State) (R : List Glyph) (Bg : Stk → List Glyph),
    s.stk 0 = encs vs ++ R →
    (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
    ∃ (out rout : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
      Post vs a out rout b ∧ Eval main p s s' n ∧ n ≤ C vs a ∧
      s'.stk 0 = encs out ++ paMark :: (encs rout ++ R) ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)

/-- `WordPe`: output form (the marker is removed and `rest` rejoins the value stack). -/
def WordPe (main p : Cmd) (Pre : List Val → List Val → (Stk → List Val) → Prop)
    (Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop)
    (C : List Val → List Val → (Stk → List Val) → ℕ) : Prop :=
  ∀ vs rest a, Pre vs rest a → ∀ (s : State) (R0 : List Glyph) (Bg : Stk → List Glyph),
    s.stk 0 = encs vs ++ paMark :: (encs rest ++ R0) →
    (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
    ∃ (out : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
      Post vs rest a out b ∧ Eval main p s s' n ∧ n ≤ C vs rest a ∧
      s'.stk 0 = encs out ++ (encs rest ++ R0) ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)

/-- A program built from `Ev`-level facts is a `WordP`. -/
theorem WordP.ofEv (main p : Cmd) (Pre : List Val → List Val → (Stk → List Val) → Prop)
    (Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop)
    (C : List Val → List Val → (Stk → List Val) → ℕ)
    (h : ∀ vs rest a, Pre vs rest a → ∀ (s : State) (R0 : List Glyph) (Bg : Stk → List Glyph),
      s.stk 0 = encs vs ++ paMark :: (encs rest ++ R0) →
      (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
      ∃ (out : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
        Post vs rest a out b ∧ Eval main p s s' n ∧ n ≤ C vs rest a ∧
        s'.stk 0 = encs out ++ paMark :: (encs rest ++ R0) ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)) :
    WordP main p Pre Post C := h

/-- A program built from `Ev`-level facts is a `WordPI`. -/
theorem WordPI.ofEv (main p : Cmd) (Pre : List Val → (Stk → List Val) → Prop)
    (Post : List Val → (Stk → List Val) → List Val → List Val → (Stk → List Val) → Prop)
    (C : List Val → (Stk → List Val) → ℕ)
    (h : ∀ vs a, Pre vs a → ∀ (s : State) (R : List Glyph) (Bg : Stk → List Glyph),
      s.stk 0 = encs vs ++ R →
      (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
      ∃ (out rout : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
        Post vs a out rout b ∧ Eval main p s s' n ∧ n ≤ C vs a ∧
        s'.stk 0 = encs out ++ paMark :: (encs rout ++ R) ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)) :
    WordPI main p Pre Post C := h

/-- A program built from `Ev`-level facts is a `WordPe`. -/
theorem WordPe.ofEv (main p : Cmd) (Pre : List Val → List Val → (Stk → List Val) → Prop)
    (Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop)
    (C : List Val → List Val → (Stk → List Val) → ℕ)
    (h : ∀ vs rest a, Pre vs rest a → ∀ (s : State) (R0 : List Glyph) (Bg : Stk → List Glyph),
      s.stk 0 = encs vs ++ paMark :: (encs rest ++ R0) →
      (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
      ∃ (out : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
        Post vs rest a out b ∧ Eval main p s s' n ∧ n ≤ C vs rest a ∧
        s'.stk 0 = encs out ++ (encs rest ++ R0) ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)) :
    WordPe main p Pre Post C := h

/-- An ordinary `WordR` word is a `WordP` word which neither moves the marker nor changes the
value lists on the non-zero stacks. -/
theorem WordP.ofWordR {main p : Cmd} {Pre : List Val → Prop}
    {Post : List Val → List Val → Prop} {C : List Val → ℕ}
    (h : WordR main p Pre Post C) :
    WordP main p (fun vs _ _ => Pre vs)
      (fun vs rest a out b => Post vs out ∧ b = a) (fun vs _ _ => C vs) := by
  intro vs rest a hpre s R0 Bg h0 hk
  obtain ⟨out, s', n, hPost, hev, hc, h0', hk'⟩ := h vs hpre s (paMark :: (encs rest ++ R0)) h0
  exact ⟨out, a, s', n, ⟨hPost, rfl⟩, hev, hc, h0', fun k hk0 => by rw [hk' k hk0, hk k hk0]⟩

/-- A `WordM` word (no marker bookkeeping needed) is a `WordP` word. -/
theorem WordP.ofWordM {main p : Cmd} {Pre : List Val → (Stk → List Val) → Prop}
    {Post : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C : List Val → (Stk → List Val) → ℕ}
    (h : WordM main p Pre Post C) :
    WordP main p (fun vs _ a => Pre vs a) (fun vs rest a out b => Post vs a out b)
      (fun vs _ a => C vs a) := by
  intro vs rest a hpre s R0 Bg h0 hk
  exact h vs a hpre s (paMark :: (encs rest ++ R0)) Bg h0 hk

/-- Composition of two `WordP` programs. -/
theorem WordP.seq {main : Cmd} {p q : Cmd}
    {Pre₁ : List Val → List Val → (Stk → List Val) → Prop}
    {Post₁ : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {Pre₂ : List Val → List Val → (Stk → List Val) → Prop}
    {Post₂ : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C₁ : List Val → List Val → (Stk → List Val) → ℕ}
    {C₂ : List Val → List Val → (Stk → List Val) → ℕ}
    {B : List Val → List Val → (Stk → List Val) → ℕ}
    (h₁ : WordP main p Pre₁ Post₁ C₁) (h₂ : WordP main q Pre₂ Post₂ C₂)
    (hpre : ∀ vs rest a mid a', Post₁ vs rest a mid a' → Pre₂ mid rest a')
    (hcost : ∀ vs rest a mid a', Post₁ vs rest a mid a' → C₂ mid rest a' ≤ B vs rest a) :
    WordP main (.seq p q) Pre₁
      (fun vs rest a out b => ∃ mid a', Post₁ vs rest a mid a' ∧ Post₂ mid rest a' out b)
      (fun vs rest a => C₁ vs rest a + B vs rest a) := by
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨mid, a', s', n₁, hP₁, hev₁, hc₁, h0', hk'⟩ := h₁ vs rest a hPre s R0 Bg h0 hk
  obtain ⟨out, b, s'', n₂, hP₂, hev₂, hc₂, h0'', hk''⟩ :=
    h₂ mid rest a' (hpre vs rest a mid a' hP₁) s' R0 Bg h0' hk'
  refine ⟨out, b, s'', n₁ + n₂, ⟨mid, a', hP₁, hP₂⟩, Eval.seq hev₁ hev₂, ?_, h0'', hk''⟩
  exact Nat.add_le_add hc₁ (le_trans hc₂ (hcost vs rest a mid a' hP₁))

/-- Composition of a `WordPI` with a `WordP`. -/
theorem WordPI.seq_P {main : Cmd} {p q : Cmd}
    {Pre₁ : List Val → (Stk → List Val) → Prop}
    {Post₁ : List Val → (Stk → List Val) → List Val → List Val → (Stk → List Val) → Prop}
    {Pre₂ : List Val → List Val → (Stk → List Val) → Prop}
    {Post₂ : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C₁ : List Val → (Stk → List Val) → ℕ}
    {C₂ : List Val → List Val → (Stk → List Val) → ℕ}
    {B : List Val → (Stk → List Val) → ℕ}
    (h₁ : WordPI main p Pre₁ Post₁ C₁) (h₂ : WordP main q Pre₂ Post₂ C₂)
    (hpre : ∀ vs a mid rout a', Post₁ vs a mid rout a' → Pre₂ mid rout a')
    (hcost : ∀ vs a mid rout a', Post₁ vs a mid rout a' → C₂ mid rout a' ≤ B vs a) :
    WordPI main (.seq p q) Pre₁
      (fun vs a out rout b => ∃ mid rout' a', rout = rout' ∧ Post₁ vs a mid rout' a' ∧
        Post₂ mid rout' a' out b)
      (fun vs a => C₁ vs a + B vs a) := by
  intro vs a hPre s R Bg h0 hk
  obtain ⟨mid, rout', a', s', n₁, hP₁, hev₁, hc₁, h0', hk'⟩ := h₁ vs a hPre s R Bg h0 hk
  obtain ⟨out, b, s'', n₂, hP₂, hev₂, hc₂, h0'', hk''⟩ :=
    h₂ mid rout' a' (hpre vs a mid rout' a' hP₁) s' R Bg h0' hk'
  refine ⟨out, rout', b, s'', n₁ + n₂, ⟨mid, rout', a', rfl, hP₁, hP₂⟩, Eval.seq hev₁ hev₂, ?_,
    h0'', hk''⟩
  exact Nat.add_le_add hc₁ (le_trans hc₂ (hcost vs a mid rout' a' hP₁))

/-- Composition of a `WordP` with a `WordPe`. -/
theorem WordP.seq_e {main : Cmd} {p q : Cmd}
    {Pre₁ : List Val → List Val → (Stk → List Val) → Prop}
    {Post₁ : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {Pre₂ : List Val → List Val → (Stk → List Val) → Prop}
    {Post₂ : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C₁ : List Val → List Val → (Stk → List Val) → ℕ}
    {C₂ : List Val → List Val → (Stk → List Val) → ℕ}
    {B : List Val → List Val → (Stk → List Val) → ℕ}
    (h₁ : WordP main p Pre₁ Post₁ C₁) (h₂ : WordPe main q Pre₂ Post₂ C₂)
    (hpre : ∀ vs rest a mid a', Post₁ vs rest a mid a' → Pre₂ mid rest a')
    (hcost : ∀ vs rest a mid a', Post₁ vs rest a mid a' → C₂ mid rest a' ≤ B vs rest a) :
    WordPe main (.seq p q) Pre₁
      (fun vs rest a out b => ∃ mid a', Post₁ vs rest a mid a' ∧ Post₂ mid rest a' out b)
      (fun vs rest a => C₁ vs rest a + B vs rest a) := by
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨mid, a', s', n₁, hP₁, hev₁, hc₁, h0', hk'⟩ := h₁ vs rest a hPre s R0 Bg h0 hk
  obtain ⟨out, b, s'', n₂, hP₂, hev₂, hc₂, h0'', hk''⟩ :=
    h₂ mid rest a' (hpre vs rest a mid a' hP₁) s' R0 Bg h0' hk'
  refine ⟨out, b, s'', n₁ + n₂, ⟨mid, a', hP₁, hP₂⟩, Eval.seq hev₁ hev₂, ?_, h0'', hk''⟩
  exact Nat.add_le_add hc₁ (le_trans hc₂ (hcost vs rest a mid a' hP₁))

/-- Consequence rule for `WordP`. -/
theorem WordP.conseq {main p : Cmd}
    {Pre : List Val → List Val → (Stk → List Val) → Prop}
    {Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C : List Val → List Val → (Stk → List Val) → ℕ}
    {Pre' : List Val → List Val → (Stk → List Val) → Prop}
    {Post' : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C' : List Val → List Val → (Stk → List Val) → ℕ}
    (h : WordP main p Pre Post C) (h1 : ∀ vs rest a, Pre' vs rest a → Pre vs rest a)
    (h2 : ∀ vs rest a out b, Pre' vs rest a → Post vs rest a out b → Post' vs rest a out b)
    (h3 : ∀ vs rest a, Pre' vs rest a → C vs rest a ≤ C' vs rest a) :
    WordP main p Pre' Post' C' := by
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨out, b, s', n, hPost, hev, hc, h0', hk'⟩ := h vs rest a (h1 vs rest a hPre) s R0 Bg h0 hk
  exact ⟨out, b, s', n, h2 vs rest a out b hPre hPost, hev, le_trans hc (h3 vs rest a hPre),
    h0', hk'⟩

/-- Monotone cost bound for `WordP`. -/
theorem WordP.mono {main p : Cmd} {Pre : List Val → List Val → (Stk → List Val) → Prop}
    {Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C C' : List Val → List Val → (Stk → List Val) → ℕ}
    (h : WordP main p Pre Post C) (hC : ∀ vs rest a, C vs rest a ≤ C' vs rest a) :
    WordP main p Pre Post C' := fun vs rest a hP s R0 Bg h0 hk => by
  obtain ⟨out, b, s', n, hPost, hev, hc, h0', hk'⟩ := h vs rest a hP s R0 Bg h0 hk
  exact ⟨out, b, s', n, hPost, hev, le_trans hc (hC vs rest a), h0', hk'⟩

/-- The word removing the (junk) region above the marker `paMark` of stack 0. -/
theorem WordP.clearRgn (main : Cmd) (r rF : Reg) :
    WordP main (.seq (.set rF Work.IntLib.Shift.gGo)
        (.loop rF Work.IntLib.Shift.gGo (Work.IntLib.Shift.clearBody 0 paMark r rF)))
      (fun _ _ _ => True)
      (fun vs rest a out b => out = [] ∧ b = a)
      (fun vs _ _ => 5 * ((vs.map vsz).sum + 1) + 2) := by
  intro vs rest a _ s R0 Bg h0 hk
  have hlen : (encs vs).length = (vs.map vsz).sum := by
    rw [encs, List.length_flatten, List.map_map]
    rfl
  obtain ⟨s', n, hev, hn, _hne, hstk0, hfr⟩ :=
    Work.IntLib.Shift.clearRgn_ev main 0 paMark r rF (encs vs) (encs rest ++ R0) s.reg s.stk
      (fun h hh hpm => by rw [hpm] at hh; exact noMark_encs vs 0 hh) h0
  refine ⟨[], a, s', n, ⟨rfl, rfl⟩, hev, ?_, ?_, ?_⟩
  · show n ≤ 5 * ((vs.map vsz).sum + 1) + 2
    rw [← hlen]
    exact hn
  · rw [hstk0, Work.Kernel.encs_nil, List.nil_append]
  · intro k hk0
    rw [hfr k hk0, hk k hk0]

/-! ## The one-dimensional slice word specification (the body of `SliceSpecA`) -/

/-- The quantifier body of `Work.Resample.SliceSpecA` for fixed parameters: the preparation word
`prep`, the slice word `q`, their `WordR` specifications, the disc invariance and the one-dimensional
error bound. -/
def SliceSpecAtA (K : ℕ) (p α s t : ℕ) (prep q : Cmd)
    (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (P : List Val) : Prop :=
  (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
    WordR main prep
      (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
      (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
        out = P ++ rest)
      (fun _ => K * (t + 1) * (p + 1) ^ K)) ∧
  (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
    WordR main q
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = ofList (u.map cfxVal) :: P ++ rest ∧
        u.length = s ∧ (∀ z ∈ u, inDisc p z))
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
        vs = ofList (u.map cfxVal) :: P ++ rest ∧
        out = cvecVal w :: P ++ rest ∧ w.length = t ∧ (∀ z ∈ w, inDisc p z) ∧
        (∀ k : Fin t, w.getD k (0,0) = Φ (fun j => u.getD j (0,0)) k))
      (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1))) ∧
  (∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t, inDisc p (Φ w k)) ∧
  (∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t,
    ‖fxC p (Φ w k) - (resA s t α).mulVec (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p
      < (p : ℝ) ^ 2)

/-- `SliceSpecA` gives the per-axis specification. -/
theorem sliceSpecAtA_of_sliceSpecA {KL IL LL FL RM} (hA : SliceSpecA KL IL LL FL RM) :
    ∃ (prep q : Cmd) (Kb : ℕ), ∀ (p α s t : ℕ), 2 ≤ s → s < t → Nat.Coprime s t → t < 2 ^ p →
      2 ≤ α → 100 ≤ p → α ^ 2 < p → (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1 →
      ∃ (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (P : List Val),
        SliceSpecAtA Kb p α s t prep q Φ P := hA

/-! ## The invariant of the axis loop -/

/-- The semantic data of the array at axis `j`: the value `cvecVal (axisIter ss ts Φ j zs0)`, with
the expected length, every entry in the disc, and its encoding bounded by `ts.prod (2p+8)`. -/
def PAVec (p : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (j : ℕ) (arr : Val) : Prop :=
  arr = cvecVal (axisIter ss ts Φ j zs0) ∧
  (axisIter ss ts Φ j zs0).length = (ts.take j).prod * (ss.drop j).prod ∧
  (∀ z ∈ axisIter ss ts Φ j zs0, HvdH.inDisc p z) ∧
  vsz arr ≤ ts.prod * (2 * p + 8) + ts.prod + 1

/-- The between-axes invariant: stack 0 holds the array of axis `j`, stacks 2–5 the dimension data,
stack 6 the running outer product `A_j = ∏_{k<j} ts_k`, every other non-zero stack no values. -/
def PAInv (p α : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (j : ℕ) (vs rest : List Val) (a : Stk → List Val) : Prop :=
  ∃ arr : Val, PAVec p ss ts Φ zs0 j arr ∧ vs = [arr] ∧
    a 1 = [] ∧ a 2 = [intList (ss.drop j)] ∧ a 3 = [intList (ts.drop j)] ∧
    a 4 = [Val.int α] ∧ a 5 = [Val.int p] ∧ a 6 = [Val.int ((ts.take j).prod)] ∧
    (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6} : Finset ℕ) → a k = [])

/-- The intermediate state between the two halves of one axis step: the four arguments of
`LayoutLib.applyAlong` and the array above the freshly built table `Pj` on stack 0. -/
def PAMid (Kb : ℕ) (p α : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (j : ℕ) (Pj : List Val)
    (vs rest : List Val) (a : Stk → List Val) : Prop :=
  ∃ arr : Val, PAVec p ss ts Φ zs0 j arr ∧
    vs = [Val.int ((ts.take j).prod), Val.int (ss.getD j 0), Val.int (ts.getD j 0),
        Val.int ((ss.drop (j + 1)).prod), arr] ++ Pj ∧
    (Pj.map vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) ∧
    a 1 = [] ∧ a 2 = [intList (ss.drop (j + 1))] ∧ a 3 = [intList (ts.drop (j + 1))] ∧
    a 4 = [Val.int α] ∧ a 5 = [Val.int p] ∧ a 6 = [Val.int ((ts.take j).prod)] ∧
    a 7 = [Val.int (ts.getD j 0)] ∧
    (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6, 7} : Finset ℕ) → a k = [])

/-! ## Budgets -/

/-- Per-axis budget of the `Ã` program (generous upper bound for the cost of one axis step). -/
def PABr (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  64 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb)
  + 64 * (((ts.take j).prod * (ss.drop (j + 1)).prod) *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)))
  + 64 * (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ts.take j).prod * (ss.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1))
  + 64 * (isz ((ts.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) + isz ((ts.getD j 0 : ℕ) : ℤ) +
      isz (((ss.drop (j + 1)).prod : ℕ) : ℤ))
  + 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2)
  + 1048576 * ((HvdH.D + 1) * (p + 2))
  + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
  + 1048576 * ((p + 3) * (p + 3))
  + 1000000

/-- Total budget of the `D` axis passes. -/
def PAIterBr (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) : ℕ :=
  ((List.range HvdH.D).map (fun j => PABr Kb Cm p α ss ts j)).sum + 1

/-- Budget of the prologue. -/
def PASetupBr (p : ℕ) (ss ts : List ℕ) : ℕ :=
  64 * (ts.prod * (2 * p + 8) + ts.prod + 2) + 64 * (vsz (intList ss) + vsz (intList ts) + 1) +
    64 * (p + 1) + 200

/-- Budget of the epilogue. -/
def PAFinalBr (p : ℕ) (ss ts : List ℕ) : ℕ :=
  64 * (ts.prod * (2 * p + 8) + ts.prod + 2) +
    64 * (vsz (intList ss) + vsz (intList ts) + vsz (Val.int p) + 1) +
    64 * ((ts.prod : ℕ).size + 1) + 200

/-! ## Elementary list and arithmetic facts -/

theorem pa_intList_cons (t : ℕ) (l : List ℕ) :
    intList (t :: l) = Val.cons (Val.int (t : ℤ)) (intList l) := rfl

theorem pa_axisIter_zero (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (zs : List (ℤ × ℤ)) : axisIter ss ts Φ 0 zs = zs := rfl

theorem pa_axisIter_succ (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (j : ℕ) (zs : List (ℤ × ℤ)) :
    axisIter ss ts Φ (j + 1) zs = axisList ((ts.take j).prod) (ss.getD j 0) (ts.getD j 0)
      ((ss.drop (j + 1)).prod) (Φ j) (axisIter ss ts Φ j zs) := rfl

/-- `intList` of a `drop`-`cons`. -/
theorem pa_intList_drop_cons {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    intList (l.drop j) = Val.cons (Val.int (l.getD j 0 : ℤ)) (intList (l.drop (j + 1))) := by
  rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem l 0 hj]
  rfl

theorem pa_vsz_cvec_le {p : ℕ} {zs : List (ℤ × ℤ)} (h : ∀ z ∈ zs, inDisc p z) :
    vsz (cvecVal zs) ≤ zs.length * (2 * p + 8) + zs.length + 1 := by
  have h1 := Work.ConvR.vsz_cvecVal_le (p := p) (r := zs.length) ⟨rfl, h⟩
  simpa [Work.ConvR.cvecSz, Work.ConvR.cfxSz] using h1

/-- `getD` of a `drop`. -/
theorem pa_getD_drop (l : List ℕ) : ∀ (n i : ℕ), i < (l.drop n).length →
    (l.drop n).getD i 0 = l.getD (i + n) 0 := by
  induction l with
  | nil => intro n i h; simp at h
  | cons a l ih =>
    intro n i h
    cases n with
    | zero => simp
    | succ n =>
      rw [List.drop_succ_cons]
      rw [ih n i (by simpa [List.drop_succ_cons] using h)]
      rw [show i + (n + 1) = (i + n) + 1 from by omega, List.getD_cons_succ]

/-- The product of a suffix is monotone in the list. -/
theorem pa_drop_prod_le {p α : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) (j : ℕ) :
    (ss.drop j).prod ≤ (ts.drop j).prod := by
  have hss : ss.length = HvdH.D := hRes.1
  have hts : ts.length = HvdH.D := hRes.2.1
  refine Work.MainP.prod_le_prod_of_getD (by simp [List.length_drop, hss, hts]) ?_
  intro i hi
  rw [pa_getD_drop ss j i hi,
    pa_getD_drop ts j i (by simpa [List.length_drop, hss, hts] using hi)]
  have hj : i + j < HvdH.D := by
    have := hi; rw [List.length_drop, hss] at this; omega
  exact le_of_lt (hRes.2.2.2.2.2 (i + j) hj).2.1

/-- The array of axis `j` has at most `ts.prod` entries. -/
theorem pa_lens_le_prod {p α : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) {j : ℕ}
    (hj : j ≤ HvdH.D) : (ts.take j).prod * (ss.drop j).prod ≤ ts.prod := by
  have hss : ss.length = HvdH.D := hRes.1
  have hts : ts.length = HvdH.D := hRes.2.1
  have h1 : ts.prod = (ts.take j).prod * (ts.drop j).prod := by
    rw [← List.prod_append, List.take_append_drop]
  rw [h1]
  exact Nat.mul_le_mul_left _ (pa_drop_prod_le hRes j)

/-- The encoding bound of the invariant, read off the length and disc facts. -/
theorem pa_vsz_axis_le {p α : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) {j : ℕ}
    (hj : j ≤ HvdH.D) {es : List (ℤ × ℤ)}
    (hlen : es.length = (ts.take j).prod * (ss.drop j).prod)
    (hdisc : ∀ z ∈ es, HvdH.inDisc p z) :
    vsz (cvecVal es) ≤ ts.prod * (2 * p + 8) + ts.prod + 1 := by
  have h1 := pa_vsz_cvec_le hdisc
  rw [hlen] at h1
  have h2 := pa_lens_le_prod hRes hj
  have h3 : (ts.take j).prod * (ss.drop j).prod * (2 * p + 8) ≤ ts.prod * (2 * p + 8) :=
    Nat.mul_le_mul_right _ h2
  omega

end Work.Resample
