import Mathlib
import Submission.Work.IntLib.divRaw

namespace Work.IntLib

open HvdH

/-!
# The carry loop of `incBits` (area IntLib)

`Work.IntLib.incBits k T S TS rr rs` increments the least-significant-first bit region of stack `k`
(delimited by the marker `T`) using stack `S` as scratch.  Its first phase is the loop
`loop rr (bit true) (incBitsLoopBody k S rr rs)`: it looks at the top bit of the region while that
bit is `true`; every `true` bit is popped from `k` and replaced by a `false` bit pushed onto the
scratch stack `S` (that is the carry propagation, most significant first), and it stops at the first
bit that is not `true`.

This file proves the loop-level specification: if the region on `k` is
`bitsG (replicate j true ++ r) ++ T :: bk` with `r = []` or `r = false :: r'`, the loop transports
the `j` leading `true` bits to `S` as `false` bits, leaves `bitsG r ++ T :: bk` on `k`, stops with
`reg rr = T` (if `r = []`) or `reg rr = bit false` (if `r` starts with `false`), touches no other
stack, and costs at most `6 * j + 8` steps.

The proof is an induction on `j`; the two per-iteration lemmas
(`incBitsBody_true`, `incBitsBody_notTrue`) describe the loop body in the two cases.
-/

/-- One iteration of the loop body when the top glyph of stack `k` is `Glyph.bit true`: the bit is
popped and a `false` bit is pushed onto the scratch stack `S`.  Cost `5` (peek, test, pop, set,
push), and only the stacks `k`, `S` and the registers `rr`, `rs` are touched. -/
theorem incBitsBody_true (main : Cmd) (k : Stk) (S : Stk) (rr rs : Reg)
    (hne : k ≠ S) (hrr : rr ≠ rs) :
    ∀ (s : State) (rest Scont : List Glyph),
      s.stk k = Glyph.bit true :: rest → s.stk S = Scont →
      ∃ s' : State, Eval main (incBitsLoopBody k S rr rs) s s' 5 ∧
        s'.stk k = rest ∧ s'.stk S = Glyph.bit false :: Scont ∧
        s'.reg rr = Glyph.bit true ∧
        (∀ j' : Stk, j' ≠ k → j' ≠ S → s'.stk j' = s.stk j') := by
  intro s rest Scont hk hS
  let p : State := ⟨Function.update s.reg rr (Glyph.bit true), s.stk⟩
  let q : State := ⟨p.reg, Function.update p.stk k rest⟩
  let t : State := ⟨Function.update q.reg rs (Glyph.bit false), q.stk⟩
  let u : State := ⟨t.reg, Function.update t.stk S (t.reg rs :: t.stk S)⟩
  have hpreg : p.reg rr = Glyph.bit true := by simp [p]
  have hpk : p.stk k = Glyph.bit true :: rest := by simp [p, hk]
  have hqreg : Function.update p.reg rr (Glyph.bit true) = p.reg := by
    funext i
    by_cases hi : i = rr
    · subst hi; simp [hpreg]
    · simp [hi]
  have h1 : Eval main (.peek k rr) s p 1 := Eval.peek_cons hk
  have h2 : Eval main (.pop k rr) p q 1 := by
    have h := Eval.pop_cons (main := main) (k := k) (r := rr) (s := p)
      (g := Glyph.bit true) (rest := rest) hpk
    rw [hqreg] at h
    exact h
  have h3 : Eval main (.set rs (Glyph.bit false)) q t 1 := Eval.set rs (Glyph.bit false) q
  have h4 : Eval main (.push S rs) t u 1 := Eval.push S rs t
  refine ⟨u, Eval.seq h1 (Eval.iteT hpreg (Eval.seq h2 (Eval.seq h3 h4))), ?_, ?_, ?_, ?_⟩
  · simp [u, t, q, p, hne, hne.symm]
  · simp [u, t, q, p, hne.symm, hS]
  · simp [u, t, q, p, hrr]
  · intro j' hj1 hj2
    simp [u, t, q, p, Function.update_apply, hj1, hj2]

/-- One iteration of the loop body when the top glyph of stack `k` is not `Glyph.bit true`: nothing
happens except that `rr` now holds that glyph.  Cost `3` (peek, test, skip). -/
theorem incBitsBody_notTrue (main : Cmd) (k : Stk) (S : Stk) (rr rs : Reg) :
    ∀ (s : State) (g : Glyph) (rest : List Glyph),
      s.stk k = g :: rest → g ≠ Glyph.bit true →
      ∃ s' : State, Eval main (incBitsLoopBody k S rr rs) s s' 3 ∧
        s'.stk = s.stk ∧ s'.reg rr = g := by
  intro s g rest hk hg
  let p : State := ⟨Function.update s.reg rr g, s.stk⟩
  have h1 : Eval main (.peek k rr) s p 1 := Eval.peek_cons hk
  have hpreg : p.reg rr = g := by simp [p]
  have hskip : Eval main .skip p p 1 := Eval.skip p
  have hite : Eval main (.ite rr (Glyph.bit true)
      (.seq (.pop k rr) (.seq (.set rs (Glyph.bit false)) (.push S rs))) .skip) p p 2 :=
    Eval.iteF (by rw [hpreg]; exact hg) hskip
  exact ⟨p, Eval.seq h1 hite, by simp [p], hpreg⟩

/-- The loop terminates as soon as the top of stack `k` is not `Glyph.bit true`: one full iteration
(cost `3`, a no-op on stacks) followed by a failing test (cost `1`), after a passing test (cost `1`). -/
theorem incBitsLoop_final (main : Cmd) (k : Stk) (S : Stk) (rr rs : Reg) (rest : List Glyph)
    (s : State) (g : Glyph) :
    s.reg rr = Glyph.bit true → s.stk k = g :: rest → g ≠ Glyph.bit true →
    ∃ s' n, Eval main (.loop rr (Glyph.bit true) (incBitsLoopBody k S rr rs)) s s' n ∧ n ≤ 5 ∧
      s'.stk = s.stk ∧ s'.reg rr = g := by
  intro hreg hk hg
  obtain ⟨s₁, hev, hstk, hreg₁⟩ := incBitsBody_notTrue main k S rr rs s g rest hk hg
  refine ⟨s₁, 3 + 1 + 1, Eval.loopT hreg hev (Eval.loopF ?_), by omega, hstk, hreg₁⟩
  rw [hreg₁]; exact hg

theorem incBits_loop_eval (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (S : HvdH.Stk)
    (rr rs : HvdH.Reg) (bk : List HvdH.Glyph) (hne : k ≠ S) (hrr : rr ≠ rs)
    (hT : ∀ b : Bool, HvdH.Glyph.bit b ≠ T) :
    ∀ (j : ℕ) (r : List Bool) (Scont : List HvdH.Glyph) (s : HvdH.State),
      s.stk k = Work.IntLib.bitsG (List.replicate j true ++ r) ++ T :: bk →
      s.stk S = Scont → s.reg rr = HvdH.Glyph.bit true →
      (r = [] ∨ ∃ r', r = false :: r') →
      ∃ s' n, HvdH.Eval main (.loop rr (HvdH.Glyph.bit true) (Work.IntLib.incBitsLoopBody k S rr rs)) s s' n ∧
        n ≤ 6 * j + 8 ∧
        s'.stk k = Work.IntLib.bitsG r ++ T :: bk ∧
        s'.stk S = List.replicate j (HvdH.Glyph.bit false) ++ Scont ∧
        s'.reg rr = (if r = [] then T else HvdH.Glyph.bit false) ∧
        ∀ j' : HvdH.Stk, j' ≠ k → j' ≠ S → s'.stk j' = s.stk j' := by
  intro j
  induction j with
  | zero =>
    intro r Scont s hk hS hreg hr
    have hk0 : s.stk k = bitsG r ++ T :: bk := by simpa using hk
    rcases hr with h | ⟨r', h⟩
    · subst h
      have hk' : s.stk k = T :: bk := by simpa [Work.IntLib.bitsG] using hk0
      obtain ⟨s', n, hev, hn, hstk, hreg'⟩ :=
        incBitsLoop_final main k S rr rs bk s T hreg hk' (fun h => hT true h.symm)
      refine ⟨s', n, hev, by omega, ?_, ?_, ?_, ?_⟩
      · simp [hstk, Work.IntLib.bitsG, hk0]
      · simpa [hstk] using hS
      · simp [hreg']
      · intro j' _ _; rw [hstk]
    · subst h
      have hk' : s.stk k = Glyph.bit false :: (bitsG r' ++ T :: bk) := by
        simpa [Work.IntLib.bitsG] using hk0
      obtain ⟨s', n, hev, hn, hstk, hreg'⟩ :=
        incBitsLoop_final main k S rr rs (bitsG r' ++ T :: bk) s (Glyph.bit false) hreg hk'
          (by simp)
      refine ⟨s', n, hev, by omega, ?_, ?_, ?_, ?_⟩
      · simp [hstk, Work.IntLib.bitsG, hk0]
      · simpa [hstk] using hS
      · simp [hreg']
      · intro j' _ _; rw [hstk]
  | succ j ih =>
    intro r Scont s hk hS hreg hr
    have hk1 : s.stk k = Glyph.bit true :: (bitsG (List.replicate j true ++ r) ++ T :: bk) := by
      rw [hk]; rfl
    obtain ⟨s₁, hev₁, hk₁, hS₁, hreg₁, hfr₁⟩ :=
      incBitsBody_true main k S rr rs hne hrr s
        (bitsG (List.replicate j true ++ r) ++ T :: bk) Scont hk1 hS
    obtain ⟨s', n, hev, hn, hk', hS', hreg', hfr'⟩ :=
      ih r (Glyph.bit false :: Scont) s₁ hk₁ hS₁ hreg₁ hr
    refine ⟨s', 5 + n + 1, Eval.loopT hreg hev₁ hev, by omega, ?_, ?_, ?_, ?_⟩
    · exact hk'
    · simpa [List.replicate_succ', List.append_assoc] using hS'
    · exact hreg'
    · intro j' hj1 hj2
      rw [hfr' j' hj1 hj2, hfr₁ j' hj1 hj2]

end Work.IntLib
