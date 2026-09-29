import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-!
# `LayoutLib.reverse`

The word walks the list `ofList xs` on stack 0 element by element:

* `peek 0 rA` reads the leading glyph of what remains of the list; `nil` means the list is
  exhausted, otherwise it is `cons`;
* in the `cons` case the glyph is popped, the element `x` (a whole `Val`) is moved aside onto the
  accumulator stack 1 with `mvVal 0 1 2 3`, and a `cons` glyph is pushed in front of the
  accumulator, i.e. `acc := .cons x acc`; the loop flag `rF` is set to `cons` again;
* in the `nil` case the flag is set to `eos`, which ends the (outer) loop.

After the loop, stack 0 holds `nil :: rest'`; the `nil` is dropped and the accumulated value
`ofList xs.reverse` is moved back on top of stack 0.

Everything the movers use lives on stacks 0--3, so the word is a `WordR` with cost
`K * (vsz (ofList xs) + 1)`.
-/

/-! ## Encodings of lists -/

private theorem enc_ofList_cons (x : Val) (ys : List Val) :
    (ofList (x :: ys)).enc = Glyph.cons :: (x.enc ++ (ofList ys).enc) := rfl

private theorem enc_ofList_nil : (ofList ([] : List Val)).enc = [Glyph.nil] := rfl

private theorem enc_val_cons (x y : Val) : (Val.cons x y).enc = Glyph.cons :: (x.enc ++ y.enc) := rfl

private theorem ofList_cons (x : Val) (ys : List Val) : ofList (x :: ys) = Val.cons x (ofList ys) := rfl

private theorem ofList_nil : ofList ([] : List Val) = Val.nil := rfl

private theorem encs_cons' (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

/-! ## Size arithmetic -/

private theorem vsz_enc_cons (x y : Val) : vsz (Val.cons x y) = vsz x + vsz y + 1 := by
  simp [vsz, Val.enc, List.length_append]

private theorem vsz_ofList (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      rw [ofList_cons, vsz_enc_cons, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

private theorem vsz_ofList_reverse (xs : List Val) : vsz (ofList xs.reverse) = vsz (ofList xs) := by
  rw [vsz_ofList, vsz_ofList, List.map_reverse, List.sum_reverse, List.length_reverse]

private theorem sum_map_revCost (xs : List Val) :
    (xs.map (fun x => 16 * (vsz x + 1) + 8)).sum
      = 16 * (xs.map (fun x => vsz x + 1)).sum + 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

private theorem sum_map_vsz_add_one (xs : List Val) :
    (xs.map (fun x => vsz x + 1)).sum = (xs.map vsz).sum + xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-! ## The program -/

/-- loop-flag register; the value movers only use registers 0--4 -/
private def rF : Reg := 5

/-- body of the reversal loop -/
private def revBody : Cmd :=
  .seq (.peek 0 rA)
    (.ite rA Glyph.nil
      (.set rF Glyph.eos)
      (.seq (.pop 0 rB)
        (.seq (mvVal 0 1 2 3)
          (.seq (pushConst 1 Glyph.cons) (.set rF Glyph.cons)))))

/-- cost of the reversal loop on the list `xs` (one iteration per element, plus the final test) -/
private def revCost (xs : List Val) : ℕ := (xs.map (fun x => 16 * (vsz x + 1) + 8)).sum + 4

/-- the reversal program -/
private def revProg : Cmd :=
  .seq (pushConst 1 Glyph.nil)
    (.seq (.set rF Glyph.cons)
      (.seq (.loop rF Glyph.cons revBody)
        (.seq (.pop 0 rA) (mvVal 1 0 2 3))))

private theorem revCostBound (xs : List Val) :
    (xs.map (fun x => 16 * (vsz x + 1) + 8)).sum + 4 ≤ 200 * (vsz (ofList xs) + 1) := by
  rw [sum_map_revCost, sum_map_vsz_add_one, vsz_ofList]
  omega

/-! ## The two one-step lemmas for the loop body -/

/-- the list is exhausted: the body sets the flag to `eos` and changes nothing else -/
private theorem revBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {A : List Glyph}
    (h0 : X 0 = (ofList ([] : List Val)).enc ++ A) :
    ∃ s' n, Ev main revBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk = X ∧ s'.reg rF = Glyph.eos := by
  have hhead : (X 0).headD Glyph.eos = Glyph.nil := by rw [h0]; rfl
  have h1 := ev_peek' (main := main) 0 rA g X
  rw [hhead] at h1
  have h2 : Ev main (.ite rA Glyph.nil (.set rF Glyph.eos)
      (.seq (.pop 0 rB) (.seq (mvVal 0 1 2 3) (.seq (pushConst 1 Glyph.cons) (.set rF Glyph.cons)))))
      ⟨Function.update g rA Glyph.nil, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rF Glyph.eos, X⟩ 2 :=
    Ev.iteT (by simp) (ev_set' (main := main) rF Glyph.eos _ X)
  have h3 : Ev main revBody ⟨g, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rF Glyph.eos, X⟩ 3 := by
    unfold revBody
    exact Ev.seq h1 h2
  exact ⟨_, _, h3, by omega, rfl, by simp⟩

/-- one `cons` is at the head of the list: pop it, move the element onto the accumulator, and push
a `cons` glyph in front of the accumulator -/
private theorem revBody_cons {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {x : Val} {ys : List Val} {acc : Val} {R' B : List Glyph}
    (h0 : X 0 = (ofList (x :: ys)).enc ++ R') (h1 : X 1 = acc.enc ++ B) :
    ∃ s' n, Ev main revBody ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz x + 1) + 7 ∧
      s'.stk 0 = (ofList ys).enc ++ R' ∧ s'.stk 1 = (Val.cons x acc).enc ++ B ∧
      s'.stk 2 = X 2 ∧ s'.stk 3 = X 3 ∧ s'.reg rF = Glyph.cons ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = X k) := by
  have hhead : (X 0).headD Glyph.eos = Glyph.cons := by rw [h0]; rfl
  have htail : (X 0).tail = x.enc ++ ((ofList ys).enc ++ R') := by
    rw [h0, enc_ofList_cons, List.cons_append, List.tail_cons, List.append_assoc]
  have hpeek := ev_peek' (main := main) 0 rA g X
  rw [hhead] at hpeek
  have hpop : Ev main (.pop 0 rB) ⟨Function.update g rA Glyph.cons, X⟩
      ⟨Function.update (Function.update g rA Glyph.cons) rB Glyph.cons,
        Function.update X 0 (X 0).tail⟩ 1 := by
    have h := ev_pop' (main := main) 0 rB (Function.update g rA Glyph.cons) X
    rw [hhead] at h
    exact h
  obtain ⟨s₄, n₄, hmv, hn₄, h4a, h4b, h4c, h4d, h4o⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update (Function.update g rA Glyph.cons) rB Glyph.cons)
      (X := Function.update X 0 (X 0).tail) (v := x)
      (A := (ofList ys).enc ++ R') (B := acc.enc ++ B)
      (by simp only [stkFn_same, htail])
      (by simp only [stkFn_ne X (by decide : (1 : Stk) ≠ 0), h1])
  obtain ⟨s₅, n₅, hpc, hn₅, h5a, h5o, -, -⟩ :=
    pushConst_ev (main := main) (k := 1) (cst := Glyph.cons) (g := s₄.reg) (X := s₄.stk)
  have hset : Ev main (.set rF Glyph.cons) s₅
      ⟨Function.update s₅.reg rF Glyph.cons, s₅.stk⟩ 1 :=
    ev_set' (main := main) rF Glyph.cons s₅.reg s₅.stk
  have hbranch : Ev main (.seq (.pop 0 rB)
        (.seq (mvVal 0 1 2 3) (.seq (pushConst 1 Glyph.cons) (.set rF Glyph.cons))))
      ⟨Function.update g rA Glyph.cons, X⟩ ⟨Function.update s₅.reg rF Glyph.cons, s₅.stk⟩
      (1 + (n₄ + (n₅ + 1))) :=
    Ev.seq hpop (Ev.seq hmv (Ev.seq hpc hset))
  have hite : Ev main (.ite rA Glyph.nil (.set rF Glyph.eos)
        (.seq (.pop 0 rB) (.seq (mvVal 0 1 2 3) (.seq (pushConst 1 Glyph.cons) (.set rF Glyph.cons)))))
      ⟨Function.update g rA Glyph.cons, X⟩ ⟨Function.update s₅.reg rF Glyph.cons, s₅.stk⟩
      ((1 + (n₄ + (n₅ + 1))) + 1) :=
    Ev.iteF (by simp) hbranch
  have hbody : Ev main revBody ⟨g, X⟩
      ⟨Function.update s₅.reg rF Glyph.cons, s₅.stk⟩
      (1 + ((1 + (n₄ + (n₅ + 1))) + 1)) := by
    unfold revBody
    exact Ev.seq hpeek hite
  have hle : 1 + ((1 + (n₄ + (n₅ + 1))) + 1) ≤ 16 * (vsz x + 1) + 7 := by omega
  obtain ⟨n, hev, hle'⟩ := hbody.mono hle
  refine ⟨_, n, ⟨n, hev, le_rfl⟩, hle', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h5o 0 (by decide), h4a]
  · rw [h5a, h4b]
    simp only [enc_val_cons, List.cons_append, List.append_assoc]
  · rw [h5o 2 (by decide), h4c]
    exact Function.update_of_ne (by decide : (2 : Stk) ≠ 0) (X 0).tail X
  · rw [h5o 3 (by decide), h4d]
    exact Function.update_of_ne (by decide : (3 : Stk) ≠ 0) (X 0).tail X
  · simp
  · intro k hk0 hk1 hk2 hk3
    rw [h5o k hk1, h4o k hk0 hk1 hk2 hk3]
    exact Function.update_of_ne hk0 (X 0).tail X

/-! ## The loop -/

private theorem rev_loop {main : Cmd} :
    ∀ (xs : List Val), ∀ (zs : List Val) (R' B : List Glyph) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      g rF = Glyph.cons → X 0 = (ofList xs).enc ++ R' → X 1 = (ofList zs).enc ++ B →
      ∃ s', loopRuns main rF Glyph.cons revBody (xs.length + 1) ⟨g, X⟩ s' (revCost xs) ∧
        s'.stk 0 = (ofList ([] : List Val)).enc ++ R' ∧
        s'.stk 1 = (ofList (xs.reverse ++ zs)).enc ++ B ∧
        s'.reg rF = Glyph.eos ∧ s'.stk 2 = X 2 ∧ s'.stk 3 = X 3 ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = X k) := by
  intro xs
  induction xs with
  | nil =>
      intro zs R' B g X hrf h0 h1
      obtain ⟨s', n, hev, hn, hstk, hreg⟩ :=
        revBody_stop (main := main) (g := g) (X := X) (A := R') h0
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine loopRuns.mono (by omega) (loopRuns.one hrf hev) ?_
        simp only [revCost, List.map_nil, List.sum_nil]
        omega
      · rw [hstk, h0]
      · rw [hstk, h1]
        simp
      · rw [hreg]
      · rw [hstk]
      · rw [hstk]
      · intro k hk0 hk1 hk2 hk3
        rw [hstk]
  | cons x xs ih =>
      intro zs R' B g X hrf h0 h1
      obtain ⟨s₁, n₁, hev₁, hn₁, h1a, h1b, h1c, h1d, h1r, h1o⟩ :=
        revBody_cons (main := main) (g := g) (X := X) (x := x) (ys := xs)
          (acc := ofList zs) (R' := R') (B := B) h0 h1
      have h1b' : s₁.stk 1 = (ofList (x :: zs)).enc ++ B := by
        rw [ofList_cons]; exact h1b
      obtain ⟨s₂, hrun₂, h2a, h2b, h2r, h2c, h2d, h2o⟩ :=
        ih (x :: zs) R' B s₁.reg s₁.stk h1r h1a h1b'
      have hcost : (n₁ + 1) + revCost xs ≤ revCost (x :: xs) := by
        simp only [revCost, List.map_cons, List.sum_cons]
        omega
      have hcat := loopRuns.concat (xs.length + 1) (loopRuns.one hrf hev₁) hrun₂
      have hcat1 : loopRuns main rF Glyph.cons revBody ((x :: xs).length + 1) ⟨g, X⟩ s₂
          (n₁ + 1 + revCost xs) :=
        loopRuns.cast (by simp only [List.length_cons]; omega) hcat
      have hcat2 : loopRuns main rF Glyph.cons revBody ((x :: xs).length + 1) ⟨g, X⟩ s₂
          (revCost (x :: xs)) :=
        loopRuns.mono (by simp only [List.length_cons]; omega) hcat1 hcost
      refine ⟨s₂, hcat2, h2a, ?_, h2r, ?_, ?_, ?_⟩
      · rw [h2b]
        congr 1
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      · rw [h2c, h1c]
      · rw [h2d, h1d]
      · intro k hk0 hk1 hk2 hk3
        rw [h2o k hk0 hk1 hk2 hk3, h1o k hk0 hk1 hk2 hk3]

/-! ## The program is a `WordR` -/

private theorem cmdTouches_revProg : cmdTouches revProg = {0, 1, 2, 3} := by
  simp only [revProg, revBody, cmdTouches, mvVal, mvA, mvAInit, mvABody, mvAPrefix, decStep,
    pushConst, cmdTouches_mvB]
  decide

/-- **`LayoutLib.reverse`**: walk `ofList xs` element by element (pop the leading `cons` glyph, move the
element aside with `Work.Layout.mvVal`), consing each element onto an accumulator list (`consV`-style:
move the element above the accumulator and insert a `cons` glyph in front by moving it aside). -/
theorem reverseWord : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
    (fun _ => K * (vsz (ofList xs) + 1)) := by
  refine ⟨revProg, 250, ?_⟩
  intro main xs vs hpre s R hs
  obtain ⟨rest, rfl⟩ := hpre
  have hs0 : s.stk 0 = (ofList xs).enc ++ (encs rest ++ R) := by
    rw [hs, encs_cons', List.append_assoc]
  -- accumulator stack 1 := nil
  obtain ⟨s₁, n₁, hpc₁, hn₁, h1a, h1o, -, -⟩ :=
    pushConst_ev (main := main) (k := 1) (cst := Glyph.nil) (g := s.reg) (X := s.stk)
  have h1b : s₁.stk 0 = (ofList xs).enc ++ (encs rest ++ R) := by
    rw [h1o 0 (by decide)]; exact hs0
  have h1c : s₁.stk 1 = (ofList ([] : List Val)).enc ++ (s.stk 1) := by
    rw [h1a]; rfl
  -- loop flag := cons, then the loop
  have hset : Ev main (.set rF Glyph.cons) s₁
      ⟨Function.update s₁.reg rF Glyph.cons, s₁.stk⟩ 1 :=
    ev_set' (main := main) rF Glyph.cons s₁.reg s₁.stk
  obtain ⟨s₃, hrun₃, h3a, h3b, h3r, h3c, h3d, h3o⟩ :=
    rev_loop (main := main) xs [] (encs rest ++ R) (s.stk 1)
      (Function.update s₁.reg rF Glyph.cons) s₁.stk (by simp) h1b h1c
  have hloop : Ev main (.loop rF Glyph.cons revBody)
      ⟨Function.update s₁.reg rF Glyph.cons, s₁.stk⟩ s₃ (revCost xs + 1) :=
    loopRuns.eval hrun₃ (by rw [h3r]; decide)
  -- drop the trailing `nil` of the exhausted list
  have hpop : Ev main (.pop 0 rA) s₃
      ⟨Function.update s₃.reg rA ((s₃.stk 0).headD Glyph.eos),
        Function.update s₃.stk 0 (s₃.stk 0).tail⟩ 1 :=
    ev_pop' (main := main) 0 rA s₃.reg s₃.stk
  have htail : (s₃.stk 0).tail = encs rest ++ R := by rw [h3a]; rfl
  -- move the accumulator back onto stack 0
  obtain ⟨s₅, n₅, hmv, hn₅, h5a, h5b, h5c, h5d, h5o⟩ :=
    mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update s₃.reg rA ((s₃.stk 0).headD Glyph.eos))
      (X := Function.update s₃.stk 0 (s₃.stk 0).tail)
      (v := ofList xs.reverse) (A := s.stk 1) (B := encs rest ++ R)
      (by simp only [stkFn_ne s₃.stk (by decide : (1 : Stk) ≠ 0), h3b, List.append_nil])
      (by simp only [stkFn_same, htail])
  -- assemble
  have hbody : Ev main revProg s s₅ (n₁ + (1 + (revCost xs + 1 + (1 + n₅)))) := by
    unfold revProg
    exact Ev.seq hpc₁ (Ev.seq hset (Ev.seq hloop (Ev.seq hpop hmv)))
  have hcost : n₁ + (1 + (revCost xs + 1 + (1 + n₅))) ≤ 250 * (vsz (ofList xs) + 1) := by
    have h1 : n₁ ≤ 2 := hn₁
    have h2 : n₅ ≤ 16 * (vsz (ofList xs) + 1) := by
      rw [← vsz_ofList_reverse xs]; exact hn₅
    have h3 : revCost xs ≤ 200 * (vsz (ofList xs) + 1) := revCostBound xs
    have h4 : 1 ≤ vsz (ofList xs) := one_le_vsz _
    omega
  obtain ⟨n, hev, hn⟩ := hbody.mono hcost
  refine ⟨ofList xs.reverse :: rest, s₅, n, ⟨rest, rfl, rfl⟩, hev, hn, ?_, ?_⟩
  · rw [h5b, encs_cons', List.append_assoc]
  · intro k hk
    have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3) := by
      by_cases h1 : k = 1
      · exact Or.inl h1
      by_cases h2 : k = 2
      · exact Or.inr (Or.inl h2)
      by_cases h3 : k = 3
      · exact Or.inr (Or.inr (Or.inl h3))
      exact Or.inr (Or.inr (Or.inr ⟨hk, h1, h2, h3⟩))
    rcases hk' with rfl | rfl | rfl | ⟨hk0, hk1, hk2, hk3⟩
    · exact h5a
    · rw [h5c, Function.update_of_ne (by decide : (2 : Stk) ≠ 0), h3c, h1o 2 (by decide)]
    · rw [h5d, Function.update_of_ne (by decide : (3 : Stk) ≠ 0), h3d, h1o 3 (by decide)]
    · rw [h5o k hk1 hk0 hk2 hk3, Function.update_of_ne hk0 (s₃.stk 0).tail s₃.stk,
        h3o k hk0 hk1 hk2 hk3, h1o k hk1]

end Work.Layout
