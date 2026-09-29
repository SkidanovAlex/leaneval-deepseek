import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.reverseWord
import Submission.Work.Layout.size_two_pow_sub_one

/-!
# Layout: `LayoutLib.length` — keep the list, push its length

The word walks the list `ofList xs` on stack 0 element by element (as in
`Submission/Work/Layout/reverseWord.lean`):

* `peek 0 rA` reads the leading glyph of what remains of the list; `nil` means the list is
  exhausted, otherwise it is `cons`;
* in the `cons` case the glyph is popped, the element `x` (a whole `Val`) is moved aside onto the
  accumulator stack 1 with `mvVal 0 1 2 3`, a `cons` glyph is pushed in front of the accumulator
  (so the accumulator becomes `ofList xs.reverse`), and a *cell* `cons (.int 1) …` is pushed on the
  counting stack 4 (so stack 4 becomes `ones k = ofList (replicate k (.int 1))`, `k` = number of
  elements processed).

After the loop, the reversed accumulator is moved back onto stack 0 and reversed by the library
word `LayoutLib.reverse` (proved in `reverseWord.lean`), so stack 0 holds `ofList xs` again; the
counting list `ones k`, followed by `.int 1`, is moved on top of it, and the library words
`IntLib.evalPoly` (with `b = 1`) and `IntLib.size` turn `ones k, 1` into `int (2^k - 1)`, resp.
`int k`.  Hence the output stack is `int xs.length :: ofList xs :: rest`, at cost
`K * (vsz (ofList xs) + 1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Layout

open HvdH

/-! ## 0. Arithmetic and encoding helpers -/

theorem ofList_cons_lw (x : Val) (ys : List Val) : ofList (x :: ys) = Val.cons x (ofList ys) := rfl

theorem enc_ofList_cons_lw (x : Val) (ys : List Val) :
    (ofList (x :: ys)).enc = Glyph.cons :: (x.enc ++ (ofList ys).enc) := rfl

theorem enc_val_cons_lw (x y : Val) : (Val.cons x y).enc = Glyph.cons :: (x.enc ++ y.enc) := rfl

theorem vsz_cons_lw (x y : Val) : vsz (Val.cons x y) = vsz x + vsz y + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

theorem vsz_ofList_lw (xs : List Val) :
    vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      rw [ofList_cons_lw, vsz_cons_lw, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem vsz_ofList_reverse_lw (xs : List Val) :
    vsz (ofList xs.reverse) = vsz (ofList xs) := by
  rw [vsz_ofList_lw, vsz_ofList_lw, List.map_reverse, List.sum_reverse, List.length_reverse]

theorem length_le_vsz_ofList_lw (xs : List Val) : xs.length ≤ vsz (ofList xs) := by
  rw [vsz_ofList_lw]; omega

theorem sum_map_vsz_add_one_lw (xs : List Val) :
    (xs.map (fun x => vsz x + 1)).sum = (xs.map vsz).sum + xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem sum_range_two_lw (k : ℕ) : ((List.range k).map (fun j => 2 ^ j)).sum = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [pow_succ]
    have h2 : (2 : ℕ) ^ k * 2 = 2 * 2 ^ k := Nat.mul_comm _ _
    rw [h2]
    have h1 : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_two_pow
    omega

theorem evalChunks_replicate_lw (k : ℕ) : evalChunks (List.replicate k 1) 1 = 2 ^ k - 1 := by
  have h : evalChunks (List.replicate k 1) 1 = ((List.range k).map fun j => 2 ^ j).sum := by
    simp only [evalChunks, List.length_replicate]
    exact congrArg List.sum (List.map_congr_left (fun j hj => by
      rw [List.getD_replicate 1 (i := j) (n := k) (y := 0) (by simpa using List.mem_range.mp hj)]
      simp))
  rw [h, sum_range_two_lw k]

theorem isz_int_one_lw : isz (1 : ℤ) = 3 := rfl

theorem encs_cons_lw (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

/-! ## 0b. Pushing a literal list of glyphs onto a fixed stack -/

/-- `pushConsts l k` pushes the glyphs of `l` onto stack `k`, first element first, so that the top
of stack `k` afterwards is `l.reverse`. -/
def pushConsts (l : List Glyph) (k : Stk) : Cmd := seqs (l.map (fun cst => pushConst k cst))

theorem pushConsts_single (c : Glyph) (k : Stk) : pushConsts [c] k = pushConst k c := rfl

theorem pushConsts_cons_cons (c d : Glyph) (t : List Glyph) (k : Stk) :
    pushConsts (c :: d :: t) k = .seq (pushConst k c) (pushConsts (d :: t) k) := rfl

theorem pushConstsEv {main : Cmd} {k : Stk} :
    ∀ (l : List Glyph) {g : Reg → Glyph} {X : Stk → List Glyph},
      ∃ s' n, Ev main (pushConsts l k) ⟨g,X⟩ s' n ∧ n ≤ 2 * l.length + 1 ∧
        s'.stk k = l.reverse ++ X k ∧ (∀ k', k' ≠ k → s'.stk k' = X k') := by
  intro l
  induction l with
  | nil => intro g X; exact ⟨⟨g,X⟩, 1, ev_skip main ⟨g,X⟩, by simp, by simp, by simp⟩
  | cons c t ih =>
      intro g X
      obtain ⟨s₁, n₁, h₁, hn₁, hk₁, ho₁⟩ :=
        pushConst_ev (main := main) (k := k) (cst := c) (g := g) (X := X)
      cases t with
      | nil =>
          refine ⟨s₁, n₁, ?_, by simp only [List.length_cons, List.length_nil]; omega, ?_, ?_⟩
          · simpa [pushConsts, seqs] using h₁
          · simpa using hk₁
          · simpa using ho₁.1
      | cons d t' =>
          obtain ⟨s₂, n₂, h₂, hn₂, hk₂, ho₂⟩ := ih (g := s₁.reg) (X := s₁.stk)
          refine ⟨s₂, n₁ + n₂, ?_, ?_, ?_, ?_⟩
          · rw [show pushConsts (c :: d :: t') k = .seq (pushConst k c) (pushConsts (d :: t') k) from rfl]
            exact Ev.seq h₁ h₂
          · have h2 : n₂ ≤ 2 * (d :: t').length + 1 := hn₂
            have h1 : n₁ ≤ 2 := hn₁
            simp only [List.length_cons] at *
            omega
          · rw [hk₂, hk₁]
            simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
          · intro k' hk'
            rw [ho₂ k' hk', ho₁.1 k' hk']

/-! ## 1. Definitions -/

/-- loop-flag register; the value movers only use registers 0–4. -/
def rF_lw : Reg := 5

/-- The value `ofList (replicate k (.int 1))`: a list of `k` ones. -/
def ones (k : ℕ) : Val := ofList (List.replicate k (Val.int 1))

theorem ones_zero_lw : ones 0 = Val.nil := rfl

theorem ones_enc_succ_lw (j : ℕ) :
    (ones (j + 1)).enc = Glyph.cons :: ((Val.int 1).enc ++ (ones j).enc) := rfl

theorem enc_int_one_lw : (Val.int 1).enc = [Glyph.pos, Glyph.bit true, Glyph.iend] := rfl

theorem ofList_nil_enc_lw : (ofList ([] : List Val)).enc = [Glyph.nil] := rfl

theorem ones_zero_enc_lw : (ones 0).enc = [Glyph.nil] := rfl

theorem reverse_singleton_lw (a : Glyph) : [a].reverse = [a] := by simp

theorem sum_replicate_three (k : ℕ) : (List.replicate k (3 : ℕ)).sum = 3 * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.sum_cons, ih]; ring

theorem vsz_ones_lw (k : ℕ) : vsz (ones k) = 4 * k + 1 := by
  rw [ones, vsz_ofList_lw]
  simp only [List.length_replicate, List.map_replicate]
  have h3 : vsz (Val.int 1) = 3 := rfl
  rw [h3, sum_replicate_three]
  ring

theorem isz_one_nat_lw : isz ((1 : ℕ) : ℤ) = 3 := rfl

theorem bind_cast_replicate_lw (k : ℕ) :
    ((List.replicate k 1) >>= (fun a : ℕ => pure (a : ℤ))) = List.replicate k (1 : ℤ) := by
  rw [List.bind_eq_flatMap]
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.flatMap_cons]
      rw [ih]
      simp

theorem intList_replicate_lw (k : ℕ) : intList (List.replicate k 1) = ones k := by
  unfold intList ones
  simp only [bind_cast_replicate_lw, List.map_replicate]

/-- body of the counting/reversal loop -/
def lenWalkBody : Cmd :=
  seqs [.peek 0 rA,
    .ite rA Glyph.nil (.set rF_lw Glyph.eos)
      (seqs [.pop 0 rB, mvVal 0 1 2 3, pushConst 1 Glyph.cons,
             pushConsts [Glyph.iend, Glyph.bit true, Glyph.pos, Glyph.cons] 4,
             .set rF_lw Glyph.cons])]

/-- cost of the counting loop on the list `xs` -/
def lenWalkCost (xs : List Val) : ℕ := (xs.map (fun x => 16 * (vsz x + 1) + 17)).sum + 4

theorem lenWalkCost_eq (xs : List Val) :
    lenWalkCost xs = 16 * ((xs.map fun x => vsz x + 1).sum) + 17 * xs.length + 4 := by
  unfold lenWalkCost
  have h : ∀ ys : List Val, (ys.map (fun x => 16 * (vsz x + 1) + 17)).sum
      = 16 * ((ys.map fun x => vsz x + 1).sum) + 17 * ys.length := by
    intro ys
    induction ys with
    | nil => simp
    | cons x ys ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [h]

/-- the `length` program skeleton (parameterised by the three library words it calls) -/
def lenProg (prev pev psz : Cmd) : Cmd :=
  seqs [pushConsts [Glyph.nil] 1,
        pushConsts [Glyph.nil] 4,
        .set rF_lw Glyph.cons,
        .loop rF_lw Glyph.cons lenWalkBody,
        .pop 0 rA,
        mvVal 1 0 2 3,
        prev,
        pushConsts ((Val.int 1).enc.reverse) 4,
        mvVal 4 0 2 3,
        mvVal 4 0 2 3,
        pev,
        psz]

/-! ## 2. The walk loop -/

theorem lenWalkBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {A : List Glyph}
    (h0 : X 0 = (ofList ([] : List Val)).enc ++ A) :
    ∃ s' n, Ev main lenWalkBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk = X ∧ s'.reg rF_lw = Glyph.eos := by
  have hhead : (X 0).headD Glyph.eos = Glyph.nil := by rw [h0]; rfl
  have h1 := ev_peek' (main := main) 0 rA g X
  rw [hhead] at h1
  have h2 : Ev main (.ite rA Glyph.nil (.set rF_lw Glyph.eos)
      (seqs [.pop 0 rB, mvVal 0 1 2 3, pushConst 1 Glyph.cons,
             pushConsts [Glyph.iend, Glyph.bit true, Glyph.pos, Glyph.cons] 4,
             .set rF_lw Glyph.cons]))
      ⟨Function.update g rA Glyph.nil, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rF_lw Glyph.eos, X⟩ 2 :=
    Ev.iteT (by simp) (ev_set' (main := main) rF_lw Glyph.eos _ X)
  have h3 : Ev main lenWalkBody ⟨g, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rF_lw Glyph.eos, X⟩ 3 := by
    unfold lenWalkBody
    simp only [seqs]
    exact Ev.seq h1 h2
  exact ⟨_, _, h3, le_rfl, rfl, by simp⟩

theorem lenWalkBody_cons {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {x : Val} {ys : List Val} {acc : Val} {j : ℕ} {R' B X4 : List Glyph}
    (h0 : X 0 = (ofList (x :: ys)).enc ++ R') (h1 : X 1 = acc.enc ++ B)
    (h4 : X 4 = (ones j).enc ++ X4) :
    ∃ s' n, Ev main lenWalkBody ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz x + 1) + 16 ∧
      s'.stk 0 = (ofList ys).enc ++ R' ∧ s'.stk 1 = (Val.cons x acc).enc ++ B ∧
      s'.stk 4 = (ones (j + 1)).enc ++ X4 ∧
      s'.reg rF_lw = Glyph.cons ∧ s'.stk 2 = X 2 ∧ s'.stk 3 = X 3 ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → s'.stk k = X k) := by
  have hhead : (X 0).headD Glyph.eos = Glyph.cons := by rw [h0]; rfl
  have htail : (X 0).tail = x.enc ++ ((ofList ys).enc ++ R') := by
    rw [h0, enc_ofList_cons_lw, List.cons_append, List.tail_cons, List.append_assoc]
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
      (by rw [Function.update_self, htail])
      (by rw [Function.update_of_ne (by decide : (1 : Stk) ≠ 0), h1])
  obtain ⟨s₅, n₅, hpc, hn₅, h5a, h5o⟩ :=
    pushConstsEv (main := main) (k := 1) [Glyph.cons] (g := s₄.reg) (X := s₄.stk)
  obtain ⟨s₆, n₆, hce, hn₆, h6a, h6o⟩ :=
    pushConstsEv (main := main) (k := 4) [Glyph.iend, Glyph.bit true, Glyph.pos, Glyph.cons]
      (g := s₅.reg) (X := s₅.stk)
  have hset : Ev main (.set rF_lw Glyph.cons) s₆ ⟨Function.update s₆.reg rF_lw Glyph.cons, s₆.stk⟩ 1 :=
    ev_set' (main := main) rF_lw Glyph.cons s₆.reg s₆.stk
  have hbranch : Ev main (seqs [.pop 0 rB, mvVal 0 1 2 3, pushConst 1 Glyph.cons,
        pushConsts [Glyph.iend, Glyph.bit true, Glyph.pos, Glyph.cons] 4, .set rF_lw Glyph.cons])
      ⟨Function.update g rA Glyph.cons, X⟩ ⟨Function.update s₆.reg rF_lw Glyph.cons, s₆.stk⟩
      (1 + (n₄ + (n₅ + (n₆ + 1)))) :=
    Ev.seq hpop (Ev.seq hmv (Ev.seq hpc (Ev.seq hce hset)))
  have hbody : Ev main lenWalkBody ⟨g, X⟩ ⟨Function.update s₆.reg rF_lw Glyph.cons, s₆.stk⟩
      (1 + ((1 + (n₄ + (n₅ + (n₆ + 1)))) + 1)) := by
    unfold lenWalkBody
    simp only [seqs]
    exact Ev.seq hpeek (Ev.iteF (by simp) hbranch)
  have hx2 : Function.update X 0 (X 0).tail 2 = X 2 :=
    Function.update_of_ne (by decide : (2 : Stk) ≠ 0) (X 0).tail X
  have hx3 : Function.update X 0 (X 0).tail 3 = X 3 :=
    Function.update_of_ne (by decide : (3 : Stk) ≠ 0) (X 0).tail X
  have hx4 : Function.update X 0 (X 0).tail 4 = X 4 :=
    Function.update_of_ne (by decide : (4 : Stk) ≠ 0) (X 0).tail X
  have hres0 : s₆.stk 0 = (ofList ys).enc ++ R' := by
    rw [h6o 0 (by decide), h5o 0 (by decide), h4a]
  have hres1 : s₆.stk 1 = (Val.cons x acc).enc ++ B := by
    rw [h6o 1 (by decide), h5a, h4b]
    simp only [enc_val_cons_lw, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc]
  have hres4 : s₆.stk 4 = (ones (j + 1)).enc ++ X4 := by
    rw [h6a, h5o 4 (by decide),
      h4o 4 (by decide) (by decide) (by decide) (by decide), hx4, h4]
    rw [ones_enc_succ_lw, enc_int_one_lw]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc]
  have hresreg : (⟨Function.update s₆.reg rF_lw Glyph.cons, s₆.stk⟩ : State).reg rF_lw = Glyph.cons := by
    simp
  have hres2 : s₆.stk 2 = X 2 := by
    rw [h6o 2 (by decide), h5o 2 (by decide), h4c, hx2]
  have hres3 : s₆.stk 3 = X 3 := by
    rw [h6o 3 (by decide), h5o 3 (by decide), h4d, hx3]
  have hresoth : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 →
      (⟨Function.update s₆.reg rF_lw Glyph.cons, s₆.stk⟩ : State).stk k = X k := by
    intro k hk0 hk1 hk2 hk3 hk4
    show s₆.stk k = X k
    rw [h6o k hk4, h5o k hk1, h4o k hk0 hk1 hk2 hk3]
    exact Function.update_of_ne hk0 (X 0).tail X
  have hrescost : (1 + ((1 + (n₄ + (n₅ + (n₆ + 1)))) + 1)) ≤ 16 * (vsz x + 1) + 16 := by
    have h4 : n₄ ≤ 16 * (vsz x + 1) := hn₄
    have h5 : n₅ ≤ 3 := by
      have := hn₅; simp only [List.length_cons, List.length_nil] at this; omega
    have h6 : n₆ ≤ 9 := by
      have := hn₆; simp only [List.length_cons, List.length_nil] at this; omega
    omega
  exact ⟨⟨Function.update s₆.reg rF_lw Glyph.cons, s₆.stk⟩, _, hbody, hrescost, hres0, hres1,
    hres4, hresreg, hres2, hres3, hresoth⟩

theorem lenWalk_loop {main : Cmd} :
    ∀ (xs zs : List Val) (R' B X4 : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      g rF_lw = Glyph.cons → X 0 = (ofList xs).enc ++ R' → X 1 = (ofList zs).enc ++ B →
      X 4 = (ones zs.length).enc ++ X4 →
      ∃ s', loopRuns main rF_lw Glyph.cons lenWalkBody (xs.length + 1) ⟨g, X⟩ s' (lenWalkCost xs) ∧
        s'.stk 0 = (ofList ([] : List Val)).enc ++ R' ∧
        s'.stk 1 = (ofList (xs.reverse ++ zs)).enc ++ B ∧
        s'.stk 4 = (ones (zs.length + xs.length)).enc ++ X4 ∧
        s'.reg rF_lw = Glyph.eos ∧ s'.stk 2 = X 2 ∧ s'.stk 3 = X 3 ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → s'.stk k = X k) := by
  intro xs
  induction xs with
  | nil =>
      intro zs R' B X4 g X hrf h0 h1 h4
      obtain ⟨s', n, hev, hn, hstk, hreg⟩ :=
        lenWalkBody_stop (main := main) (g := g) (X := X) (A := R') h0
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine loopRuns.mono (by omega) (loopRuns.one hrf hev) ?_
        simp only [lenWalkCost, List.map_nil, List.sum_nil]
        omega
      · rw [hstk, h0]
      · rw [hstk, h1, List.reverse_nil, List.nil_append]
      · rw [hstk, h4, List.length_nil, Nat.add_zero]
      · rw [hreg]
      · rw [hstk]
      · rw [hstk]
      · intro k hk0 hk1 hk2 hk3 hk4
        rw [hstk]
  | cons x xs ih =>
      intro zs R' B X4 g X hrf h0 h1 h4
      obtain ⟨s₁, n₁, hev₁, hn₁, h1a, h1b, h1c, h1r, h1s2, h1s3, h1o⟩ :=
        lenWalkBody_cons (main := main) (g := g) (X := X) (x := x) (ys := xs)
          (acc := ofList zs) (j := zs.length) (R' := R') (B := B) (X4 := X4) h0 h1 h4
      have h1b' : s₁.stk 1 = (ofList (x :: zs)).enc ++ B := by
        rw [ofList_cons_lw]; exact h1b
      have h1c' : s₁.stk 4 = (ones (x :: zs).length).enc ++ X4 := by
        rw [h1c]; rfl
      obtain ⟨s₂, hrun₂, h2a, h2b, h2c, h2r, h2s2, h2s3, h2o⟩ :=
        ih (x :: zs) R' B X4 s₁.reg s₁.stk h1r h1a h1b' h1c'
      have hcost : (n₁ + 1) + lenWalkCost xs ≤ lenWalkCost (x :: xs) := by
        rw [lenWalkCost_eq, lenWalkCost_eq]
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      have hcat := loopRuns.concat (xs.length + 1) (loopRuns.one hrf hev₁) hrun₂
      have hcat1 : loopRuns main rF_lw Glyph.cons lenWalkBody ((x :: xs).length + 1)
          ⟨g, X⟩ s₂ (n₁ + 1 + lenWalkCost xs) :=
        loopRuns.cast (by simp only [List.length_cons]; omega) hcat
      have hcat2 : loopRuns main rF_lw Glyph.cons lenWalkBody ((x :: xs).length + 1)
          ⟨g, X⟩ s₂ (lenWalkCost (x :: xs)) :=
        loopRuns.mono (by simp only [List.length_cons]; omega) hcat1 hcost
      refine ⟨s₂, hcat2, h2a, ?_, ?_, h2r, ?_, ?_, ?_⟩
      · rw [h2b]
        congr 1
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      · rw [h2c]
        congr 1
        have hidx : (x :: zs).length + xs.length = zs.length + (x :: xs).length := by
          simp only [List.length_cons]; omega
        rw [hidx]
      · rw [h2s2, h1s2]
      · rw [h2s3, h1s3]
      · intro k hk0 hk1 hk2 hk3 hk4
        rw [h2o k hk0 hk1 hk2 hk3 hk4, h1o k hk0 hk1 hk2 hk3 hk4]

/-! ## 3. Instantiating the three library words -/

theorem reverseEv_lw {main : Cmd} {prev : Cmd} {Krev : ℕ}
    (hrev : ∀ (ys : List Val), WordR main prev
      (fun vs => ∃ r, vs = ofList ys :: r)
      (fun vs out => ∃ r, vs = ofList ys :: r ∧ out = ofList ys.reverse :: r)
      (fun _ => Krev * (vsz (ofList ys) + 1))) :
    ∀ (ys : List Val) (rvs : List Val) (R : List Glyph) {g : Reg → Glyph} {X : Stk → List Glyph},
      X 0 = encs (ofList ys :: rvs) ++ R →
      ∃ s' n, Eval main prev ⟨g, X⟩ s' n ∧ n ≤ Krev * (vsz (ofList ys) + 1) ∧
        s'.stk 0 = encs (ofList ys.reverse :: rvs) ++ R ∧ (∀ j, j ≠ 0 → s'.stk j = X j) := by
  intro ys rvs R g X h0
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ :=
    hrev ys (ofList ys :: rvs) ⟨rvs, rfl⟩ ⟨g, X⟩ R h0
  obtain ⟨r, hvs, hout⟩ := hpost
  have hr : r = rvs := ((List.cons.inj hvs).2).symm
  have hout' : out = ofList ys.reverse :: rvs := by rw [hout, hr]
  refine ⟨s', n, hev, hn, ?_, hoth⟩
  rw [hstk, hout']

theorem evalPolyEv_lw {main : Cmd} {pev : Cmd} {Ke : ℕ}
    (hev : ∀ (hs : List ℕ) (b : ℕ), 1 ≤ b → (∀ h ∈ hs, h < 2 ^ (3 * b)) →
      WordR main pev (fun vs => ∃ r, vs = intList hs :: .int b :: r)
        (fun vs out => ∃ r, vs = intList hs :: .int b :: r ∧ out = .int (evalChunks hs b) :: r)
        (fun _ => Ke * ((hs.map fun h => isz h).sum + hs.length * (b + 1) + isz b + 1))) :
    ∀ (k : ℕ) (rvs : List Val) (R : List Glyph) {g : Reg → Glyph} {X : Stk → List Glyph},
      X 0 = encs (intList (List.replicate k 1) :: .int 1 :: rvs) ++ R →
      ∃ s' n, Eval main pev ⟨g, X⟩ s' n ∧ n ≤ Ke * (5 * k + 4) ∧
        s'.stk 0 = encs (.int (evalChunks (List.replicate k 1) 1) :: rvs) ++ R ∧
        (∀ j, j ≠ 0 → s'.stk j = X j) := by
  intro k rvs R g X h0
  have hb : 1 ≤ (1 : ℕ) := le_rfl
  have hsmall : ∀ h ∈ List.replicate k 1, h < 2 ^ (3 * 1) := by
    intro h hh
    rw [List.mem_replicate] at hh
    omega
  obtain ⟨out, s', n, hpost, hev', hn, hstk, hoth⟩ :=
    hev (List.replicate k 1) 1 hb hsmall (intList (List.replicate k 1) :: .int 1 :: rvs)
      ⟨rvs, rfl⟩ ⟨g, X⟩ R h0
  obtain ⟨r, hvs, hout⟩ := hpost
  have hr : r = rvs := ((List.cons.inj (List.cons.inj hvs).2).2).symm
  have hout' : out = .int (evalChunks (List.replicate k 1) 1) :: rvs := by rw [hout, hr]
  have hcost : n ≤ Ke * (5 * k + 4) := by
    have hn' := hn
    dsimp only at hn'
    simp only [bind_cast_replicate_lw, List.map_replicate, isz_int_one_lw,
      sum_replicate_three, List.length_replicate] at hn'
    have hkey : Ke * (3 * k + k * (1 + 1) + 3 + 1) ≤ Ke * (5 * k + 4) := by
      refine Nat.mul_le_mul_left Ke ?_
      omega
    exact le_trans hn' hkey
  refine ⟨s', n, hev', hcost, ?_, hoth⟩
  rw [hstk, hout']

theorem sizeEv_lw {main : Cmd} {psz : Cmd} {Ksz : ℕ}
    (hsz : UnOp main psz (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => Ksz * isz a)) :
    ∀ (k m : ℕ) (rvs : List Val) (R : List Glyph) {g : Reg → Glyph} {X : Stk → List Glyph},
      m = 2 ^ k - 1 → X 0 = encs (.int (m : ℤ) :: rvs) ++ R →
      ∃ s' n, Eval main psz ⟨g, X⟩ s' n ∧ n ≤ Ksz * (k + 2) ∧
        s'.stk 0 = encs (.int (k : ℤ) :: rvs) ++ R ∧ (∀ j, j ≠ 0 → s'.stk j = X j) := by
  intro k m rvs R g X hm h0
  unfold UnOp at hsz
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ :=
    hsz (.int (m : ℤ) :: rvs) ⟨(m : ℤ), rvs, rfl, trivial⟩ ⟨g, X⟩ R h0
  obtain ⟨a, r, hvs, hout⟩ := hpost
  have ha : a = (m : ℤ) := (Val.int.inj (List.cons.inj hvs).1).symm
  have hr : r = rvs := ((List.cons.inj hvs).2).symm
  have hsize : ((m : ℤ)).natAbs.size = k := by
    rw [Int.natAbs_natCast, hm, size_two_pow_sub_one]
  have hsize' : m.size = k := by simpa only [Int.natAbs_natCast] using hsize
  have hout' : out = .int (k : ℤ) :: rvs := by
    have hthis : out = .int ((fun a => (a.natAbs.size : ℤ)) (m : ℤ)) :: rvs := by rw [hout, ha, hr]
    simpa only [Int.natAbs_natCast, hsize'] using hthis
  have hn' : n ≤ Ksz * isz (m : ℤ) := hn
  have hcost : Ksz * isz (m : ℤ) ≤ Ksz * (k + 2) := by
    have h2 : isz (m : ℤ) = k + 2 := by
      simp only [isz, hsize]
    rw [h2]
  refine ⟨s', n, hev, le_trans hn' hcost, ?_, hoth⟩
  rw [hstk, hout']

/-! ## 4. The target -/

theorem lengthWord (hI : HvdH.IntLib) : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = .int xs.length :: ofList xs :: rest)
    (fun _ => K * (vsz (ofList xs) + 1)) := by
  obtain ⟨prev, Krev, hrev0⟩ := reverseWord
  obtain ⟨pev, Ke, hev0⟩ := hI.evalPoly
  obtain ⟨psz, Ksz, hsz0⟩ := hI.size
  refine ⟨lenProg prev pev psz, 400 + Krev + 9 * Ke + 3 * Ksz, ?_⟩
  intro main xs vs hpre s R hs
  obtain ⟨rest, rfl⟩ := hpre
  have hs' : s.stk 0 = (ofList xs).enc ++ (encs rest ++ R) := by
    rw [hs, encs_cons_lw, List.append_assoc]
  -- (1) the accumulator (stack 1) starts as the empty list
  obtain ⟨s₁, n₁, he₁, hn₁, h1a, h1o⟩ :=
    pushConstsEv (main := main) (k := 1) [Glyph.nil] (g := s.reg) (X := s.stk)
  have hq₁ : s₁.stk 1 = (ofList ([] : List Val)).enc ++ s.stk 1 := by
    rw [h1a, reverse_singleton_lw, ofList_nil_enc_lw]
  -- (2) the counting list (stack 4) starts as the empty list
  obtain ⟨s₂, n₂, he₂, hn₂, h2a, h2o⟩ :=
    pushConstsEv (main := main) (k := 4) [Glyph.nil] (g := s₁.reg) (X := s₁.stk)
  have hq₂ : s₂.stk 4 = (ones 0).enc ++ s.stk 4 := by
    rw [h2a, h1o 4 (by decide), reverse_singleton_lw, ones_zero_enc_lw]
  have h2s1 : s₂.stk 1 = (ofList ([] : List Val)).enc ++ s.stk 1 := by
    rw [h2o 1 (by decide)]; exact hq₁
  have h2s0 : s₂.stk 0 = (ofList xs).enc ++ (encs rest ++ R) := by
    rw [h2o 0 (by decide), h1o 0 (by decide)]; exact hs'
  have hp₂ : ∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 4 → s₂.stk j = s.stk j :=
    fun j hj0 hj1 hj4 => by rw [h2o j hj4, h1o j hj1]
  -- (3) set the loop flag
  let s₃ : State := ⟨Function.update s₂.reg rF_lw Glyph.cons, s₂.stk⟩
  have he₃ : Ev main (.set rF_lw Glyph.cons) s₂ s₃ 1 :=
    ev_set' (main := main) rF_lw Glyph.cons s₂.reg s₂.stk
  have h3r : s₃.reg rF_lw = Glyph.cons := by
    show (Function.update s₂.reg rF_lw Glyph.cons) rF_lw = Glyph.cons
    simp
  -- (4) the counting/reversal loop
  obtain ⟨s₄, hrun₄, h4a, h4b, h4c, h4r, h4s2, h4s3, h4o⟩ :=
    lenWalk_loop (main := main) xs [] (encs rest ++ R) (s.stk 1) (s.stk 4)
      s₃.reg s₃.stk h3r h2s0 h2s1 hq₂
  have he₄ : Ev main (.loop rF_lw Glyph.cons lenWalkBody) s₃ s₄ (lenWalkCost xs + 1) :=
    loopRuns.eval hrun₄ (by rw [h4r]; decide)
  have h4c' : s₄.stk 4 = (ones xs.length).enc ++ s.stk 4 := by
    rw [h4c, List.length_nil, Nat.zero_add]
  have hp₄ : ∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 4 → s₄.stk j = s.stk j := by
    intro j hj0 hj1 hj4
    by_cases h2 : j = 2
    · rw [h2, h4s2]; exact hp₂ 2 (by decide) (by decide) (by decide)
    by_cases h3 : j = 3
    · rw [h3, h4s3]; exact hp₂ 3 (by decide) (by decide) (by decide)
    · rw [h4o j hj0 hj1 h2 h3 hj4]; exact hp₂ j hj0 hj1 hj4
  -- (5) drop the `nil` terminator of the exhausted source list
  let s₅ : State := ⟨Function.update s₄.reg rA ((s₄.stk 0).headD Glyph.eos),
      Function.update s₄.stk 0 (s₄.stk 0).tail⟩
  have he₅ : Ev main (.pop 0 rA) s₄ s₅ 1 :=
    ev_pop' (main := main) 0 rA s₄.reg s₄.stk
  have h5s : ∀ j : Stk, j ≠ 0 → s₅.stk j = s₄.stk j :=
    fun j hj => Function.update_of_ne hj _ _
  have h5s0 : s₅.stk 0 = encs rest ++ R := by
    show (Function.update s₄.stk 0 (s₄.stk 0).tail) 0 = encs rest ++ R
    rw [Function.update_self, h4a]; rfl
  have h5s1 : s₅.stk 1 = (ofList xs.reverse).enc ++ s.stk 1 := by
    rw [h5s 1 (by decide), h4b]; simp
  have hp₅ : ∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 4 → s₅.stk j = s.stk j :=
    fun j hj0 hj1 hj4 => by rw [h5s j hj0]; exact hp₄ j hj0 hj1 hj4
  -- (6) move the reversed accumulator onto stack 0
  obtain ⟨s₆, n₆, he₆, hn₆, h6a, h6b, h6c, h6d, h6o⟩ :=
    mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₅.reg) (X := s₅.stk) (v := ofList xs.reverse)
      (A := s.stk 1) (B := encs rest ++ R) h5s1 h5s0
  have h6s0 : s₆.stk 0 = encs (ofList xs.reverse :: rest) ++ R := by
    rw [h6b, encs_cons_lw, List.append_assoc]
  have h6s4 : s₆.stk 4 = (ones xs.length).enc ++ s.stk 4 := by
    rw [h6o 4 (by decide) (by decide) (by decide) (by decide), h5s 4 (by decide)]
    exact h4c'
  have hp₆ : ∀ j : Stk, j ≠ 0 → j ≠ 4 → s₆.stk j = s.stk j := by
    intro j hj0 hj4
    by_cases h1j : j = 1
    · rw [h1j]; exact h6a
    by_cases h2j : j = 2
    · rw [h2j, h6c]
      exact hp₅ 2 (by decide) (by decide) (by decide)
    by_cases h3j : j = 3
    · rw [h3j, h6d]
      exact hp₅ 3 (by decide) (by decide) (by decide)
    · rw [h6o j h1j hj0 h2j h3j]
      exact hp₅ j hj0 h1j hj4
  -- (7) the library reversal word puts the original order back
  obtain ⟨s₇, n₇, he₇, hn₇, h7a, h7o⟩ :=
    reverseEv_lw (main := main) (prev := prev) (Krev := Krev) (fun ys => hrev0 main ys)
      xs.reverse rest R (g := s₆.reg) (X := s₆.stk) h6s0
  have h7s0 : s₇.stk 0 = encs (ofList xs :: rest) ++ R := by
    rw [h7a, List.reverse_reverse]
  have h7s4 : s₇.stk 4 = (ones xs.length).enc ++ s.stk 4 := by
    rw [h7o 4 (by decide)]; exact h6s4
  have hp₇ : ∀ j : Stk, j ≠ 0 → j ≠ 4 → s₇.stk j = s.stk j :=
    fun j hj0 hj4 => by rw [h7o j hj0]; exact hp₆ j hj0 hj4
  -- (8) push `.int 1` on top of the counting list
  obtain ⟨s₈, n₈, he₈, hn₈, h8a, h8o⟩ :=
    pushConstsEv (main := main) (k := 4) ((Val.int 1).enc.reverse) (g := s₇.reg) (X := s₇.stk)
  have h8s0 : s₈.stk 0 = encs (ofList xs :: rest) ++ R := by
    rw [h8o 0 (by decide)]; exact h7s0
  have h8s4 : s₈.stk 4 = (Val.int 1).enc ++ ((ones xs.length).enc ++ s.stk 4) := by
    rw [h8a, List.reverse_reverse, h7s4]
  have hp₈ : ∀ j : Stk, j ≠ 0 → j ≠ 4 → s₈.stk j = s.stk j :=
    fun j hj0 hj4 => by rw [h8o j hj4]; exact hp₇ j hj0 hj4
  -- (9) move `.int 1` onto stack 0
  obtain ⟨s₉, n₉, he₉, hn₉, h9a, h9b, h9c, h9d, h9o⟩ :=
    mvVal_ev_full (main := main) (a := 4) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₈.reg) (X := s₈.stk) (v := Val.int 1)
      (A := (ones xs.length).enc ++ s.stk 4) (B := encs (ofList xs :: rest) ++ R) h8s4 h8s0
  have h9s0 : s₉.stk 0 = (Val.int 1).enc ++ (encs (ofList xs :: rest) ++ R) := h9b
  have h9s4 : s₉.stk 4 = (ones xs.length).enc ++ s.stk 4 := h9a
  have hp₉ : ∀ j : Stk, j ≠ 0 → j ≠ 4 → s₉.stk j = s.stk j := by
    intro j hj0 hj4
    by_cases h2j : j = 2
    · rw [h2j, h9c]; exact hp₈ 2 (by decide) (by decide)
    by_cases h3j : j = 3
    · rw [h3j, h9d]; exact hp₈ 3 (by decide) (by decide)
    · rw [h9o j hj4 hj0 h2j h3j]; exact hp₈ j hj0 hj4
  -- (10) move the counting list onto stack 0
  obtain ⟨s₁₀, n₁₀, he₁₀, hn₁₀, h10a, h10b, h10c, h10d, h10o⟩ :=
    mvVal_ev_full (main := main) (a := 4) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₉.reg) (X := s₉.stk) (v := ones xs.length)
      (A := s.stk 4) (B := (Val.int 1).enc ++ (encs (ofList xs :: rest) ++ R)) h9s4 h9s0
  have h10s0 : s₁₀.stk 0 =
      encs (intList (List.replicate xs.length 1) :: .int 1 :: ofList xs :: rest) ++ R := by
    rw [h10b, intList_replicate_lw]
    simp only [encs_cons_lw, List.append_assoc]
  have hp₁₀ : ∀ j : Stk, j ≠ 0 → s₁₀.stk j = s.stk j := by
    intro j hj0
    by_cases h4j : j = 4
    · rw [h4j]; exact h10a
    by_cases h2j : j = 2
    · rw [h2j, h10c]; exact hp₉ 2 (by decide) (by decide)
    by_cases h3j : j = 3
    · rw [h3j, h10d]; exact hp₉ 3 (by decide) (by decide)
    · rw [h10o j h4j hj0 h2j h3j]; exact hp₉ j hj0 h4j
  -- (11) `evalPoly` with `b = 1` evaluates the counting list to `2 ^ k - 1`
  obtain ⟨s₁₁, n₁₁, he₁₁, hn₁₁, h11a, h11o⟩ :=
    evalPolyEv_lw (main := main) (pev := pev) (Ke := Ke) (fun hs b hb hh => hev0 main hs b hb hh)
      xs.length (ofList xs :: rest) R (g := s₁₀.reg) (X := s₁₀.stk) h10s0
  -- (12) `size` extracts `k`
  obtain ⟨s₁₂, n₁₂, he₁₂, hn₁₂, h12a, h12o⟩ :=
    sizeEv_lw (main := main) (psz := psz) (Ksz := Ksz) (hsz0 main)
      xs.length (evalChunks (List.replicate xs.length 1) 1) (ofList xs :: rest) R
      (g := s₁₁.reg) (X := s₁₁.stk) (evalChunks_replicate_lw xs.length) h11a
  -- the whole run
  have he₇' : Ev main prev s₆ s₇ n₇ := ⟨n₇, he₇, le_rfl⟩
  have he₁₁' : Ev main pev s₁₀ s₁₁ n₁₁ := ⟨n₁₁, he₁₁, le_rfl⟩
  have he₁₂' : Ev main psz s₁₁ s₁₂ n₁₂ := ⟨n₁₂, he₁₂, le_rfl⟩
  have hall : Ev main (lenProg prev pev psz) ⟨s.reg, s.stk⟩ s₁₂
      (n₁ + (n₂ + (1 + ((lenWalkCost xs + 1) + (1 + (n₆ + (n₇ + (n₈ + (n₉ +
        (n₁₀ + (n₁₁ + n₁₂))))))))))) := by
    unfold lenProg
    simp only [seqs]
    exact Ev.seq he₁ (Ev.seq he₂ (Ev.seq he₃ (Ev.seq he₄ (Ev.seq he₅ (Ev.seq he₆
      (Ev.seq he₇' (Ev.seq he₈ (Ev.seq he₉ (Ev.seq he₁₀ (Ev.seq he₁₁' he₁₂'))))))))))
  obtain ⟨n, hev, hn⟩ := hall
  -- cost accounting
  have hV : 1 ≤ vsz (ofList xs) + 1 := by omega
  have hk : xs.length ≤ vsz (ofList xs) + 1 := by
    have := length_le_vsz_ofList_lw xs; omega
  have hwalk : lenWalkCost xs + 1 ≤ 34 * (vsz (ofList xs) + 1) := by
    rw [lenWalkCost_eq, sum_map_vsz_add_one_lw, vsz_ofList_lw]
    omega
  have h6 : n₆ ≤ 16 * (vsz (ofList xs) + 1) := by
    have h := hn₆; rwa [vsz_ofList_reverse_lw] at h
  have h7 : n₇ ≤ Krev * (vsz (ofList xs) + 1) := by
    have h := hn₇; rwa [vsz_ofList_reverse_lw] at h
  have h8 : n₈ ≤ 7 := by
    have h := hn₈
    rw [List.length_reverse, enc_int_one_lw] at h
    simp only [List.length_cons, List.length_nil] at h
    omega
  have h9 : n₉ ≤ 64 := by
    have h := hn₉
    have h3 : vsz (Val.int 1) = 3 := rfl
    rw [h3] at h
    omega
  have h10 : n₁₀ ≤ 96 * (vsz (ofList xs) + 1) := by
    have h := hn₁₀
    rw [vsz_ones_lw] at h
    have hk2 : 4 * xs.length + 2 ≤ 6 * (vsz (ofList xs) + 1) := by omega
    calc n₁₀ ≤ 16 * (4 * xs.length + 1 + 1) := h
      _ = 16 * (4 * xs.length + 2) := by ring
      _ ≤ 16 * (6 * (vsz (ofList xs) + 1)) := Nat.mul_le_mul_left 16 hk2
      _ = 96 * (vsz (ofList xs) + 1) := by ring
  have h11 : n₁₁ ≤ 9 * Ke * (vsz (ofList xs) + 1) := by
    have h := hn₁₁
    have hk4 : 5 * xs.length + 4 ≤ 9 * (vsz (ofList xs) + 1) := by omega
    calc n₁₁ ≤ Ke * (5 * xs.length + 4) := h
      _ ≤ Ke * (9 * (vsz (ofList xs) + 1)) := Nat.mul_le_mul_left Ke hk4
      _ = 9 * Ke * (vsz (ofList xs) + 1) := by ring
  have h12 : n₁₂ ≤ 3 * Ksz * (vsz (ofList xs) + 1) := by
    have h := hn₁₂
    have hk2 : xs.length + 2 ≤ 3 * (vsz (ofList xs) + 1) := by omega
    calc n₁₂ ≤ Ksz * (xs.length + 2) := h
      _ ≤ Ksz * (3 * (vsz (ofList xs) + 1)) := Nat.mul_le_mul_left Ksz hk2
      _ = 3 * Ksz * (vsz (ofList xs) + 1) := by ring
  have hsum_le : n₁ + (n₂ + (1 + (lenWalkCost xs + 1 + (1 + (n₆ + (n₇ + (n₈ + (n₉ +
      (n₁₀ + (n₁₁ + n₁₂)))))))))) ≤
      (fun _ => (400 + Krev + 9 * Ke + 3 * Ksz) * (vsz (ofList xs) + 1))
        (ofList xs :: rest) := by
    show n₁ + (n₂ + (1 + (lenWalkCost xs + 1 + (1 + (n₆ + (n₇ + (n₈ + (n₉ +
      (n₁₀ + (n₁₁ + n₁₂)))))))))) ≤ (400 + Krev + 9 * Ke + 3 * Ksz) * (vsz (ofList xs) + 1)
    have hn₁' : n₁ ≤ 3 := by
      have h := hn₁; simp only [List.length_cons, List.length_nil] at h; omega
    have hn₂' : n₂ ≤ 3 := by
      have h := hn₂; simp only [List.length_cons, List.length_nil] at h; omega
    set V : ℕ := vsz (ofList xs) + 1 with hVdef
    have hV1 : 1 ≤ V := by rw [hVdef]; exact hV
    have key : n₁ + (n₂ + (1 + (lenWalkCost xs + 1 + (1 + (n₆ + (n₇ + (n₈ + (n₉ +
        (n₁₀ + (n₁₁ + n₁₂)))))))))) ≤
        3 + (3 + (1 + (34 * V + (1 + (16 * V + (Krev * V + (7 + (64 + (96 * V +
          (9 * Ke * V + 3 * Ksz * V)))))))))) := by omega
    have hK : 3 + (3 + (1 + (34 * V + (1 + (16 * V + (Krev * V + (7 + (64 + (96 * V +
        (9 * Ke * V + 3 * Ksz * V)))))))))) ≤ (400 + Krev + 9 * Ke + 3 * Ksz) * V := by
      nlinarith [hV1]
    exact le_trans key hK
  refine ⟨.int (xs.length : ℤ) :: ofList xs :: rest, s₁₂, n, ⟨rest, rfl, rfl⟩, hev,
    le_trans hn hsum_le, ?_, ?_⟩
  · exact h12a
  · intro j hj
    rw [h12o j hj, h11o j hj]
    exact hp₁₀ j hj

end Work.Layout
