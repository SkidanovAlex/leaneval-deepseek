import Mathlib
import Submission.Work.ConvR.listProdBDefs
import Submission.Work.Kernel.Raw

/-!
# Working module for the proof of `Work.ConvR.listProdB`
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## State bookkeeping for the primitive commands -/

theorem tPeek_stk (s : State) (k : Stk) (r : Reg) : (State.tPeek s k r).stk = s.stk := rfl

theorem tPeek_reg_self (s : State) (k : Stk) (r : Reg) :
    (State.tPeek s k r).reg r = (s.stk k).headD Glyph.eos := by
  cases s with
  | mk reg stk => simp [State.tPeek, State.updReg]

theorem tPop_stk_self (s : State) (r : Reg) : (State.tPop s 0 r).stk 0 = (s.stk 0).tail := by
  cases s with
  | mk reg stk => simp [State.tPop, State.updStk, State.updReg]

theorem tPop_stk_ne (s : State) (r : Reg) {k : Stk} (hk : k ≠ 0) :
    (State.tPop s 0 r).stk k = s.stk k := by
  cases s with
  | mk reg stk => simp [State.tPop, State.updStk, State.updReg, hk]

theorem tSet_stk (s : State) (r : Reg) (g : Glyph) : (State.tSet s r g).stk = s.stk := rfl

theorem tSet_reg_self (s : State) (r : Reg) (g : Glyph) : (State.tSet s r g).reg r = g := by
  cases s with
  | mk reg stk => simp [State.tSet, State.updReg]

/-! ## The loop lemma with a sum of per-iteration costs -/

/-- `Cmd.loop` unrolled along an explicit sequence of states, charging each round its own cost. -/
theorem eval_loop_iterate_sum (main : Cmd) (r : Reg) (cc : Glyph) (body : Cmd) :
    ∀ (n : ℕ) (f : ℕ → State) (c : ℕ → ℕ),
      (∀ i < n, (f i).reg r = cc ∧ Eval main body (f i) (f (i + 1)) (c i)) →
      (f n).reg r ≠ cc →
      Eval main (.loop r cc body) (f 0) (f n) (((List.range n).map c).sum + n + 1) := by
  intro n
  induction n with
  | zero =>
    intro f c _ hstop
    simpa using Eval.loopF (main := main) (s := f 0) hstop
  | succ n ih =>
    intro f c hstep hstop
    have h0 := hstep 0 (Nat.zero_lt_succ n)
    have hrest : Eval main (.loop r cc body) (f 1) (f (n + 1))
        (((List.range n).map (fun i => c (i + 1))).sum + n + 1) :=
      ih (fun i => f (i + 1)) (fun i => c (i + 1))
        (fun i hi => hstep (i + 1) (by omega)) hstop
    have hT := Eval.loopT (main := main) h0.1 h0.2 hrest
    have hcost : (((List.range (n + 1)).map c).sum + (n + 1) + 1) =
        c 0 + (((List.range n).map (fun i => c (i + 1))).sum + n + 1) + 1 := by
      have hsum : ((List.range n).map (c ∘ Nat.succ)).sum =
          ((List.range n).map (fun i => c (i + 1))).sum := by
        have hf : (c ∘ Nat.succ) = fun i => c (i + 1) := by funext i; rfl
        rw [hf]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, hsum]
      omega
    rw [hcost]
    exact hT

/-! ## The two runs of one iteration -/

theorem body_nil (main : Cmd) {rp mp sp : Cmd} (s : State) (P : ℕ) (rest : List Val)
    (R : List Glyph) (stk : Stk → List Glyph)
    (hstk : s.stk 0 = encs (Val.nil :: Val.int (P : ℤ) :: rest) ++ R)
    (hoth : ∀ k : Stk, k ≠ 0 → s.stk k = stk k) :
    ∃ (s' : State) (n : ℕ), Eval main (bodyProg rp mp sp) s s' n ∧ n ≤ 5 ∧
      s'.stk 0 = encs (Val.int (P : ℤ) :: rest) ++ R ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = stk k) ∧ s'.reg rLoop = gStop := by
  set s1 : State := State.tPeek s 0 rHead with hs1
  set s2 : State := State.tPop s1 0 rPop with hs2
  have hhead : (s.stk 0).headD Glyph.eos = Glyph.nil := by rw [hstk, headD_stack_nil]
  have hreg1 : s1.reg rHead = Glyph.nil := by rw [hs1, tPeek_reg_self, hhead]
  have hstk2 : s2.stk 0 = encs (Val.int (P : ℤ) :: rest) ++ R := by
    rw [hs2, tPop_stk_self, hs1, tPeek_stk, hstk, tail_nil_stack]
  have hoth2 : ∀ k : Stk, k ≠ 0 → s2.stk k = stk k := by
    intro k hk
    rw [hs2, tPop_stk_ne _ _ hk, hs1, tPeek_stk]
    exact hoth k hk
  refine ⟨State.tSet s2 rLoop gStop, 4, ?_, by norm_num, ?_, ?_, ?_⟩
  · rw [show bodyProg rp mp sp = .seq (.peek 0 rHead)
        (.ite rHead Glyph.nil (.seq (.pop 0 rPop) (.set rLoop gStop))
          (.seq (.pop 0 rPop) (.seq rp (.seq mp (.seq sp (.set rLoop gCont)))))) from rfl]
    have hp : Eval main (.peek 0 rHead) s s1 1 := by rw [hs1]; exact Eval.peek 0 rHead s
    have hb : Eval main (.seq (.pop 0 rPop) (.set rLoop gStop)) s1 (State.tSet s2 rLoop gStop) 2 :=
      Eval.seq (by rw [hs2]; exact Eval.pop 0 rPop s1) (Eval.set rLoop gStop s2)
    have hi : Eval main (.ite rHead Glyph.nil (.seq (.pop 0 rPop) (.set rLoop gStop))
        (.seq (.pop 0 rPop) (.seq rp (.seq mp (.seq sp (.set rLoop gCont))))))
        s1 (State.tSet s2 rLoop gStop) 3 := Eval.iteT hreg1 hb
    have hs : Eval main (.seq (.peek 0 rHead) (.ite rHead Glyph.nil
        (.seq (.pop 0 rPop) (.set rLoop gStop))
        (.seq (.pop 0 rPop) (.seq rp (.seq mp (.seq sp (.set rLoop gCont)))))))
        s (State.tSet s2 rLoop gStop) 4 := Eval.seq hp hi
    exact hs
  · rw [tSet_stk, hstk2]
  · intro k hk
    rw [tSet_stk]
    exact hoth2 k hk
  · exact tSet_reg_self s2 rLoop gStop

theorem body_cons (main : Cmd) {rp mp sp : Cmd} {Kr Km Ks : ℕ}
    (hr : IsRoll2 main rp Kr) (hm : IsMul main mp Km) (hsw : IsSwap main sp Ks)
    (s : State) (t : ℕ) (rem : List ℕ) (P : ℕ) (rest : List Val) (R : List Glyph)
    (stk : Stk → List Glyph)
    (hstk : s.stk 0 = encs (ofList (intVals (t :: rem)) :: Val.int (P : ℤ) :: rest) ++ R)
    (hoth : ∀ k : Stk, k ≠ 0 → s.stk k = stk k) :
    ∃ (s' : State) (n : ℕ), Eval main (bodyProg rp mp sp) s s' n ∧ n ≤ stepCost Kr Km Ks t rem P ∧
      s'.stk 0 = encs (ofList (intVals rem) :: Val.int ((P * t : ℕ) : ℤ) :: rest) ++ R ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = stk k) ∧ s'.reg rLoop = gCont := by
  set s1 : State := State.tPeek s 0 rHead with hs1
  set s2 : State := State.tPop s1 0 rPop with hs2
  have hhead : (s.stk 0).headD Glyph.eos = Glyph.cons := by rw [hstk, headD_stack_cons]
  have hreg1 : s1.reg rHead = Glyph.cons := by rw [hs1, tPeek_reg_self, hhead]
  have hne1 : s1.reg rHead ≠ Glyph.nil := by rw [hreg1]; decide
  have hstk2 : s2.stk 0 =
      encs (Val.int (t : ℤ) :: ofList (intVals rem) :: Val.int (P : ℤ) :: rest) ++ R := by
    rw [hs2, tPop_stk_self, hs1, tPeek_stk, hstk, tail_cons_stack]
  have hoth2 : ∀ k : Stk, k ≠ 0 → s2.stk k = stk k := by
    intro k hk
    rw [hs2, tPop_stk_ne _ _ hk, hs1, tPeek_stk]
    exact hoth k hk
  -- roll 2
  obtain ⟨o1, s3, n1, ho1, he1, hn1, hs3, ho3⟩ :=
    hr (Val.int (t : ℤ) :: ofList (intVals rem) :: Val.int (P : ℤ) :: rest) (by simp) s2 R hstk2
  have hs3' : s3.stk 0 =
      encs (Val.int (P : ℤ) :: Val.int (t : ℤ) :: ofList (intVals rem) :: rest) ++ R := by
    rw [ho1] at hs3
    simp only [getD_two, eraseIdx_two] at hs3
    exact hs3
  have hn1' : n1 ≤ Kr * 3 * (isz (t : ℤ) + SZrem rem + isz (P : ℤ) + 1) := by
    simpa only [take_three_sum, vsz_int, SZrem] using hn1
  -- mul
  obtain ⟨o2, s4, n2, ho2, he2, hn2, hs4, ho4⟩ :=
    hm (Val.int (P : ℤ) :: Val.int (t : ℤ) :: ofList (intVals rem) :: rest)
      ⟨(P : ℤ), (t : ℤ), ofList (intVals rem) :: rest, rfl, trivial⟩ s3 R hs3'
  obtain ⟨a2, b2, r2, hvs2, hout2⟩ := ho2
  simp only [List.cons.injEq, Val.int.injEq, and_true, true_and] at hvs2
  obtain ⟨rfl, rfl, rfl⟩ := hvs2
  have hout2' : o2 = Val.int ((P * t : ℕ) : ℤ) :: ofList (intVals rem) :: rest := by
    rw [hout2]
    show Val.int ((P : ℤ) * (t : ℤ)) :: ofList (intVals rem) :: rest =
      Val.int (((P * t : ℕ) : ℤ)) :: ofList (intVals rem) :: rest
    rw [Int.natCast_mul]
  have hs4' : s4.stk 0 =
      encs (Val.int ((P * t : ℕ) : ℤ) :: ofList (intVals rem) :: rest) ++ R := by
    rw [hout2'] at hs4
    exact hs4
  have hn2' : n2 ≤ Km * isz (P : ℤ) * isz (t : ℤ) := by
    simpa only [binCost] using hn2
  -- swap
  obtain ⟨o3, s5, n3, ho3', he3, hn3, hs5, ho5⟩ :=
    hsw (Val.int ((P * t : ℕ) : ℤ) :: ofList (intVals rem) :: rest) (by simp) s4 R hs4'
  obtain ⟨a3, b3, r3, hvs3, hout3⟩ := ho3'
  simp only [List.cons.injEq, and_true, true_and] at hvs3
  obtain ⟨rfl, rfl, rfl⟩ := hvs3
  have hs5' : s5.stk 0 =
      encs (ofList (intVals rem) :: Val.int ((P * t : ℕ) : ℤ) :: rest) ++ R := by
    rw [hout3] at hs5
    exact hs5
  have hn3' : n3 ≤ Ks * (isz ((P * t : ℕ) : ℤ) + SZrem rem + 1) := by
    simpa only [List.getD_cons_zero, List.getD_cons_succ, vsz_int, SZrem] using hn3
  refine ⟨State.tSet s5 rLoop gCont, n1 + n2 + n3 + 4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show bodyProg rp mp sp = .seq (.peek 0 rHead)
        (.ite rHead Glyph.nil (.seq (.pop 0 rPop) (.set rLoop gStop))
          (.seq (.pop 0 rPop) (.seq rp (.seq mp (.seq sp (.set rLoop gCont)))))) from rfl]
    have hp : Eval main (.peek 0 rHead) s s1 1 := by rw [hs1]; exact Eval.peek 0 rHead s
    have hb : Eval main (.seq (.pop 0 rPop) (.seq rp (.seq mp (.seq sp (.set rLoop gCont)))))
        s1 (State.tSet s5 rLoop gCont) (1 + (n1 + (n2 + (n3 + 1)))) :=
      Eval.seq (by rw [hs2]; exact Eval.pop 0 rPop s1)
        (Eval.seq he1 (Eval.seq he2 (Eval.seq he3 (Eval.set rLoop gCont s5))))
    have hi : Eval main (.ite rHead Glyph.nil (.seq (.pop 0 rPop) (.set rLoop gStop))
        (.seq (.pop 0 rPop) (.seq rp (.seq mp (.seq sp (.set rLoop gCont))))))
        s1 (State.tSet s5 rLoop gCont) (1 + (n1 + (n2 + (n3 + 1))) + 1) := Eval.iteF hne1 hb
    have hs := Eval.seq hp hi
    convert hs using 1
    omega
  · rw [stepCost]
    omega
  · rw [tSet_stk, hs5']
  · intro k hk
    rw [tSet_stk]
    rw [ho5 k hk, ho4 k hk, ho3 k hk]
    exact hoth2 k hk
  · exact tSet_reg_self s5 rLoop gCont

/-! ## The walk over the list -/

/-- Running the loop from a state whose value stack is `ofList (intVals ts) :: int P :: rest`
ends with the value stack `int (P * ts.prod) :: rest`, at cost `≤ loopCost Kr Km Ks ts P`. -/
theorem loop_run (main : Cmd) {rp mp sp : Cmd} {Kr Km Ks : ℕ}
    (hr : IsRoll2 main rp Kr) (hm : IsMul main mp Km) (hsw : IsSwap main sp Ks) :
    ∀ (ts : List ℕ) (P : ℕ) (rest : List Val) (R : List Glyph) (stk : Stk → List Glyph)
      (s : State),
      s.stk 0 = encs (ofList (intVals ts) :: Val.int (P : ℤ) :: rest) ++ R →
      (∀ k : Stk, k ≠ 0 → s.stk k = stk k) → s.reg rLoop = gCont →
      ∃ (s' : State) (n : ℕ), Eval main (loopProg rp mp sp) s s' n ∧
        n ≤ loopCost Kr Km Ks ts P ∧
        s'.stk 0 = encs (Val.int ((P * ts.prod : ℕ) : ℤ) :: rest) ++ R ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = stk k) ∧ s'.reg rLoop ≠ gCont := by
  intro ts
  induction ts with
  | nil =>
    intro P rest R stk s hstk hoth hreg
    obtain ⟨s1, n1, he1, hn1, hs1, hf1, hr1⟩ :=
      body_nil main (rp := rp) (mp := mp) (sp := sp) s P rest R stk hstk hoth
    have hne : s1.reg rLoop ≠ gCont := by rw [hr1]; exact gStop_ne_gCont
    have he2 : Eval main (loopProg rp mp sp) s1 s1 1 := by
      rw [loopProg]; exact Eval.loopF hne
    have he : Eval main (loopProg rp mp sp) s s1 (n1 + 1 + 1) := by
      rw [loopProg]; exact Eval.loopT hreg he1 he2
    refine ⟨s1, n1 + 1 + 1, he, ?_, ?_, hf1, hne⟩
    · show n1 + 1 + 1 ≤ 7
      omega
    · rw [hs1, List.prod_nil, Nat.mul_one]
  | cons t rem ih =>
    intro P rest R stk s hstk hoth hreg
    obtain ⟨s1, n1, he1, hn1, hs1, hf1, hr1⟩ :=
      body_cons main hr hm hsw s t rem P rest R stk hstk hoth
    obtain ⟨s2, n2, he2, hn2, hs2, hf2, hr2⟩ := ih (P * t) rest R stk s1 hs1 hf1 hr1
    have he : Eval main (loopProg rp mp sp) s s2 (n1 + n2 + 1) := by
      rw [loopProg]; exact Eval.loopT hreg he1 he2
    refine ⟨s2, n1 + n2 + 1, he, ?_, ?_, hf2, hr2⟩
    · show n1 + n2 + 1 ≤ stepCost Kr Km Ks t rem P + loopCost Kr Km Ks rem (P * t) + 1
      omega
    · rw [hs2]
      have hprod : ((P * t) * rem.prod : ℕ) = P * (t :: rem).prod := by
        rw [List.prod_cons]; ring
      rw [hprod]

/-! ## Bounding `loopCost` -/

/-- One iteration with the accumulator size replaced by a bound `B`. -/
def stepCostB (Kr Km Ks B : ℕ) (t : ℕ) (rem : List ℕ) : ℕ :=
  4 + Kr * 3 * (isz (t : ℤ) + SZrem rem + B + 1) + Km * B * isz (t : ℤ)
    + Ks * (B + isz (t : ℤ) + SZrem rem + 1)

/-- Cost of the walk with the accumulator bound threaded through. -/
def costSum (Kr Km Ks : ℕ) : ℕ → List ℕ → ℕ
  | B, [] => 7
  | B, t :: rem => (stepCostB Kr Km Ks B t rem + 1) + costSum Kr Km Ks (B + isz (t : ℤ)) rem

/-- Sum of the element sizes of a list. -/
def Ssum (ts : List ℕ) : ℕ := (ts.map fun t => isz (t : ℤ)).sum

theorem Ssum_cons (t : ℕ) (rem : List ℕ) : Ssum (t :: rem) = isz (t : ℤ) + Ssum rem := rfl

theorem SZrem_eq_sum (ts : List ℕ) : SZrem ts = Ssum ts + ts.length + 1 := by
  rw [SZrem_eq]; rfl

theorem loopCost_le_costSum (Kr Km Ks : ℕ) :
    ∀ (ts : List ℕ) (P B : ℕ), isz (P : ℤ) ≤ B → loopCost Kr Km Ks ts P ≤ costSum Kr Km Ks B ts := by
  intro ts
  induction ts with
  | nil => intro P B _; exact le_refl 7
  | cons t rem ih =>
    intro P B hB
    have hmul : isz ((P * t : ℕ) : ℤ) ≤ B + isz (t : ℤ) := by
      have h := isz_mul_le (P : ℤ) (t : ℤ)
      rw [← Int.natCast_mul] at h
      omega
    have hstep : stepCost Kr Km Ks t rem P ≤ stepCostB Kr Km Ks B t rem := by
      simp only [stepCost, stepCostB]
      gcongr <;> omega
    have hih := ih (P * t) (B + isz (t : ℤ)) hmul
    calc loopCost Kr Km Ks (t :: rem) P
        = stepCost Kr Km Ks t rem P + loopCost Kr Km Ks rem (P * t) + 1 := rfl
      _ ≤ stepCostB Kr Km Ks B t rem + costSum Kr Km Ks (B + isz (t : ℤ)) rem + 1 := by omega
      _ = (stepCostB Kr Km Ks B t rem + 1) + costSum Kr Km Ks (B + isz (t : ℤ)) rem := by omega
      _ = costSum Kr Km Ks B (t :: rem) := rfl

theorem core_sq (B S k : ℕ) : B * S + S ^ 2 ≤ (B + S + k) ^ 2 := by
  have h1 : B * S + S ^ 2 = (B + S) * S := by ring
  rw [h1, pow_two]
  have ha : S ≤ B + S := by omega
  have hb : B + S ≤ B + S + k := by omega
  exact le_trans (Nat.mul_le_mul_left (B + S) ha) (Nat.mul_le_mul hb (by omega))

theorem core_const (B S m : ℕ) : 5 * m + 7 ≤ 12 * (B + S + m + 1) ^ 2 := by
  set X : ℕ := B + S + m + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hm : m ≤ X := by omega
  have hsq : X ≤ X ^ 2 := by
    calc X = X * 1 := by ring
      _ ≤ X * X := Nat.mul_le_mul_left X hX1
      _ = X ^ 2 := by ring
  have h12 : 12 * X ≤ 12 * X ^ 2 := Nat.mul_le_mul_left 12 hsq
  have h57 : 5 * X + 7 ≤ 12 * X := by omega
  omega

theorem costSum_le_bound (Kr Km Ks : ℕ) (ts : List ℕ) :
    ∀ (B : ℕ), costSum Kr Km Ks B ts ≤
      Km * (B * Ssum ts + (Ssum ts) ^ 2) +
        (3 * Kr + Ks) * (ts.length * (B + Ssum ts + ts.length) + Ssum ts + ts.length) +
        5 * ts.length + 7 := by
  induction ts with
  | nil => intro B; simp [costSum, Ssum]
  | cons t rem ih =>
    intro B
    have hih := ih (B + isz (t : ℤ))
    rw [Ssum_cons t rem, show (t :: rem).length = rem.length + 1 from rfl]
    rw [show costSum Kr Km Ks B (t :: rem) =
        (stepCostB Kr Km Ks B t rem + 1) + costSum Kr Km Ks (B + isz (t : ℤ)) rem from rfl]
    have hstep : stepCostB Kr Km Ks B t rem + 1 =
        5 + Km * B * isz (t : ℤ) +
          (3 * Kr + Ks) * (B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1) + 1) := by
      simp only [stepCostB]
      rw [SZrem_eq_sum]
      ring
    rw [hstep]
    have hKm : Km * B * isz (t : ℤ) + Km * ((B + isz (t : ℤ)) * Ssum rem + (Ssum rem) ^ 2) ≤
        Km * (B * (isz (t : ℤ) + Ssum rem) + (isz (t : ℤ) + Ssum rem) ^ 2) := by
      have h : B * isz (t : ℤ) + (B + isz (t : ℤ)) * Ssum rem + (Ssum rem) ^ 2 ≤
          B * (isz (t : ℤ) + Ssum rem) + (isz (t : ℤ) + Ssum rem) ^ 2 := by
        have h1 : B * isz (t : ℤ) + (B + isz (t : ℤ)) * Ssum rem + (Ssum rem) ^ 2 =
            B * (isz (t : ℤ) + Ssum rem) + Ssum rem * (isz (t : ℤ) + Ssum rem) := by ring
        rw [h1, pow_two]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      calc Km * B * isz (t : ℤ) + Km * ((B + isz (t : ℤ)) * Ssum rem + (Ssum rem) ^ 2)
          = Km * (B * isz (t : ℤ) + (B + isz (t : ℤ)) * Ssum rem + (Ssum rem) ^ 2) := by ring
        _ ≤ Km * (B * (isz (t : ℤ) + Ssum rem) + (isz (t : ℤ) + Ssum rem) ^ 2) :=
            Nat.mul_le_mul_left _ h
    have hLin : (3 * Kr + Ks) * (B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1) + 1) +
          (3 * Kr + Ks) * (rem.length * (B + isz (t : ℤ) + Ssum rem + rem.length) +
            Ssum rem + rem.length) ≤
        (3 * Kr + Ks) * ((rem.length + 1) * (B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1)) +
          (isz (t : ℤ) + Ssum rem) + (rem.length + 1)) := by
      have h : (B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1) + 1) +
            (rem.length * (B + isz (t : ℤ) + Ssum rem + rem.length) + Ssum rem + rem.length) ≤
          (rem.length + 1) * (B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1)) +
            (isz (t : ℤ) + Ssum rem) + (rem.length + 1) := by
        nlinarith
      calc (3 * Kr + Ks) * (B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1) + 1) +
            (3 * Kr + Ks) * (rem.length * (B + isz (t : ℤ) + Ssum rem + rem.length) +
              Ssum rem + rem.length)
          = (3 * Kr + Ks) * ((B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1) + 1) +
              (rem.length * (B + isz (t : ℤ) + Ssum rem + rem.length) + Ssum rem + rem.length)) := by ring
        _ ≤ (3 * Kr + Ks) * ((rem.length + 1) * (B + (isz (t : ℤ) + Ssum rem) + (rem.length + 1)) +
              (isz (t : ℤ) + Ssum rem) + (rem.length + 1)) := Nat.mul_le_mul_left _ h
    have hConst : 5 + (5 * rem.length + 7) ≤ 5 * (rem.length + 1) + 7 := by omega
    nlinarith [hih, hKm, hLin, hConst]

theorem bound_le_quadratic (Kr Km Ks : ℕ) (ts : List ℕ) (B : ℕ) :
    Km * (B * Ssum ts + (Ssum ts) ^ 2) +
        (3 * Kr + Ks) * (ts.length * (B + Ssum ts + ts.length) + Ssum ts + ts.length) +
        5 * ts.length + 7 ≤
      (12 * (Kr + Km + Ks + 1)) * (B + SZrem ts) ^ 2 := by
  rw [SZrem_eq_sum]
  have hX : B + (Ssum ts + ts.length + 1) = B + Ssum ts + ts.length + 1 := by omega
  rw [hX]
  have h1 : Km * (B * Ssum ts + (Ssum ts) ^ 2) ≤ Km * (B + Ssum ts + ts.length + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (core_sq B (Ssum ts) (ts.length + 1))
  have h2 : (3 * Kr + Ks) * (ts.length * (B + Ssum ts + ts.length) + Ssum ts + ts.length) ≤
      (3 * Kr + Ks) * (B + Ssum ts + ts.length + 1) ^ 2 := by
    have h : ts.length * (B + Ssum ts + ts.length) + Ssum ts + ts.length ≤
        (B + Ssum ts + ts.length + 1) ^ 2 := by nlinarith
    exact Nat.mul_le_mul_left _ h
  have h3 : 5 * ts.length + 7 ≤ 12 * (B + Ssum ts + ts.length + 1) ^ 2 :=
    core_const B (Ssum ts) ts.length
  have h4 : Km + (3 * Kr + Ks) + 12 ≤ 12 * (Kr + Km + Ks + 1) := by omega
  have hstep1 : Km * (B * Ssum ts + (Ssum ts) ^ 2) + (3 * Kr + Ks) * (ts.length * (B + Ssum ts + ts.length) + Ssum ts + ts.length) + 5 * ts.length + 7 ≤ Km * (B + Ssum ts + ts.length + 1) ^ 2 + (3 * Kr + Ks) * (B + Ssum ts + ts.length + 1) ^ 2 + 12 * (B + Ssum ts + ts.length + 1) ^ 2 := by
    omega
  have hstep2 : Km * (B + Ssum ts + ts.length + 1) ^ 2 + (3 * Kr + Ks) * (B + Ssum ts + ts.length + 1) ^ 2 + 12 * (B + Ssum ts + ts.length + 1) ^ 2 = (Km + (3 * Kr + Ks) + 12) * (B + Ssum ts + ts.length + 1) ^ 2 := by
    ring
  have hstep3 : (Km + (3 * Kr + Ks) + 12) * (B + Ssum ts + ts.length + 1) ^ 2 ≤ (12 * (Kr + Km + Ks + 1)) * (B + Ssum ts + ts.length + 1) ^ 2 :=
    Nat.mul_le_mul_right _ h4
  exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)

theorem costSum_le (Kr Km Ks : ℕ) (ts : List ℕ) (B : ℕ) :
    costSum Kr Km Ks B ts ≤ (12 * (Kr + Km + Ks + 1)) * (B + SZrem ts) ^ 2 :=
  le_trans (costSum_le_bound Kr Km Ks ts B) (bound_le_quadratic Kr Km Ks ts B)

theorem loopCost_le (Kr Km Ks : ℕ) (ts : List ℕ) :
    loopCost Kr Km Ks ts 1 ≤ 192 * (Kr + Km + Ks + 1) * ((vsz (intList ts)) + 1) ^ 2 := by
  have h1 : loopCost Kr Km Ks ts 1 ≤ costSum Kr Km Ks 3 ts :=
    loopCost_le_costSum Kr Km Ks ts 1 3 (by decide)
  have h2 : costSum Kr Km Ks 3 ts ≤ (12 * (Kr + Km + Ks + 1)) * (SZrem ts + 4) ^ 2 := by
    have h := costSum_le Kr Km Ks ts 3
    have hs : (3 + SZrem ts) ^ 2 ≤ (SZrem ts + 4) ^ 2 := by
      apply Nat.pow_le_pow_left; omega
    exact le_trans h (Nat.mul_le_mul_left _ hs)
  have h3 : (SZrem ts + 4) ^ 2 ≤ 16 * (SZrem ts + 1) ^ 2 := by
    have hs : SZrem ts + 4 ≤ 4 * (SZrem ts + 1) := by omega
    calc (SZrem ts + 4) ^ 2 ≤ (4 * (SZrem ts + 1)) ^ 2 := Nat.pow_le_pow_left hs 2
      _ = 16 * (SZrem ts + 1) ^ 2 := by ring
  have h4 : (12 * (Kr + Km + Ks + 1)) * (SZrem ts + 4) ^ 2 ≤ (12 * (Kr + Km + Ks + 1)) * (16 * (SZrem ts + 1) ^ 2) := Nat.mul_le_mul_left _ h3
  have h5 : (12 * (Kr + Km + Ks + 1)) * (16 * (SZrem ts + 1) ^ 2) = 192 * (Kr + Km + Ks + 1) * ((vsz (intList ts)) + 1) ^ 2 := by
    rw [show SZrem ts = vsz (intList ts) from rfl]; ring
  exact le_trans h1 (le_trans h2 (le_trans h4 (le_of_eq h5)))

/-! ## Final assembly -/

/-- Arithmetic of the final cost: the four pieces add up to `Kconst`. -/
theorem cost_final (Kp Ks C V SZ n1 n2 n3 : ℕ) (hSZ : SZ ≤ V)
    (h1 : n1 ≤ 4 * Kp) (h2 : n2 ≤ Ks * (SZ + 4)) (h3 : n3 ≤ 192 * C * (V + 1) ^ 2) :
    n1 + (n2 + (1 + n3)) ≤ (4 * Kp + 1 + 4 * Ks + 19200 * C) * (V + 1) ^ 2 := by
  have hV0 : 1 ≤ V + 1 := by omega
  have hV1 : 1 ≤ (V + 1) ^ 2 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ (V + 1) * (V + 1) := Nat.mul_le_mul hV0 hV0
      _ = (V + 1) ^ 2 := by ring
  have hV' : 4 * Kp ≤ 4 * Kp * (V + 1) ^ 2 := by
    calc 4 * Kp = 4 * Kp * 1 := by ring
      _ ≤ 4 * Kp * (V + 1) ^ 2 := Nat.mul_le_mul_left _ hV1
  have hVsq : (V + 1) ≤ (V + 1) ^ 2 := by
    calc (V + 1) = (V + 1) * 1 := by ring
      _ ≤ (V + 1) * (V + 1) := Nat.mul_le_mul_left _ hV0
      _ = (V + 1) ^ 2 := by ring
  have hKs : Ks * (SZ + 4) ≤ 4 * Ks * (V + 1) ^ 2 := by
    have h4 : SZ + 4 ≤ 4 * (V + 1) := by omega
    have h6 : 4 * (V + 1) ≤ 4 * (V + 1) ^ 2 := Nat.mul_le_mul_left 4 hVsq
    have h7 : Ks * (4 * (V + 1)) ≤ Ks * (4 * (V + 1) ^ 2) := Nat.mul_le_mul_left Ks h6
    calc Ks * (SZ + 4) ≤ Ks * (4 * (V + 1)) := Nat.mul_le_mul_left Ks h4
      _ ≤ Ks * (4 * (V + 1) ^ 2) := h7
      _ = 4 * Ks * (V + 1) ^ 2 := by ring
  have h3' : 192 * C * (V + 1) ^ 2 ≤ 19200 * C * (V + 1) ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right C (by norm_num))
  have hexp : (4 * Kp + 1 + 4 * Ks + 19200 * C) * (V + 1) ^ 2 =
      4 * Kp * (V + 1) ^ 2 + (V + 1) ^ 2 + 4 * Ks * (V + 1) ^ 2 + 19200 * C * (V + 1) ^ 2 := by ring
  rw [hexp]
  omega

theorem listProdB_aux (hK : KernelLib) (hI : IntLib) (hL : LayoutLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (ts : List ℕ) (rest : List Val),
      WordR main prog (fun vs => vs = intList ts :: rest)
        (fun _ out => out = Val.int ((ts.prod : ℕ) : ℤ) :: rest)
        (fun vs => K * ((vsz (vs.headD Val.nil)) + 1) ^ 2) := by
  obtain ⟨pushF, Kp, hpushF⟩ := hK.pushVal
  obtain ⟨swapP, Ks, hswapP⟩ := hK.swap
  obtain ⟨rollF, Kr, hrollF⟩ := hK.roll
  obtain ⟨mulP, Km, hmulP⟩ := hI.mulS
  refine ⟨fullProg (pushF (Val.int 1)) swapP (loopProg (rollF 2) mulP swapP),
    Kconst Kp Kr Km Ks, ?_⟩
  intro main ts rest vs hpre s R hR
  subst vs
  have hpush : IsPushOne main (pushF (Val.int 1)) Kp := hpushF main (Val.int 1)
  have hswap : IsSwap main swapP Ks := hswapP main
  have hroll : IsRoll2 main (rollF 2) Kr := hrollF main 2
  have hmul : IsMul main mulP Km := hmulP main
  obtain ⟨o1, s1, n1, ho1, he1, hn1, hs1, hf1⟩ := hpush (intList ts :: rest) trivial s R hR
  have hs1' : s1.stk 0 = encs (Val.int 1 :: intList ts :: rest) ++ R := by rw [ho1] at hs1; exact hs1
  obtain ⟨o2, s2, n2, ho2, he2, hn2, hs2, hf2⟩ :=
    hswap (Val.int 1 :: intList ts :: rest) (by simp) s1 R hs1'
  obtain ⟨a2, b2, r2, hvs2, hout2⟩ := ho2
  simp only [List.cons.injEq, and_true, true_and] at hvs2
  obtain ⟨rfl, rfl, rfl⟩ := hvs2
  have hs2' : s2.stk 0 = encs (ofList (intVals ts) :: Val.int (1 : ℤ) :: rest) ++ R := by
    rw [hout2] at hs2; exact hs2
  have hset : Eval main (.set rLoop gCont) s2 (State.tSet s2 rLoop gCont) 1 := Eval.set rLoop gCont s2
  have hreg3 : (State.tSet s2 rLoop gCont).reg rLoop = gCont := tSet_reg_self s2 rLoop gCont
  have hstk3 : (State.tSet s2 rLoop gCont).stk 0 =
      encs (ofList (intVals ts) :: Val.int (1 : ℤ) :: rest) ++ R := by
    rw [tSet_stk]; exact hs2'
  have hoth3 : ∀ k : Stk, k ≠ 0 → (State.tSet s2 rLoop gCont).stk k = s.stk k := by
    intro k hk
    rw [tSet_stk, hf2 k hk, hf1 k hk]
  obtain ⟨s3, n3, he3, hn3, hs3, hf3, hr3⟩ :=
    loop_run main hroll hmul hswap ts 1 rest R s.stk (State.tSet s2 rLoop gCont) hstk3 hoth3 hreg3
  have hn3' : n3 ≤ 192 * (Kr + Km + Ks + 1) * ((vsz (intList ts)) + 1) ^ 2 :=
    le_trans hn3 (loopCost_le Kr Km Ks ts)
  have hn1' : n1 ≤ 4 * Kp := by
    have h := hn1
    simp only [vsz_int, isz_one] at h
    rw [show Kp * 4 = 4 * Kp from by ring] at h
    exact h
  have hn2' : n2 ≤ Ks * (SZrem ts + 4) := by
    have h := hn2
    simp only [List.getD_cons_zero, List.getD_cons_succ, vsz_int, isz_one] at h
    rw [show (3 + vsz (intList ts) + 1 : ℕ) = SZrem ts + 4 from by
      rw [show SZrem ts = vsz (intList ts) from rfl]; omega] at h
    exact h
  refine ⟨Val.int ((ts.prod : ℕ) : ℤ) :: rest, s3, n1 + (n2 + (1 + n3)), rfl, ?_, ?_, ?_, ?_⟩
  · rw [show fullProg (pushF (Val.int 1)) swapP (loopProg (rollF 2) mulP swapP) =
        .seq (pushF (Val.int 1)) (.seq swapP (.seq (.set rLoop gCont) (loopProg (rollF 2) mulP swapP)))
        from rfl]
    exact Eval.seq he1 (Eval.seq he2 (Eval.seq hset he3))
  · have hfin := cost_final Kp Ks (Kr + Km + Ks + 1) (vsz (intList ts)) (SZrem ts) n1 n2 n3
      (by rw [show SZrem ts = vsz (intList ts) from rfl]) hn1' hn2' hn3'
    have hce : (fun vs => Kconst Kp Kr Km Ks * ((vsz (vs.headD Val.nil)) + 1) ^ 2)
          (intList ts :: rest) = Kconst Kp Kr Km Ks * ((vsz (intList ts)) + 1) ^ 2 := rfl
    rw [hce, Kconst]
    exact hfin
  · rw [hs3, show (1 * ts.prod : ℕ) = ts.prod from by omega]
  · exact hf3

end Work.ConvR
