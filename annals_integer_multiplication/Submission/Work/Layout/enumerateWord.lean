import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.enumDefs
import Submission.Work.Layout.reverseWord
import Submission.Work.Layout.incDup_ev
import Submission.Work.Layout.dropVal_ev
import Submission.Work.Layout.enumCost_bound
import Submission.Work.Layout.vsz_ofList_lab_le

/-!
# `LayoutLib.enumerate`

`enumerate` labels `xs[i]` by `cons (int i) xs[i]`.  The list is moved to stack 1 and the walk keeps a
binary counter `int i` on top of the value stack 0.  Per element the counter is copied (`incDup`),
the copy is incremented (`IntLib.add` with `int 1`) and the *old* value is used as the label; the
labelled element is consed onto an accumulator list on stack 5.  At the end the counter is deleted
(`dropVal`), the accumulator is moved to stack 0 and reversed (`LayoutLib.reverse`), which restores
the original order.

Cost: `Σ_{i<N} O(isz i + vsz xs[i]) = O(vsz (ofList xs) + N log N)`.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## Encoding and size facts -/

private theorem encodePosNum_bits (p : PosNum) : Computability.encodePosNum p = (p : ℕ).bits := by
  induction p with
  | one => simp [Computability.encodePosNum, Nat.one_bits]
  | bit0 q ih =>
      rw [Computability.encodePosNum, ih, PosNum.cast_bit0,
        show ((q : ℕ) + (q : ℕ)) = 2 * (q : ℕ) by ring,
        Nat.bit0_bits _ (Nat.ne_of_gt (PosNum.cast_pos q))]
  | bit1 q ih =>
      rw [Computability.encodePosNum, ih, PosNum.cast_bit1,
        show ((q : ℕ) + (q : ℕ) + 1) = 2 * (q : ℕ) + 1 by ring, Nat.bit1_bits]

private theorem encodeNum_bits (m : Num) : Computability.encodeNum m = (m : ℕ).bits := by
  induction m with
  | zero => simp [Computability.encodeNum, Nat.zero_bits]
  | pos p => simpa [Computability.encodeNum] using encodePosNum_bits p

private theorem encodeNat_bits (n : ℕ) : Computability.encodeNat n = n.bits := by
  show Computability.encodeNum (↑n : Num) = n.bits
  rw [encodeNum_bits]
  exact congrArg Nat.bits (Num.to_of_nat n)

private theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  rw [encodeNat_bits]; exact Nat.size_eq_bits_len n

/-- `vsz (int z) = isz z`. -/
private theorem vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  rw [vsz, isz, Val.enc]
  simp [List.length_append, List.length_map, encodeNat_length]

private theorem vsz_int_cons (z : ℤ) (x : Val) :
    vsz (Val.cons (.int z) x) = isz z + vsz x + 1 := by
  rw [vsz_enc_cons, vsz_int]

/-- the lab function at counter `0` is the labelling required by `LayoutLib.enumerate` -/
private theorem lab_zero_eq (xs : List Val) :
    lab 0 xs = (List.range xs.length).map fun i : ℕ => Val.cons (.int (i : ℤ)) (xs.getD i .nil) := by
  unfold lab
  simp only [Nat.zero_add]

private theorem lab_cons (i : ℕ) (x : Val) (xs : List Val) :
    lab i (x :: xs) = Val.cons (.int (i : ℤ)) x :: lab (i + 1) xs := by
  unfold lab
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  have h1 : (Val.int ((i + 0 : ℕ) : ℤ)).cons ((x :: xs).getD 0 Val.nil) =
      (Val.int (i : ℤ)).cons x := by simp
  have h2 : List.map ((fun j => (Val.int ((i + j : ℕ) : ℤ)).cons ((x :: xs).getD j Val.nil))
        ∘ Nat.succ) (List.range xs.length)
      = List.map (fun j => (Val.int ((i + 1 + j : ℕ) : ℤ)).cons (xs.getD j Val.nil))
          (List.range xs.length) := by
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, List.getD_cons_succ]
    rw [show i + (j + 1) = i + 1 + j by omega]
  rw [h1, h2]

/-! ## Arithmetic -/

/-- cost budget of one element step (before the loop test) -/
private def stepB (Kadd a b : ℕ) : ℕ :=
  (64 + Kadd) * (b + 4) + (16 * (a + 1) + (16 * (b + 1) + (16 * (b + a + 2) + 6)))

/-- the step budget, plus the `peek`/`ite` of the body, fits the per-iteration budget -/
private theorem stepB_le_iter {Kadd a b : ℕ} :
    stepB Kadd a b + 2 ≤ (100 + Kadd) * (a + b + 4) := by
  have e1 : stepB Kadd a b + 2 = 32 * a + (96 + Kadd) * b + (328 + 4 * Kadd) := by
    unfold stepB; ring
  have e2 : (100 + Kadd) * (a + b + 4)
      = (100 + Kadd) * a + (100 + Kadd) * b + (400 + 4 * Kadd) := by ring
  rw [e1, e2]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right a (by omega))
    (Nat.mul_le_mul_right b (by omega))) (by omega)

private theorem nsize_bound (N : ℕ) : N.size + 3 ≤ 3 * (N * (N.size + 1)) + 3 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have h1 : N.size ≤ N * (N.size + 1) := by
      calc N.size ≤ 1 * (N.size + 1) := by omega
        _ ≤ N * (N.size + 1) := Nat.mul_le_mul_right _ hN
    omega

private theorem sum8_le {a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : ℕ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4) (h5 : a5 ≤ b5) (h6 : a6 ≤ b6)
    (h7 : a7 ≤ b7) (h8 : a8 ≤ b8) :
    a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 ≤ b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 := by
  have e1 : a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8
      = a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + a8)))))) := by omega
  have e2 : b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8
      = b1 + (b2 + (b3 + (b4 + (b5 + (b6 + (b7 + b8)))))) := by omega
  rw [e1, e2]
  exact Nat.add_le_add h1 (Nat.add_le_add h2 (Nat.add_le_add h3 (Nat.add_le_add h4
    (Nat.add_le_add h5 (Nat.add_le_add h6 (Nat.add_le_add h7 h8))))))

/-- the eight individual cost bounds of one element step give `stepB` -/
private theorem step_cost_le {Kadd a b c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℕ}
    (h1 : c₁ ≤ 1) (h2 : c₂ ≤ 16 * (a + 1)) (h3 : c₃ ≤ (64 + Kadd) * (b + 4))
    (h4 : c₄ ≤ 16 * (b + 1)) (h5 : c₅ ≤ 2) (h6 : c₆ ≤ 16 * (b + a + 2)) (h7 : c₇ ≤ 2)
    (h8 : c₈ ≤ 1) :
    c₁ + (c₂ + (c₃ + (c₄ + (c₅ + (c₆ + (c₇ + c₈)))))) ≤ stepB Kadd a b := by
  have e1 : c₁ + (c₂ + (c₃ + (c₄ + (c₅ + (c₆ + (c₇ + c₈))))))
      = c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + c₈ := by omega
  rw [e1]
  have h := sum8_le h1 h2 h3 h4 h5 h6 h7 h8
  have e2 : 1 + 16 * (a + 1) + (64 + Kadd) * (b + 4) + 16 * (b + 1) + 2
      + 16 * (b + a + 2) + 2 + 1 = stepB Kadd a b := by
    unfold stepB; ring
  rw [e2] at h
  exact h

/-- the final cost arithmetic of `enumerateWord` -/
private theorem final_le (Kadd Krev V Z Ns : ℕ) (hNs : Ns + 3 ≤ 3 * Z + 3) :
    16 * (V + 1) + 4 + 2 + 1 + 4 * (101 + Kadd) * (V + Z + 10) + 16 * (Ns + 3)
        + 16 * (V + 4 * Z + 5) + Krev * (V + 4 * Z + 5)
      ≤ 100 * (Kadd + Krev + 100) * (V + Z + 1) := by
  set W := V + Z + 1 with hW
  have h1 : 16 * (V + 1) + 4 + 2 + 1 ≤ 37 * W := by omega
  have h2 : 4 * (101 + Kadd) * (V + Z + 10) ≤ (40 * (101 + Kadd)) * W := by
    rw [show 4 * (101 + Kadd) * (V + Z + 10) = (4 * (101 + Kadd)) * (V + Z + 10) by ring]
    rw [show (40 * (101 + Kadd)) * W = (4 * (101 + Kadd)) * (10 * W) by ring]
    exact Nat.mul_le_mul_left _ (by omega)
  have h3 : 16 * (Ns + 3) ≤ 48 * W := by
    have h : Ns + 3 ≤ 3 * W := by omega
    calc 16 * (Ns + 3) ≤ 16 * (3 * W) := Nat.mul_le_mul_left _ h
      _ = 48 * W := by ring
  have h4 : 16 * (V + 4 * Z + 5) ≤ 80 * W := by
    rw [show (80 : ℕ) * W = 16 * (5 * W) by ring]
    exact Nat.mul_le_mul_left 16 (by omega)
  have h5 : Krev * (V + 4 * Z + 5) ≤ (5 * Krev) * W := by
    rw [show (5 * Krev) * W = Krev * (5 * W) by ring]
    exact Nat.mul_le_mul_left Krev (by omega)
  have hsum : 16 * (V + 1) + 4 + 2 + 1 + 4 * (101 + Kadd) * (V + Z + 10) + 16 * (Ns + 3)
        + 16 * (V + 4 * Z + 5) + Krev * (V + 4 * Z + 5)
      ≤ 37 * W + ((40 * (101 + Kadd)) * W + (48 * W + (80 * W + (5 * Krev) * W))) := by
    have hassoc : 16 * (V + 1) + 4 + 2 + 1 + 4 * (101 + Kadd) * (V + Z + 10) + 16 * (Ns + 3)
          + 16 * (V + 4 * Z + 5) + Krev * (V + 4 * Z + 5)
        = (16 * (V + 1) + 4 + 2 + 1)
          + (4 * (101 + Kadd) * (V + Z + 10)
            + (16 * (Ns + 3) + (16 * (V + 4 * Z + 5) + Krev * (V + 4 * Z + 5)))) := by ring
    rw [hassoc]
    exact Nat.add_le_add h1 (Nat.add_le_add h2 (Nat.add_le_add h3 (Nat.add_le_add h4 h5)))
  have hfinal : 37 * W + ((40 * (101 + Kadd)) * W + (48 * W + (80 * W + (5 * Krev) * W)))
      ≤ 100 * (Kadd + Krev + 100) * W := by
    have hc : 37 + (40 * (101 + Kadd) + (48 + (80 + 5 * Krev))) ≤ 100 * (Kadd + Krev + 100) := by
      omega
    have := Nat.mul_le_mul_right W hc
    rwa [show (37 + (40 * (101 + Kadd) + (48 + (80 + 5 * Krev)))) * W
        = 37 * W + ((40 * (101 + Kadd)) * W + (48 * W + (80 * W + (5 * Krev) * W))) by ring] at this
  exact le_trans hsum hfinal

/-! ## State-level wrappers for the movers -/

private theorem pop_state (main : Cmd) (s : State) :
    ∃ s' n, Ev main (.pop 1 rA) s s' n ∧ n ≤ 1 ∧ s'.stk 1 = (s.stk 1).tail ∧
      (∀ k : Stk, k ≠ 1 → s'.stk k = s.stk k) := by
  refine ⟨⟨Function.update s.reg rA ((s.stk 1).headD Glyph.eos), Function.update s.stk 1 (s.stk 1).tail⟩,
    1, ?_, le_rfl, ?_, ?_⟩
  · simpa using ev_pop' (main := main) 1 rA s.reg s.stk
  · simp
  · intro k hk; simp [Function.update_of_ne hk]

private theorem peek_state (main : Cmd) (s : State) :
    ∃ s' n, Ev main (.peek 1 rA) s s' n ∧ n ≤ 1 ∧ s'.stk = s.stk ∧
      s'.reg rA = (s.stk 1).headD Glyph.eos := by
  refine ⟨⟨Function.update s.reg rA ((s.stk 1).headD Glyph.eos), s.stk⟩, 1, ?_, le_rfl, rfl, ?_⟩
  · simpa using ev_peek' (main := main) 1 rA s.reg s.stk
  · simp

private theorem set_state (main : Cmd) (r : Reg) (c : Glyph) (s : State) :
    ∃ s' n, Ev main (.set r c) s s' n ∧ n ≤ 1 ∧ s'.stk = s.stk ∧ s'.reg r = c := by
  refine ⟨⟨Function.update s.reg r c, s.stk⟩, 1, ?_, le_rfl, rfl, ?_⟩
  · simpa using ev_set' (main := main) r c s.reg s.stk
  · simp

private theorem mvVal_state {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {s : State} {v : Val} {A B : List Glyph}
    (ha : s.stk a = v.enc ++ A) (hb : s.stk b = B) :
    ∃ s' n, Ev main (mvVal a b c d) s s' n ∧ n ≤ 16 * (vsz v + 1) ∧ s'.stk a = A ∧
      s'.stk b = v.enc ++ B ∧ s'.stk c = s.stk c ∧ s'.stk d = s.stk d ∧
      (∀ k : Stk, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = s.stk k) :=
  mvVal_ev_full hab hac had hbc hbd hcd (g := s.reg) (X := s.stk) ha hb

private theorem pushGlyph_state (main : Cmd) (k : Stk) (cst : Glyph) (s : State) :
    ∃ s' n, Ev main (pushConst k cst) s s' n ∧ n ≤ 2 ∧ s'.stk k = cst :: s.stk k ∧
      (∀ k' : Stk, k' ≠ k → s'.stk k' = s.stk k') := by
  obtain ⟨s', n, h, hn, hk, hf, -, -⟩ :=
    pushConst_ev (main := main) (k := k) (cst := cst) (g := s.reg) (X := s.stk)
  exact ⟨s', n, h, hn, hk, hf⟩

private theorem pushIntZero_state (main : Cmd) (s : State) :
    ∃ s' n, Ev main pushIntZero s s' n ∧ n ≤ 4 ∧ s'.stk 0 = (Val.int 0).enc ++ s.stk 0 ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k) := by
  obtain ⟨s', n, h, hn, h0, hf⟩ := pushIntZero_ev main s.reg s.stk
  exact ⟨s', n, h, hn, h0, hf⟩

private theorem incDup_state {main addP : Cmd} {Kadd : ℕ}
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (· + ·)
      (fun a b => Kadd * (isz a + isz b)))
    {s : State} {i : ℕ} {rest : List Val} {R L : List Glyph}
    (h0 : s.stk 0 = encs (.int (i : ℤ) :: rest) ++ R) (h4 : s.stk 4 = L) :
    ∃ s' n, Ev main (incDup addP) s s' n ∧ n ≤ (64 + Kadd) * (isz (i : ℤ) + 4) ∧
      s'.stk 0 = encs (.int ((i + 1 : ℕ) : ℤ) :: rest) ++ R ∧
      s'.stk 4 = (Val.int (i : ℤ)).enc ++ L ∧ s'.stk 6 = s.stk 6 ∧ s'.stk 7 = s.stk 7 ∧
      s'.stk 9 = s.stk 9 ∧ s'.stk 10 = s.stk 10 ∧ s'.stk 11 = s.stk 11 ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 4 → k ≠ 6 → k ≠ 7 → k ≠ 9 → k ≠ 10 → k ≠ 11 →
        s'.stk k = s.stk k) :=
  incDup_ev hadd main s.reg s.stk i rest R L h0 h4

private theorem dropVal_state {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    {s : State} {v : Val} {A : List Glyph} (ha : s.stk a = v.enc ++ A) :
    ∃ s' n, Ev main (dropVal a c d) s s' n ∧ n ≤ 16 * (vsz v + 1) ∧ s'.stk a = A ∧
      s'.stk c = s.stk c ∧ s'.stk d = s.stk d ∧
      (∀ k : Stk, k ≠ a → k ≠ c → k ≠ d → s'.stk k = s.stk k) :=
  dropVal_ev hac had hcd (g := s.reg) (X := s.stk) ha

/-! ## The `nil` case of the body -/

set_option maxHeartbeats 1600000 in
/-- the `nil` case of the loop body: drop the trailing `nil` glyph and stop the loop -/
private theorem enumNil_ev (main addP : Cmd) {s : State} {S₁ : List Glyph}
    (h1 : s.stk 1 = (ofList ([] : List Val)).enc ++ S₁) :
    ∃ s' n, Ev main (enumBody addP) s s' n ∧ n ≤ 6 ∧ s'.stk 1 = S₁ ∧
      s'.reg rEn = Glyph.eos ∧ (∀ k : Stk, k ≠ 1 → s'.stk k = s.stk k) := by
  have hhead : (s.stk 1).headD Glyph.eos = Glyph.nil := by rw [h1]; rfl
  obtain ⟨p₁, c₁, hE₁, hc₁, hp₁κ, hp₁r⟩ := peek_state main s
  have hrA : p₁.reg rA = Glyph.nil := by rw [hp₁r]; exact hhead
  obtain ⟨p₂, c₂, hE₂, hc₂, hp₂, hf₂⟩ := pop_state main p₁
  obtain ⟨p₃, c₃, hE₃, hc₃, hp₃, hp₃r⟩ := set_state main rEn Glyph.eos p₂
  have hbr : Ev main (.seq (.pop 1 rA) (.set rEn Glyph.eos)) p₁ p₃ (c₂ + c₃) := Ev.seq hE₂ hE₃
  have hite : Ev main (.ite rA Glyph.nil (.seq (.pop 1 rA) (.set rEn Glyph.eos)) (enumStep addP))
      p₁ p₃ (c₂ + c₃ + 1) := Ev.iteT hrA hbr
  have hbody : Ev main (enumBody addP) s p₃ (c₁ + (c₂ + c₃ + 1)) := by
    unfold enumBody
    exact Ev.seq hE₁ hite
  have h1' : p₂.stk 1 = S₁ := by rw [hp₂, hp₁κ, h1]; rfl
  have h3' : p₃.stk 1 = S₁ := by rw [hp₃]; exact h1'
  exact ⟨p₃, _, hbody, by omega, h3', hp₃r, fun k hk => by rw [hp₃, hf₂ k hk, hp₁κ]⟩

/-! ## One element step of the body -/

/-- the encoding of a labelled element consed onto the accumulator -/
private theorem cons_lab_enc (z : ℤ) (x : Val) (acc : List Val) :
    (ofList (Val.cons (.int z) x :: acc)).enc
      = Glyph.cons :: ((Val.cons (.int z) x).enc ++ (ofList acc).enc) := rfl

set_option maxHeartbeats 3200000 in
/-- one element step of the loop: the counter is incremented, `xs[0]` is labelled with the *old*
counter and consed onto the accumulator -/
private theorem enumStep_ev {main addP : Cmd} {Kadd : ℕ}
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (· + ·)
      (fun a b => Kadd * (isz a + isz b)))
    {s : State} {i : ℕ} {x : Val} {xs acc rest : List Val} {R S₁ S₅ : List Glyph}
    (h0 : s.stk 0 = encs (.int (i : ℤ) :: rest) ++ R)
    (h1 : s.stk 1 = (Val.cons x (ofList xs)).enc ++ S₁)
    (h5 : s.stk 5 = (ofList acc).enc ++ S₅) :
    ∃ s' n, Ev main (enumStep addP) s s' n ∧
      n ≤ stepB Kadd (vsz x) (isz (i : ℤ)) ∧
      s'.stk 0 = encs (.int ((i + 1 : ℕ) : ℤ) :: rest) ++ R ∧
      s'.stk 1 = (ofList xs).enc ++ S₁ ∧
      s'.stk 5 = (ofList (Val.cons (.int (i : ℤ)) x :: acc)).enc ++ S₅ ∧
      s'.reg rEn = Glyph.cons ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k) := by
  have htail : (s.stk 1).tail = x.enc ++ ((ofList xs).enc ++ S₁) := by
    rw [h1]
    simp only [Val.enc, List.cons_append, List.tail_cons, List.append_assoc]
  obtain ⟨s₁, c₁, hE₁, hc₁, h₁1, hf₁⟩ := pop_state main s
  obtain ⟨s₂, c₂, hE₂, hc₂, h₂1, h₂3, h₂6, h₂7, hf₂⟩ :=
    mvVal_state (main := main) (a := 1) (b := 3) (c := 6) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (s := s₁) (v := x) (A := (ofList xs).enc ++ S₁) (B := s₁.stk 3)
      (by rw [h₁1, htail]) rfl
  obtain ⟨s₃, c₃, hE₃, hc₃, h₃0, h₃4, h₃6, h₃7, h₃9, h₃10, h₃11, hf₃⟩ :=
    incDup_state (main := main) hadd (s := s₂) (i := i) (rest := rest) (R := R) (L := s₂.stk 4)
      (by rw [hf₂ 0 (by decide) (by decide) (by decide) (by decide), hf₁ 0 (by decide)]; exact h0) rfl
  obtain ⟨s₄, c₄, hE₄, hc₄, h₄4, h₄3, h₄6, h₄7, hf₄⟩ :=
    mvVal_state (main := main) (a := 4) (b := 3) (c := 6) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (s := s₃) (v := .int (i : ℤ)) (A := s₂.stk 4) (B := s₃.stk 3) (by rw [h₃4]) rfl
  obtain ⟨s₅, c₅, hE₅, hc₅, h₅3, hf₅⟩ := pushGlyph_state main 3 Glyph.cons s₄
  have h₅3' : s₅.stk 3 = (Val.cons (.int (i : ℤ)) x).enc ++ s.stk 3 := by
    rw [h₅3, h₄3, hf₃ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h₂3, hf₁ 3 (by decide)]
    simp only [Val.enc, List.cons_append, List.append_assoc]
  obtain ⟨s₆, c₆, hE₆, hc₆, h₆3, h₆5, h₆6, h₆7, hf₆⟩ :=
    mvVal_state (main := main) (a := 3) (b := 5) (c := 6) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (s := s₅) (v := Val.cons (.int (i : ℤ)) x) (A := s.stk 3) (B := s₅.stk 5) h₅3' rfl
  obtain ⟨s₇, c₇, hE₇, hc₇, h₇5, hf₇⟩ := pushGlyph_state main 5 Glyph.cons s₆
  obtain ⟨s₈, c₈, hE₈, hc₈, h₈κ, h₈r⟩ := set_state main rEn Glyph.cons s₇
  have hEv : Ev main (enumStep addP) s s₈
      (c₁ + (c₂ + (c₃ + (c₄ + (c₅ + (c₆ + (c₇ + c₈))))))) := by
    unfold enumStep
    exact Ev.seq hE₁ (Ev.seq hE₂ (Ev.seq hE₃ (Ev.seq hE₄ (Ev.seq hE₅ (Ev.seq hE₆ (Ev.seq hE₇ hE₈))))))
  -- stack facts
  have h5₅ : s₅.stk 5 = s.stk 5 := by
    rw [hf₅ 5 (by decide), hf₄ 5 (by decide) (by decide) (by decide) (by decide),
      hf₃ 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hf₂ 5 (by decide) (by decide) (by decide) (by decide), hf₁ 5 (by decide)]
  have hs1 : s₈.stk 1 = (ofList xs).enc ++ S₁ := by
    rw [h₈κ, hf₇ 1 (by decide), hf₆ 1 (by decide) (by decide) (by decide) (by decide),
      hf₅ 1 (by decide), hf₄ 1 (by decide) (by decide) (by decide) (by decide),
      hf₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h₂1
  have hs0 : s₈.stk 0 = encs (.int ((i + 1 : ℕ) : ℤ) :: rest) ++ R := by
    rw [h₈κ, hf₇ 0 (by decide), hf₆ 0 (by decide) (by decide) (by decide) (by decide),
      hf₅ 0 (by decide), hf₄ 0 (by decide) (by decide) (by decide) (by decide)]
    exact h₃0
  have hs5 : s₈.stk 5 = (ofList (Val.cons (.int (i : ℤ)) x :: acc)).enc ++ S₅ := by
    rw [h₈κ, h₇5, h₆5, h5₅, h5, cons_lab_enc]
    simp only [List.cons_append, List.append_assoc]
  -- cost
  have hc4 : c₄ ≤ 16 * (isz (i : ℤ) + 1) := by
    have h := hc₄
    rw [vsz_int] at h
    omega
  have hc6 : c₆ ≤ 16 * (isz (i : ℤ) + vsz x + 2) := by
    have h := hc₆
    rw [vsz_int_cons] at h
    omega
  have hcost : c₁ + (c₂ + (c₃ + (c₄ + (c₅ + (c₆ + (c₇ + c₈))))))
      ≤ stepB Kadd (vsz x) (isz (i : ℤ)) :=
    step_cost_le hc₁ hc₂ hc₃ hc4 hc₅ hc6 hc₇ hc₈
  -- frame
  have hframe : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 5 → s₈.stk k = s.stk k := by
    intro k hk0 hk1 hk5
    have eA : s₈.stk k = s₇.stk k := by rw [h₈κ]
    have eB : s₇.stk k = s₆.stk k := hf₇ k hk5
    by_cases hk3 : k = 3
    · subst hk3
      rw [eA, eB, h₆3]
    by_cases hk4 : k = 4
    · subst hk4
      rw [eA, eB, hf₆ 4 (by decide) (by decide) (by decide) (by decide), hf₅ 4 (by decide), h₄4,
        hf₂ 4 (by decide) (by decide) (by decide) (by decide), hf₁ 4 (by decide)]
    by_cases hk6 : k = 6
    · subst hk6
      rw [eA, eB, h₆6, hf₅ 6 (by decide), h₄6, h₃6, h₂6, hf₁ 6 (by decide)]
    by_cases hk7 : k = 7
    · subst hk7
      rw [eA, eB, h₆7, hf₅ 7 (by decide), h₄7, h₃7, h₂7, hf₁ 7 (by decide)]
    by_cases hk9 : k = 9
    · subst hk9
      rw [eA, eB, hf₆ 9 (by decide) (by decide) (by decide) (by decide), hf₅ 9 (by decide),
        hf₄ 9 (by decide) (by decide) (by decide) (by decide), h₃9,
        hf₂ 9 (by decide) (by decide) (by decide) (by decide), hf₁ 9 (by decide)]
    by_cases hk10 : k = 10
    · subst hk10
      rw [eA, eB, hf₆ 10 (by decide) (by decide) (by decide) (by decide), hf₅ 10 (by decide),
        hf₄ 10 (by decide) (by decide) (by decide) (by decide), h₃10,
        hf₂ 10 (by decide) (by decide) (by decide) (by decide), hf₁ 10 (by decide)]
    by_cases hk11 : k = 11
    · subst hk11
      rw [eA, eB, hf₆ 11 (by decide) (by decide) (by decide) (by decide), hf₅ 11 (by decide),
        hf₄ 11 (by decide) (by decide) (by decide) (by decide), h₃11,
        hf₂ 11 (by decide) (by decide) (by decide) (by decide), hf₁ 11 (by decide)]
    rw [eA, eB, hf₆ k hk3 hk5 hk6 hk7, hf₅ k hk3, hf₄ k hk4 hk3 hk6 hk7,
      hf₃ k hk0 hk4 hk6 hk7 hk9 hk10 hk11, hf₂ k hk1 hk3 hk6 hk7, hf₁ k hk1]
  exact ⟨s₈, _, hEv, hcost, hs0, hs1, hs5, h₈r, hframe⟩

/-! ## The `cons` case of the body -/

set_option maxHeartbeats 1600000 in
/-- `enumBody addP` in the `cons` case: `peek`, the `ite` test, and then one element step -/
private theorem enumCons_ev {main addP : Cmd} {Kadd : ℕ}
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (· + ·)
      (fun a b => Kadd * (isz a + isz b)))
    {s : State} {i : ℕ} {x : Val} {xs acc rest : List Val} {R S₁ S₅ : List Glyph}
    (h0 : s.stk 0 = encs (.int (i : ℤ) :: rest) ++ R)
    (h1 : s.stk 1 = (Val.cons x (ofList xs)).enc ++ S₁)
    (h5 : s.stk 5 = (ofList acc).enc ++ S₅) :
    ∃ s' n, Ev main (enumBody addP) s s' n ∧
      n ≤ (100 + Kadd) * (vsz x + isz (i : ℤ) + 4) ∧
      s'.stk 0 = encs (.int ((i + 1 : ℕ) : ℤ) :: rest) ++ R ∧
      s'.stk 1 = (ofList xs).enc ++ S₁ ∧
      s'.stk 5 = (ofList (Val.cons (.int (i : ℤ)) x :: acc)).enc ++ S₅ ∧
      s'.reg rEn = Glyph.cons ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k) := by
  obtain ⟨p₁, c₁, hE₁, hc₁, hp₁κ, hp₁r⟩ := peek_state main s
  have hhead0 : (s.stk 1).headD Glyph.eos = Glyph.cons := by rw [h1]; rfl
  have hhead : (p₁.stk 1).headD Glyph.eos = Glyph.cons := by rw [hp₁κ]; exact hhead0
  have hrA : p₁.reg rA = Glyph.cons := by rw [hp₁r]; exact hhead0
  obtain ⟨p₂, c₂, hE₂, hc₂, hp₂_0, hp₂_1, hp₂_5, hp₂r, hp₂f⟩ :=
    enumStep_ev (main := main) (addP := addP) hadd (s := p₁) (i := i) (x := x) (xs := xs)
      (acc := acc) (rest := rest) (R := R) (S₁ := S₁) (S₅ := S₅)
      (by rw [hp₁κ]; exact h0) (by rw [hp₁κ]; exact h1) (by rw [hp₁κ]; exact h5)
  have hite : Ev main (.ite rA Glyph.nil (.seq (.pop 1 rA) (.set rEn Glyph.eos)) (enumStep addP))
      p₁ p₂ (c₂ + 1) := Ev.iteF (by rw [hrA]; decide) hE₂
  have hbody : Ev main (enumBody addP) s p₂ (c₁ + (c₂ + 1)) := by
    unfold enumBody
    exact Ev.seq hE₁ hite
  have hcost : c₁ + (c₂ + 1) ≤ (100 + Kadd) * (vsz x + isz (i : ℤ) + 4) := by
    have h := stepB_le_iter (Kadd := Kadd) (a := vsz x) (b := isz (i : ℤ))
    omega
  refine ⟨p₂, _, hbody, hcost, hp₂_0, hp₂_1, hp₂_5, hp₂r, ?_⟩
  intro k hk0 hk1 hk5
  rw [hp₂f k hk0 hk1 hk5, hp₁κ]

/-! ## The loop -/

set_option maxHeartbeats 1600000 in
private theorem enumLoopRuns {main addP : Cmd} {Kadd : ℕ}
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (· + ·)
      (fun a b => Kadd * (isz a + isz b))) :
    ∀ (xs : List Val) (i : ℕ) (acc rest : List Val) (R S₁ S₅ : List Glyph) (s : State),
      s.stk 0 = encs (.int (i : ℤ) :: rest) ++ R →
      s.stk 1 = (ofList xs).enc ++ S₁ →
      s.stk 5 = (ofList acc).enc ++ S₅ →
      s.reg rEn = Glyph.cons →
      ∃ s', loopRuns main rEn Glyph.cons (enumBody addP) (xs.length + 1) s s'
          (enumCost (100 + Kadd) i xs) ∧
        s'.stk 0 = encs (.int ((i + xs.length : ℕ) : ℤ) :: rest) ++ R ∧
        s'.stk 1 = S₁ ∧
        s'.stk 5 = (ofList ((lab i xs).reverse ++ acc)).enc ++ S₅ ∧
        s'.reg rEn = Glyph.eos ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k) := by
  intro xs
  induction xs with
  | nil =>
      intro i acc rest R S₁ S₅ s h0 h1 h5 hrf
      obtain ⟨s', n, hE, hn, hs'1, hs'r, hfr⟩ := enumNil_ev main addP (s := s) h1
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine loopRuns.mono (by omega) (loopRuns.one hrf hE) ?_
        simp only [List.length_nil, enumCost_nil]
        omega
      · rw [hfr 0 (by decide)]
        simpa using h0
      · exact hs'1
      · rw [hfr 5 (by decide), h5]
        simp [lab]
      · exact hs'r
      · intro k hk0 hk1 hk5
        exact hfr k hk1
  | cons x xs ih =>
      intro i acc rest R S₁ S₅ s h0 h1 h5 hrf
      obtain ⟨s₁, n₁, hE₁, hn₁, h₁0, h₁1, h₁5, h₁r, h₁f⟩ :=
        enumCons_ev (main := main) (addP := addP) hadd (s := s) (i := i) (x := x) (xs := xs)
          (acc := acc) (rest := rest) (R := R) (S₁ := S₁) (S₅ := S₅) h0 h1 h5
      obtain ⟨s₂, hrun₂, h₂0, h₂1, h₂5, h₂r, h₂f⟩ :=
        ih (i + 1) (Val.cons (.int (i : ℤ)) x :: acc) rest R S₁ S₅ s₁ h₁0 h₁1 h₁5 h₁r
      have hconcat : loopRuns main rEn Glyph.cons (enumBody addP) ((x :: xs).length + 1) s s₂
          ((n₁ + 1) + enumCost (100 + Kadd) (i + 1) xs) := by
        have h := loopRuns.concat (xs.length + 1) (loopRuns.one hrf hE₁) hrun₂
        rwa [show (1 : ℕ) + (xs.length + 1) = (x :: xs).length + 1 from by
          rw [List.length_cons]; omega] at h
      have hcost : (n₁ + 1) + enumCost (100 + Kadd) (i + 1) xs
          ≤ enumCost (100 + Kadd) i (x :: xs) := by
        have h1 : enumCost (100 + Kadd) i (x :: xs)
            = (100 + Kadd) * (vsz x + isz (i : ℤ) + 4) + 1
              + enumCost (100 + Kadd) (i + 1) xs := by
          rw [enumCost_cons]; unfold iterCost; ring
        rw [h1]
        omega
      refine ⟨s₂, loopRuns.mono (by omega) hconcat hcost, ?_, ?_, ?_, ?_, ?_⟩
      · have h : (((i + 1) + xs.length : ℕ) : ℤ) = ((i + (x :: xs).length : ℕ) : ℤ) := by
          simp only [List.length_cons]
          omega
        rw [h₂0, h]
      · exact h₂1
      · have h : (lab (i + 1) xs).reverse ++ (Val.cons (.int (i : ℤ)) x :: acc)
            = (lab i (x :: xs)).reverse ++ acc := by
          simp only [lab_cons, List.reverse_cons, List.singleton_append, List.append_assoc]
        rw [h₂5, h]
      · exact h₂r
      · intro k hk0 hk1 hk5
        rw [h₂f k hk0 hk1 hk5, h₁f k hk0 hk1 hk5]

private theorem enumLoop_ev {main addP : Cmd} {Kadd : ℕ}
    (hadd : ∀ main : Cmd, BinOp main addP (fun _ _ => True) (· + ·)
      (fun a b => Kadd * (isz a + isz b)))
    {i : ℕ} {xs acc rest : List Val} {R S₁ S₅ : List Glyph} {s : State}
    (h0 : s.stk 0 = encs (.int (i : ℤ) :: rest) ++ R)
    (h1 : s.stk 1 = (ofList xs).enc ++ S₁)
    (h5 : s.stk 5 = (ofList acc).enc ++ S₅)
    (hrf : s.reg rEn = Glyph.cons) :
    ∃ s' n, Ev main (.loop rEn Glyph.cons (enumBody addP)) s s' n ∧
      n ≤ enumCost (100 + Kadd) i xs + 1 ∧
      s'.stk 0 = encs (.int ((i + xs.length : ℕ) : ℤ) :: rest) ++ R ∧
      s'.stk 1 = S₁ ∧
      s'.stk 5 = (ofList ((lab i xs).reverse ++ acc)).enc ++ S₅ ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k) := by
  obtain ⟨s', hrun, hs'0, hs'1, hs'5, hs'r, hfr⟩ :=
    enumLoopRuns hadd xs i acc rest R S₁ S₅ s h0 h1 h5 hrf
  obtain ⟨n, hev, hle⟩ := loopRuns.eval hrun (by rw [hs'r]; decide)
  exact ⟨s', n, ⟨n, hev, le_rfl⟩, hle, hs'0, hs'1, hs'5, hfr⟩

/-! ## `enumerateWord` -/

/-- **`LayoutLib.enumerate`**: label `xs[i]` by `cons (int i) xs[i]`.  Walk the list in order, keeping a
binary `int i` counter on a scratch stack and incrementing it (`IntLib.add` with `int 1`) once per
element — total cost `Σ_{i<N} isz i = O(N log N)`, within the bound `N*(N.size+1)`.  (Labelling needs a
copy of the counter, so use a raw copy program.) -/
theorem enumerateWord (hI : HvdH.IntLib) : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
      out = ofList ((List.range xs.length).map fun i : ℕ => Val.cons (.int (i : ℤ)) (xs.getD i .nil)) :: rest)
    (fun _ => K * (vsz (ofList xs) + xs.length * (xs.length.size + 1) + 1)) := by
  obtain ⟨addP, Kadd, hadd⟩ := hI.add
  obtain ⟨revP, Krev, hrev⟩ := reverseWord
  refine ⟨seqs [mvVal 0 1 2 3, pushIntZero, pushConst 5 Glyph.nil, .set rEn Glyph.cons,
      .loop rEn Glyph.cons (enumBody addP), dropVal 0 2 3, mvVal 5 0 6 7, revP],
    100 * (Kadd + Krev + 100), ?_⟩
  intro main xs vs hpre s R hs
  obtain ⟨rest, rfl⟩ := hpre
  have hs0 : s.stk 0 = (ofList xs).enc ++ (encs rest ++ R) := by
    rw [hs, encs_cons, List.append_assoc]
  -- (1) move the list to stack 1
  obtain ⟨t₁, m₁, hF₁, hm₁, ht₁_0, ht₁_1, ht₁_2, ht₁_3, htf₁⟩ :=
    mvVal_state (main := main) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (s := s) (v := ofList xs) (A := encs rest ++ R) (B := s.stk 1) hs0 rfl
  -- (2) the initial counter `int 0`
  obtain ⟨t₂, m₂, hF₂, hm₂, ht₂_0, htf₂⟩ := pushIntZero_state main t₁
  -- (3) the initial accumulator `nil`
  obtain ⟨t₃, m₃, hF₃, hm₃, ht₃_5, htf₃⟩ := pushGlyph_state main 5 Glyph.nil t₂
  -- (4) the loop flag
  obtain ⟨t₄, m₄, hF₄, hm₄, ht₄, ht₄r⟩ := set_state main rEn Glyph.cons t₃
  have hL0 : t₄.stk 0 = encs (.int (0 : ℤ) :: rest) ++ R := by
    rw [ht₄, htf₃ 0 (by decide), ht₂_0, ht₁_0, encs_cons, List.append_assoc]
  have hL1 : t₄.stk 1 = (ofList xs).enc ++ s.stk 1 := by
    rw [ht₄, htf₃ 1 (by decide), htf₂ 1 (by decide), ht₁_1]
  have hL5 : t₄.stk 5 = (ofList ([] : List Val)).enc ++ s.stk 5 := by
    rw [ht₄, ht₃_5, htf₂ 5 (by decide), htf₁ 5 (by decide) (by decide) (by decide) (by decide)]
    simp [ofList, Val.enc, List.nil_append]
  -- (5) the loop
  obtain ⟨t₅, m₅, hF₅, hm₅, ht₅_0, ht₅_1, ht₅_5, htf₅⟩ :=
    enumLoop_ev (main := main) (addP := addP) hadd (i := 0) (xs := xs) (acc := []) (rest := rest)
      (R := R) (S₁ := s.stk 1) (S₅ := s.stk 5) (s := t₄) hL0 hL1 hL5 ht₄r
  -- (6) delete the counter `int xs.length`
  obtain ⟨t₆, m₆, hF₆, hm₆, ht₆_0, ht₆_2, ht₆_3, htf₆⟩ :=
    dropVal_state (main := main) (a := 0) (c := 2) (d := 3) (by decide) (by decide) (by decide)
      (s := t₅) (v := .int (xs.length : ℤ)) (A := encs rest ++ R)
      (by rw [ht₅_0, Nat.zero_add, encs_cons, List.append_assoc])
  -- (7) move the accumulator to stack 0
  obtain ⟨t₇, m₇, hF₇, hm₇, ht₇_5, ht₇_0, ht₇_6, ht₇_7, htf₇⟩ :=
    mvVal_state (main := main) (a := 5) (b := 0) (c := 6) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (s := t₆) (v := ofList (lab 0 xs).reverse) (A := s.stk 5) (B := t₆.stk 0)
      (by rw [htf₆ 5 (by decide) (by decide) (by decide), ht₅_5, List.append_nil])
      rfl
  -- (8) reverse it
  obtain ⟨out, t₈, m₈, hpost, hF₈, hm₈, ht₈, htf₈⟩ :=
    hrev main (lab 0 xs).reverse (ofList (lab 0 xs).reverse :: rest) ⟨rest, rfl⟩ t₇ R
      (by rw [ht₇_0, ht₆_0, encs_cons, ← List.append_assoc])
  obtain ⟨rest', hrest', hout⟩ := hpost
  have hrst : rest' = rest := (List.cons.inj hrest').2.symm
  have hEv : Ev main (seqs [mvVal 0 1 2 3, pushIntZero, pushConst 5 Glyph.nil, .set rEn Glyph.cons,
      .loop rEn Glyph.cons (enumBody addP), dropVal 0 2 3, mvVal 5 0 6 7, revP]) s t₈
      (m₁ + (m₂ + (m₃ + (m₄ + (m₅ + (m₆ + (m₇ + m₈))))))) := by
    unfold seqs
    exact Ev.seq hF₁ (Ev.seq hF₂ (Ev.seq hF₃ (Ev.seq hF₄ (Ev.seq hF₅ (Ev.seq hF₆
      (Ev.seq hF₇ ⟨m₈, hF₈, le_rfl⟩))))))
  obtain ⟨n, hev, hnle⟩ := hEv
  refine ⟨out, t₈, n, ⟨rest, rfl, ?_⟩, hev, ?_, ht₈, ?_⟩
  · rw [hout, List.reverse_reverse, lab_zero_eq, hrst]
  · -- the cost bound
    have hlab : vsz (ofList (lab 0 xs)) ≤ vsz (ofList xs) + 4 * (xs.length * (xs.length.size + 1) + 1) :=
      vsz_ofList_lab_le xs
    have hrev' : vsz (ofList (lab 0 xs).reverse) = vsz (ofList (lab 0 xs)) := vsz_ofList_reverse _
    have hcost5 : m₅ ≤ 4 * (101 + Kadd) * (vsz (ofList xs) + xs.length * (xs.length.size + 1) + 10) := by
      have h := enumCost_bound (100 + Kadd) xs
      have e : 4 * (100 + Kadd + 1) = 4 * (101 + Kadd) := by ring
      rw [e] at h
      omega
    have hcost6 : m₆ ≤ 16 * (xs.length.size + 3) := by
      have h := hm₆
      simp only [vsz_int, isz, Int.natAbs_natCast] at h
      omega
    have hstep2 : vsz (ofList (lab 0 xs)) + 1
        ≤ vsz (ofList xs) + 4 * (xs.length * (xs.length.size + 1) + 1) + 1 := by omega
    have hcost7 : m₇ ≤ 16 * (vsz (ofList xs) + 4 * (xs.length * (xs.length.size + 1) + 1) + 1) := by
      have h := hm₇
      simp only [hrev'] at h
      exact le_trans h (Nat.mul_le_mul_left 16 hstep2)
    have hcost8 : m₈ ≤ Krev * (vsz (ofList xs) + 4 * (xs.length * (xs.length.size + 1) + 1) + 1) := by
      have h := hm₈
      simp only [hrev'] at h
      exact le_trans h (Nat.mul_le_mul_left Krev hstep2)
    have hsum := sum8_le (a1 := m₁) (a2 := m₂) (a3 := m₃) (a4 := m₄) (a5 := m₅) (a6 := m₆)
      (a7 := m₇) (a8 := m₈) (b1 := 16 * (vsz (ofList xs) + 1)) (b2 := 4) (b3 := 2) (b4 := 1)
      (b5 := 4 * (101 + Kadd) * (vsz (ofList xs) + xs.length * (xs.length.size + 1) + 10))
      (b6 := 16 * (xs.length.size + 3))
      (b7 := 16 * (vsz (ofList xs) + 4 * (xs.length * (xs.length.size + 1) + 1) + 1))
      (b8 := Krev * (vsz (ofList xs) + 4 * (xs.length * (xs.length.size + 1) + 1) + 1))
      (by omega) hm₂ hm₃ hm₄ hcost5 hcost6 hcost7 hcost8
    have hfin := final_le Kadd Krev (vsz (ofList xs)) (xs.length * (xs.length.size + 1))
      xs.length.size (nsize_bound xs.length)
    have e1 : m₁ + (m₂ + (m₃ + (m₄ + (m₅ + (m₆ + (m₇ + m₈))))))
        = m₁ + m₂ + m₃ + m₄ + m₅ + m₆ + m₇ + m₈ := by omega
    rw [e1] at hnle
    exact le_trans hnle (le_trans hsum hfin)
  · -- frame: every other stack is restored
    intro k hk0
    have e8 : t₈.stk k = t₇.stk k := htf₈ k hk0
    have h5s : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 5 → t₅.stk k = s.stk k := by
      intro k hk0 hk1 hk5
      by_cases hk2 : k = 2
      · subst hk2
        rw [htf₅ 2 (by decide) (by decide) hk5, ht₄, htf₃ 2 (by decide), htf₂ 2 (by decide), ht₁_2]
      by_cases hk3 : k = 3
      · subst hk3
        rw [htf₅ 3 (by decide) (by decide) hk5, ht₄, htf₃ 3 (by decide), htf₂ 3 (by decide), ht₁_3]
      rw [htf₅ k hk0 hk1 hk5, ht₄, htf₃ k hk5, htf₂ k hk0, htf₁ k hk0 hk1 hk2 hk3]
    by_cases hk5 : k = 5
    · subst hk5; rw [e8, ht₇_5]
    by_cases hk1 : k = 1
    · subst hk1
      rw [e8, htf₇ 1 (by decide) (by decide) (by decide) (by decide),
        htf₆ 1 (by decide) (by decide) (by decide), ht₅_1]
    by_cases hk6 : k = 6
    · subst hk6
      rw [e8, ht₇_6, htf₆ 6 (by decide) (by decide) (by decide)]
      exact h5s 6 (by decide) (by decide) (by decide)
    by_cases hk7 : k = 7
    · subst hk7
      rw [e8, ht₇_7, htf₆ 7 (by decide) (by decide) (by decide)]
      exact h5s 7 (by decide) (by decide) (by decide)
    by_cases hk2 : k = 2
    · subst hk2
      rw [e8, htf₇ 2 hk5 hk0 (by decide) (by decide), ht₆_2]
      exact h5s 2 (by decide) (by decide) (by decide)
    by_cases hk3 : k = 3
    · subst hk3
      rw [e8, htf₇ 3 hk5 hk0 (by decide) (by decide), ht₆_3]
      exact h5s 3 (by decide) (by decide) (by decide)
    rw [e8, htf₇ k hk5 hk0 hk6 hk7, htf₆ k hk0 hk2 hk3]
    exact h5s k hk0 hk1 hk5

end Work.Layout
