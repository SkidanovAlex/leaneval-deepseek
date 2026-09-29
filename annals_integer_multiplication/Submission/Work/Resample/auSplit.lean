import Mathlib
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auPeel
import Submission.Work.Layout.Move
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.IntLib.encodeNatBridge

namespace Work.Resample

open HvdH
open Work.Layout

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `auSplit`: splitting a list value at a given index

`auSplit` is the word that splits the list value on top of stack 0 at index `L` (read from stack 1):
the prefix `E.take L` stays on stack 0 (as a list value) and the elements of the suffix `E.drop L`
are moved — in order, above the `nil` frame — onto stack 2.

The program is a straight line:

1. `mvVal 1 0` moves `int L` from stack 1 to the value stack;
2. `dup`, `mvVal 0 1` duplicate it so that stack 1 holds `int L` again and stack 0 has a copy on
   top of `ofList E`;
3. `LayoutLib.take` keeps `ofList (E.take L)` and exposes `ofList E` again;
4. `swap` brings `ofList E` on top, and steps 1–2 are repeated to get a second copy of `int L`;
5. `LayoutLib.drop` gives `ofList (E.drop L)`, `LayoutLib.reverse` reverses it;
6. `auPeel` on stack 2 peels it, which puts the elements of `E.drop L` (in order) above the `nil`
   already on stack 2 and leaves `ofList (E.take L)` on stack 0.

`LayoutLib.take`/`drop`/`reverse` are the only words of the size of the list; every `mvVal` step is
linear in `vsz (int L)` and the peeling is linear in `vsz (ofList E)`, hence the uniform budget
`K * (vsz (ofList E) + isz (L : ℤ) + 1)`.
-/

/-! ## Scratch stacks of the split word -/

/-- First scratch stack of `auSplit` (buffer of `mvVal`). -/
def auSplitC : Stk := ⟨9, by decide⟩

/-- Second scratch stack of `auSplit` (buffer of `mvVal`). -/
def auSplitD : Stk := ⟨10, by decide⟩

/-! ## Sizes of list values -/

/-- `vsz` of an integer value is `isz`. -/
private theorem vsz_int_eq (z : ℤ) : vsz (Val.int z) = isz z := by
  show (Val.int z).enc.length = isz z
  rw [Work.IntLib.enc_int, List.length_cons, List.length_append, List.length_map,
    List.length_singleton, Work.IntLib.encodeNat_length]
  simp only [HvdH.isz]

/-- `vsz` of a `cons`-chain. -/
theorem vsz_ofList_cons (x : Val) (xs : List Val) :
    vsz (ofList (x :: xs)) = vsz x + vsz (ofList xs) + 1 := by
  simp only [ofList, List.foldr_cons, Val.enc, vsz, List.length_cons, List.length_append]

/-- `vsz` of a list value. -/
theorem vsz_ofList_eq (A : List Val) : vsz (ofList A) = (A.map vsz).sum + A.length + 1 := by
  induction A with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      rw [vsz_ofList_cons x xs, ih]
      show vsz x + ((xs.map vsz).sum + xs.length + 1) + 1 =
        (vsz x + (xs.map vsz).sum) + (xs.length + 1) + 1
      omega

/-- The `vsz`-sum of a `take` is at most the `vsz`-sum of the list. -/
theorem sum_map_take_le : ∀ (E : List Val) (L : ℕ), ((E.take L).map vsz).sum ≤ (E.map vsz).sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: xs, (n + 1) => by
      have ih := sum_map_take_le xs n
      show vsz x + ((xs.take n).map vsz).sum ≤ vsz x + (xs.map vsz).sum
      omega

/-- The `vsz`-sum of a `drop` is at most the `vsz`-sum of the list. -/
theorem sum_map_drop_le : ∀ (E : List Val) (L : ℕ), ((E.drop L).map vsz).sum ≤ (E.map vsz).sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: xs, (n + 1) => by
      have ih := sum_map_drop_le xs n
      show ((xs.drop n).map vsz).sum ≤ vsz x + (xs.map vsz).sum
      omega

/-- Length of a `take`. -/
theorem take_length_le : ∀ (E : List Val) (L : ℕ), (E.take L).length ≤ E.length
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: xs, (n + 1) => by
      have ih := take_length_le xs n
      show (x :: xs.take n).length ≤ (x :: xs).length
      simp only [List.length_cons]
      omega

/-- Length of a `drop`. -/
theorem drop_length_le : ∀ (E : List Val) (L : ℕ), (E.drop L).length ≤ E.length
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: xs, (n + 1) => by
      have ih := drop_length_le xs n
      show (xs.drop n).length ≤ (x :: xs).length
      simp only [List.length_cons]
      omega

/-- Size of the prefix of a list value. -/
theorem vsz_take_le (E : List Val) (L : ℕ) : vsz (ofList (E.take L)) ≤ vsz (ofList E) := by
  rw [vsz_ofList_eq, vsz_ofList_eq]
  have h1 := sum_map_take_le E L
  have h2 := take_length_le E L
  omega

/-- Size of the suffix of a list value. -/
theorem vsz_drop_le (E : List Val) (L : ℕ) : vsz (ofList (E.drop L)) ≤ vsz (ofList E) := by
  rw [vsz_ofList_eq, vsz_ofList_eq]
  have h1 := sum_map_drop_le E L
  have h2 := drop_length_le E L
  omega

/-- Reversing a list does not change the size of its list value. -/
theorem vsz_ofList_reverse (A : List Val) : vsz (ofList A.reverse) = vsz (ofList A) := by
  rw [vsz_ofList_eq, vsz_ofList_eq, List.map_reverse, List.sum_reverse, List.length_reverse]

/-! ## Pipelines on the value stack -/

/-- `SplitPipe main p A B c`: the word `p` rewrites the fixed window `A` of values on top of the
value stack into `B`, leaving everything below it and every other stack untouched, at cost `≤ c`. -/
def SplitPipe (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val, WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest)
    (fun _ => c)

/-- `SplitPipe` at the level of explicit states. -/
theorem splitPipe_ev {main p : Cmd} {A B : List Val} {c : ℕ} (h : SplitPipe main p A B c)
    {g : Reg → Glyph} {X : Stk → List Glyph} {R : List Glyph} {Tail : List Val}
    (h0 : X 0 = encs (A ++ Tail) ++ R) :
    ∃ s' n, Ev main p ⟨g, X⟩ s' n ∧ n ≤ c ∧ s'.stk 0 = encs (B ++ Tail) ++ R ∧
      ∀ k, k ≠ 0 → s'.stk k = X k := by
  obtain ⟨out, s', n, hout, hev, hn, h0', hk'⟩ := h Tail (A ++ Tail) rfl ⟨g, X⟩ R h0
  exact ⟨s', n, ⟨n, hev, le_rfl⟩, hn, by rw [h0', hout], hk'⟩

theorem splitPipe_dup {main p : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (a : Val) :
    SplitPipe main p [a] [a, a] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hvs1 : vs = a :: rest := hvs
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, h0, hk⟩ :=
    h main vs (by rw [hvs1]; exact List.cons_ne_nil a rest) s R hR
  have hvs1' : vs = v :: rest' := hvs'
  obtain ⟨h1, h2⟩ := List.cons.inj (hvs1.symm.trans hvs1')
  refine ⟨out, s', n, ?_, hev, ?_, h0, hk⟩
  · simp only [hout, ← h1, ← h2, List.cons_append, List.nil_append]
  · rw [hvs1] at hn; simpa using hn

theorem splitPipe_swap {main p : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) : SplitPipe main p [a, b] [b, a] (K * (vsz a + vsz b + 1)) := by
  intro rest vs hvs s R hR
  have hvs1 : vs = a :: b :: rest := hvs
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, h0, hk⟩ :=
    h main vs (by rw [hvs1]; simp only [List.length_cons]; omega) s R hR
  have hvs1' : vs = a' :: b' :: rest' := hvs'
  obtain ⟨h1, h2⟩ := List.cons.inj (hvs1.symm.trans hvs1')
  obtain ⟨h3, h4⟩ := List.cons.inj h2
  refine ⟨out, s', n, ?_, hev, ?_, h0, hk⟩
  · simp only [hout, ← h1, ← h3, ← h4, List.cons_append, List.nil_append]
  · rw [hvs1] at hn; simpa using hn

theorem splitPipe_pick {main p : Cmd} {K : ℕ}
    (h : WordR main p (fun vs => 1 < vs.length)
      (fun vs out => out = vs.getD 1 .nil :: vs)
      (fun vs => K * (1 + 1) * (((vs.take (1 + 1)).map vsz).sum + 1)))
    (a b : Val) : SplitPipe main p [a, b] [b, a, b] (K * 2 * (vsz a + vsz b + 1)) := by
  intro rest vs hvs s R hR
  have hvs1 : vs = a :: b :: rest := hvs
  obtain ⟨out, s', n, hout, hev, hn, h0, hk⟩ :=
    h vs (by rw [hvs1]; simp only [List.length_cons]; omega) s R hR
  have hd : (a :: b :: rest).getD 1 Val.nil = b := by simp
  refine ⟨out, s', n, ?_, hev, ?_, h0, hk⟩
  · simp only [hout, hvs1, hd, List.cons_append, List.nil_append]
  · rw [hvs1] at hn
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero] at hn
    exact hn
theorem splitPipe_takeDrop {main p : Cmd} {k : ℕ} {K : ℕ} {xs : List Val} {Bv : Val}
    (h : WordR main p (fun vs => ∃ rest, vs = .int (k : ℤ) :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int (k : ℤ) :: ofList xs :: rest ∧ out = Bv :: rest)
      (fun _ => K * (vsz (ofList xs) + isz (k : ℤ) + 1))) :
    SplitPipe main p [.int (k : ℤ), ofList xs] [Bv] (K * (vsz (ofList xs) + isz (k : ℤ) + 1)) := by
  intro rest vs hvs s R hR
  have hvs1 : vs = Val.int (k : ℤ) :: ofList xs :: rest := hvs
  obtain ⟨out, s', n, ⟨rest', hvs', hout⟩, hev, hn, h0, hk⟩ := h vs ⟨rest, hvs1⟩ s R hR
  have hvs1' : vs = Val.int (k : ℤ) :: ofList xs :: rest' := hvs'
  obtain ⟨_, h2⟩ := List.cons.inj (hvs1.symm.trans hvs1')
  obtain ⟨_, h4⟩ := List.cons.inj h2
  exact ⟨out, s', n, by simp only [hout, ← h4, List.cons_append, List.nil_append], hev, hn, h0, hk⟩

theorem splitPipe_reverse {main p : Cmd} {K : ℕ} {xs : List Val}
    (h : WordR main p (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
      (fun _ => K * (vsz (ofList xs) + 1))) :
    SplitPipe main p [ofList xs] [ofList xs.reverse] (K * (vsz (ofList xs) + 1)) := by
  intro rest vs hvs s R hR
  have hvs1 : vs = ofList xs :: rest := hvs
  obtain ⟨out, s', n, ⟨rest', hvs', hout⟩, hev, hn, h0, hk⟩ := h vs ⟨rest, hvs1⟩ s R hR
  have hvs1' : vs = ofList xs :: rest' := hvs'
  have h4 : rest = rest' := (List.cons.inj (hvs1.symm.trans hvs1')).2
  exact ⟨out, s', n, by simp only [hout, ← h4, List.cons_append, List.nil_append], hev, hn, h0, hk⟩

theorem splitPipe_dropTop {main p : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (a : Val) :
    SplitPipe main p [a] [] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hvs1 : vs = a :: rest := hvs
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, h0, hk⟩ :=
    h main vs (by rw [hvs1]; exact List.cons_ne_nil a rest) s R hR
  have hvs1' : vs = v :: rest' := hvs'
  have h4 : rest = rest' := (List.cons.inj (hvs1.symm.trans hvs1')).2
  refine ⟨out, s', n, ?_, hev, ?_, h0, hk⟩
  · simp only [hout, ← h4, List.nil_append]
  · rw [hvs1] at hn; simpa using hn

/-! ## State-level variants -/

/-- `mvVal` at the level of explicit states (the state is an argument, so that no `Eval`
statement mentions a state written as a pair of components). -/
theorem mvVal_state {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (s : State) {v : Val} {A B : List Glyph}
    (ha : s.stk a = v.enc ++ A) (hb : s.stk b = B) :
    ∃ s' n, Ev main (mvVal a b c d) s s' n ∧ n ≤ 16 * (vsz v + 1) ∧ s'.stk a = A ∧
      s'.stk b = v.enc ++ B ∧ s'.stk c = s.stk c ∧ s'.stk d = s.stk d ∧
      ∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = s.stk k := by
  obtain ⟨g, X⟩ := s
  obtain ⟨s', n, hev, hn, ha', hb', hc', hd', hk'⟩ :=
    Work.Layout.mvVal_ev_full (main := main) hab hac had hbc hbd hcd (g := g) (X := X) ha hb
  exact ⟨s', n, hev, hn, ha', hb', hc', hd', hk'⟩

/-- `SplitPipe` at the level of explicit states. -/
theorem splitPipe_state {main p : Cmd} {A B : List Val} {c : ℕ} (h : SplitPipe main p A B c)
    (s : State) {R : List Glyph} {Tail : List Val} (h0 : s.stk 0 = encs (A ++ Tail) ++ R) :
    ∃ s' n, Ev main p s s' n ∧ n ≤ c ∧ s'.stk 0 = encs (B ++ Tail) ++ R ∧
      ∀ k, k ≠ 0 → s'.stk k = s.stk k := by
  obtain ⟨g, X⟩ := s
  obtain ⟨s', n, hev, hn, h0', hk'⟩ :=
    splitPipe_ev (main := main) (A := A) (B := B) (Tail := Tail) (R := R) (g := g) (X := X) h h0
  exact ⟨s', n, hev, hn, h0', hk'⟩

/-! ## The split word -/


theorem auSplit (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (L : ℕ) (E P : List HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs a => vs = HvdH.ofList E :: P ∧ a 1 = [HvdH.Val.int (L : ℤ)] ∧
          a 2 = [HvdH.Val.nil])
        (fun vs a out b => out = HvdH.ofList (E.take L) :: P ∧
          b 1 = [HvdH.Val.int (L : ℤ)] ∧
          b 2 = E.drop L ++ [HvdH.Val.nil] ∧
          (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → b k = a k))
        (fun vs a => K * (HvdH.vsz (HvdH.ofList E) + HvdH.isz (L : ℤ) + 1)) := by
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨takeP, Kt, htake⟩ := hl.take
  obtain ⟨dropLP, Kdl, hdropL⟩ := hl.drop
  obtain ⟨revP, Kr, hrev⟩ := hl.reverse
  obtain ⟨peelP, Kpeel, hpeel⟩ := auPeel 2 (by decide)
  refine ⟨seqs [mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD, pickP 1, swapP,
    dropLP, revP, peelP, mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD, takeP],
    100 * (Kd + Ksw + Kt + Kdl + Kr + Kdr + Kpeel + Kp + 1), ?_⟩
  intro main L E P vs a hpre s R Bg h0 hfr
  obtain ⟨hvs, ha1, ha2⟩ := hpre
  have hX0 : s.stk 0 = encs (ofList E :: P) ++ R := by rw [h0, hvs]
  have hX1 : s.stk 1 = (Val.int (L : ℤ)).enc ++ Bg 1 := by
    have h := hfr 1 (by decide : (1 : Stk) ≠ 0)
    rw [ha1] at h
    simpa only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil] using h
  have hX2 : s.stk 2 = encs [Val.nil] ++ Bg 2 := by
    rw [hfr 2 (by decide : (2 : Stk) ≠ 0), ha2]
  -- ---- stage 1: `int L` from stack 1 to the value stack
  obtain ⟨s1, n1, hev1, hn1, hs1_1, hs1_0, hs1_c, hs1_d, ho1⟩ :=
    mvVal_state (a := 1) (b := 0) (c := auSplitC) (d := auSplitD)
      (by decide : (1 : Stk) ≠ 0) (by decide : (1 : Stk) ≠ auSplitC)
      (by decide : (1 : Stk) ≠ auSplitD) (by decide : (0 : Stk) ≠ auSplitC)
      (by decide : (0 : Stk) ≠ auSplitD) (by decide : auSplitC ≠ auSplitD) s
      (v := Val.int (L : ℤ)) (A := Bg 1) (B := encs (ofList E :: P) ++ R) hX1 hX0
  have hF1 : s1.stk 0 = encs (Val.int (L : ℤ) :: ofList E :: P) ++ R := by
    rw [hs1_0]; simp only [Work.Kernel.encs_cons, List.append_assoc]
  have hfr1 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s1.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    by_cases hkc : k = auSplitC
    · rw [hkc, hs1_c]
    · by_cases hkd : k = auSplitD
      · rw [hkd, hs1_d]
      · exact ho1 k hk1 hk0 hkc hkd
  -- ---- stage 2: duplicate `int L`
  obtain ⟨s2, n2, hev2, hn2, hF2', ho2⟩ :=
    splitPipe_state (A := [Val.int (L : ℤ)]) (B := [Val.int (L : ℤ), Val.int (L : ℤ)])
      (Tail := ofList E :: P) (R := R)
      (splitPipe_dup (main := main) hdup (Val.int (L : ℤ))) s1 hF1
  have hF2 : s2.stk 0 = encs (Val.int (L : ℤ) :: Val.int (L : ℤ) :: ofList E :: P) ++ R := hF2'
  have hfr2 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s2.stk k = s.stk k := by
    intro k hk0 hk1 hk2; rw [ho2 k hk0]; exact hfr1 k hk0 hk1 hk2
  have hs2_0e : s2.stk 0 =
      (Val.int (L : ℤ)).enc ++ (encs (Val.int (L : ℤ) :: ofList E :: P) ++ R) := by
    rw [hF2]; simp only [Work.Kernel.encs_cons, List.append_assoc]
  -- ---- stage 3: one copy back on stack 1
  obtain ⟨s3, n3, hev3, hn3, hs3_0, hs3_1, hs3_c, hs3_d, ho3⟩ :=
    mvVal_state (a := 0) (b := 1) (c := auSplitC) (d := auSplitD)
      (by decide : (0 : Stk) ≠ 1) (by decide : (0 : Stk) ≠ auSplitC)
      (by decide : (0 : Stk) ≠ auSplitD) (by decide : (1 : Stk) ≠ auSplitC)
      (by decide : (1 : Stk) ≠ auSplitD) (by decide : auSplitC ≠ auSplitD) s2
      (v := Val.int (L : ℤ))
      (A := encs (Val.int (L : ℤ) :: ofList E :: P) ++ R) (B := s2.stk 1) hs2_0e rfl
  have hF3 : s3.stk 0 = encs (Val.int (L : ℤ) :: ofList E :: P) ++ R := hs3_0
  have hs3_1e : s3.stk 1 = (Val.int (L : ℤ)).enc ++ Bg 1 := by
    rw [hs3_1, ho2 1 (by decide : (1 : Stk) ≠ 0), hs1_1]
  have hfr3 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s3.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    by_cases hkc : k = auSplitC
    · rw [hkc, hs3_c]; exact hfr2 auSplitC (by decide) (by decide) (by decide)
    · by_cases hkd : k = auSplitD
      · rw [hkd, hs3_d]; exact hfr2 auSplitD (by decide) (by decide) (by decide)
      · rw [ho3 k hk0 hk1 hkc hkd]; exact hfr2 k hk0 hk1 hk2
  -- ---- stage 4: copy of `ofList E` to the top
  obtain ⟨s4, n4, hev4, hn4, hF4', ho4⟩ :=
    splitPipe_state (A := [Val.int (L : ℤ), ofList E]) (B := [ofList E, Val.int (L : ℤ), ofList E])
      (Tail := P) (R := R)
      (splitPipe_pick (main := main) (hpick main 1) (Val.int (L : ℤ)) (ofList E)) s3 hF3
  have hF4 : s4.stk 0 =
      encs (ofList E :: Val.int (L : ℤ) :: ofList E :: P) ++ R := hF4'
  have hfr4 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s4.stk k = s.stk k := by
    intro k hk0 hk1 hk2; rw [ho4 k hk0]; exact hfr3 k hk0 hk1 hk2
  -- ---- stage 5: two copies of `ofList E` under `int L`
  obtain ⟨s5, n5, hev5, hn5, hF5', ho5⟩ :=
    splitPipe_state (A := [ofList E, Val.int (L : ℤ)]) (B := [Val.int (L : ℤ), ofList E])
      (Tail := ofList E :: P) (R := R)
      (splitPipe_swap (main := main) hswap (ofList E) (Val.int (L : ℤ))) s4 hF4
  have hF5 : s5.stk 0 =
      encs (Val.int (L : ℤ) :: ofList E :: ofList E :: P) ++ R := hF5'
  have hfr5 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s5.stk k = s.stk k := by
    intro k hk0 hk1 hk2; rw [ho5 k hk0]; exact hfr4 k hk0 hk1 hk2
  -- ---- stage 6: `drop L`
  obtain ⟨s6, n6, hev6, hn6, hF6', ho6⟩ :=
    splitPipe_state (A := [Val.int (L : ℤ), ofList E]) (B := [ofList (E.drop L)])
      (Tail := ofList E :: P) (R := R)
      (splitPipe_takeDrop (main := main) (k := L) (xs := E) (Bv := ofList (E.drop L))
        (hdropL main L E)) s5 hF5
  have hF6 : s6.stk 0 = encs (ofList (E.drop L) :: ofList E :: P) ++ R := hF6'
  have hfr6 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s6.stk k = s.stk k := by
    intro k hk0 hk1 hk2; rw [ho6 k hk0]; exact hfr5 k hk0 hk1 hk2
  -- ---- stage 7: `reverse`
  obtain ⟨s7, n7, hev7, hn7, hF7', ho7⟩ :=
    splitPipe_state (A := [ofList (E.drop L)]) (B := [ofList (E.drop L).reverse])
      (Tail := ofList E :: P) (R := R)
      (splitPipe_reverse (main := main) (xs := E.drop L) (hrev main (E.drop L))) s6 hF6
  have hF7 : s7.stk 0 = encs (ofList (E.drop L).reverse :: ofList E :: P) ++ R := hF7'
  have hfr7 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s7.stk k = s.stk k := by
    intro k hk0 hk1 hk2; rw [ho7 k hk0]; exact hfr6 k hk0 hk1 hk2
  -- ---- stage 8: peel the reversed suffix onto stack 2
  have hs7_1 : s7.stk 1 = (Val.int (L : ℤ)).enc ++ Bg 1 := by
    rw [ho7 1 (by decide : (1 : Stk) ≠ 0), ho6 1 (by decide : (1 : Stk) ≠ 0),
      ho5 1 (by decide : (1 : Stk) ≠ 0), ho4 1 (by decide : (1 : Stk) ≠ 0)]
    exact hs3_1e
  have hs7_2 : s7.stk 2 = encs [Val.nil] ++ Bg 2 := by
    rw [ho7 2 (by decide : (2 : Stk) ≠ 0), ho6 2 (by decide : (2 : Stk) ≠ 0),
      ho5 2 (by decide : (2 : Stk) ≠ 0), ho4 2 (by decide : (2 : Stk) ≠ 0),
      ho3 2 (by decide) (by decide) (by decide) (by decide),
      ho2 2 (by decide : (2 : Stk) ≠ 0), ho1 2 (by decide) (by decide) (by decide) (by decide)]
    exact hX2
  have hframe7 : ∀ k : Stk, k ≠ 0 → s7.stk k = encs (a k) ++ Bg k := by
    intro k hk0
    by_cases hk1 : k = 1
    · subst hk1
      rw [hs7_1, ha1]
      simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
    · by_cases hk2 : k = 2
      · subst hk2
        rw [hs7_2, ha2]
      · rw [hfr7 k hk0 hk1 hk2]
        exact hfr k hk0
  obtain ⟨out, b, s8, n8, hpost, hev8, hn8, hs8_0, hs8_fr⟩ :=
    hpeel main (E.drop L).reverse (ofList E :: P) Val.nil
      (ofList ((E.drop L).reverse) :: ofList E :: P) a ⟨rfl, ha2⟩ s7 R Bg hF7 hframe7
  have hs8_0e : s8.stk 0 = encs (ofList E :: P) ++ R := by rw [hs8_0, hpost.1]
  have hb1 : b 1 = [Val.int (L : ℤ)] := by
    rw [hpost.2.2.2 1 (by decide : (1 : Stk) ≠ 0) (by decide : (1 : Stk) ≠ 2)]
    exact ha1
  have hs8_1 : s8.stk 1 = (Val.int (L : ℤ)).enc ++ Bg 1 := by
    rw [hs8_fr 1 (by decide : (1 : Stk) ≠ 0), hb1]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
  have hfr8 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s8.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    rw [hs8_fr k hk0, hpost.2.2.2 k hk0 hk2, hfr k hk0]
  -- ---- stage 9: second copy of `int L` onto the value stack
  obtain ⟨s9, n9, hev9, hn9, hs9_1, hs9_0, hs9_c, hs9_d, ho9⟩ :=
    mvVal_state (a := 1) (b := 0) (c := auSplitC) (d := auSplitD)
      (by decide : (1 : Stk) ≠ 0) (by decide : (1 : Stk) ≠ auSplitC)
      (by decide : (1 : Stk) ≠ auSplitD) (by decide : (0 : Stk) ≠ auSplitC)
      (by decide : (0 : Stk) ≠ auSplitD) (by decide : auSplitC ≠ auSplitD) s8
      (v := Val.int (L : ℤ)) (A := Bg 1) (B := encs (ofList E :: P) ++ R) hs8_1 hs8_0e
  have hF9 : s9.stk 0 = encs (Val.int (L : ℤ) :: ofList E :: P) ++ R := by
    rw [hs9_0]; simp only [Work.Kernel.encs_cons, List.append_assoc]
  have hfr9 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s9.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    by_cases hkc : k = auSplitC
    · rw [hkc, hs9_c]; exact hfr8 auSplitC (by decide) (by decide) (by decide)
    · by_cases hkd : k = auSplitD
      · rw [hkd, hs9_d]; exact hfr8 auSplitD (by decide) (by decide) (by decide)
      · rw [ho9 k hk1 hk0 hkc hkd]; exact hfr8 k hk0 hk1 hk2
  -- ---- stage 10: duplicate the second copy
  obtain ⟨s10, n10, hev10, hn10, hF10', ho10⟩ :=
    splitPipe_state (A := [Val.int (L : ℤ)]) (B := [Val.int (L : ℤ), Val.int (L : ℤ)])
      (Tail := ofList E :: P) (R := R)
      (splitPipe_dup (main := main) hdup (Val.int (L : ℤ))) s9 hF9
  have hF10 : s10.stk 0 = encs (Val.int (L : ℤ) :: Val.int (L : ℤ) :: ofList E :: P) ++ R :=
    hF10'
  have hfr10 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s10.stk k = s.stk k := by
    intro k hk0 hk1 hk2; rw [ho10 k hk0]; exact hfr9 k hk0 hk1 hk2
  have hs10_0e : s10.stk 0 =
      (Val.int (L : ℤ)).enc ++ (encs (Val.int (L : ℤ) :: ofList E :: P) ++ R) := by
    rw [hF10]; simp only [Work.Kernel.encs_cons, List.append_assoc]
  -- ---- stage 11: one copy back on stack 1
  obtain ⟨s11, n11, hev11, hn11, hs11_0, hs11_1, hs11_c, hs11_d, ho11⟩ :=
    mvVal_state (a := 0) (b := 1) (c := auSplitC) (d := auSplitD)
      (by decide : (0 : Stk) ≠ 1) (by decide : (0 : Stk) ≠ auSplitC)
      (by decide : (0 : Stk) ≠ auSplitD) (by decide : (1 : Stk) ≠ auSplitC)
      (by decide : (1 : Stk) ≠ auSplitD) (by decide : auSplitC ≠ auSplitD) s10
      (v := Val.int (L : ℤ))
      (A := encs (Val.int (L : ℤ) :: ofList E :: P) ++ R) (B := s10.stk 1) hs10_0e rfl
  have hF11 : s11.stk 0 = encs (Val.int (L : ℤ) :: ofList E :: P) ++ R := hs11_0
  have hs11_1e : s11.stk 1 = (Val.int (L : ℤ)).enc ++ Bg 1 := by
    rw [hs11_1, ho10 1 (by decide : (1 : Stk) ≠ 0), hs9_1]
  have hfr11 : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s11.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    by_cases hkc : k = auSplitC
    · rw [hkc, hs11_c]; exact hfr10 auSplitC (by decide) (by decide) (by decide)
    · by_cases hkd : k = auSplitD
      · rw [hkd, hs11_d]; exact hfr10 auSplitD (by decide) (by decide) (by decide)
      · rw [ho11 k hk0 hk1 hkc hkd]; exact hfr10 k hk0 hk1 hk2
  -- ---- stage 12: `take L`
  obtain ⟨s12, n12, hev12, hn12, hF12', ho12⟩ :=
    splitPipe_state (A := [Val.int (L : ℤ), ofList E]) (B := [ofList (E.take L)]) (Tail := P)
      (R := R)
      (splitPipe_takeDrop (main := main) (k := L) (xs := E) (Bv := ofList (E.take L))
        (htake main L E)) s11 hF11
  have hF12 : s12.stk 0 = encs (ofList (E.take L) :: P) ++ R := hF12'
  -- ---- final state
  have hb2 : b 2 = E.drop L ++ [Val.nil] := by simpa using hpost.2.2.1
  have hbfr : ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → b k = a k := fun k h0 h1 h2 => hpost.2.2.2 k h0 h2
  have hs12_0 : s12.stk 0 = encs (ofList (E.take L) :: P) ++ R := hF12
  have hs12_1 : s12.stk 1 = encs (b 1) ++ Bg 1 := by
    rw [ho12 1 (by decide : (1 : Stk) ≠ 0), hs11_1e, hb1]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]
  have hs12_2 : s12.stk 2 = encs (b 2) ++ Bg 2 := by
    rw [ho12 2 (by decide : (2 : Stk) ≠ 0),
      ho11 2 (by decide) (by decide) (by decide) (by decide),
      ho10 2 (by decide : (2 : Stk) ≠ 0),
      ho9 2 (by decide) (by decide) (by decide) (by decide)]
    exact hs8_fr 2 (by decide : (2 : Stk) ≠ 0)
  have hs12_fr : ∀ k : Stk, k ≠ 0 → s12.stk k = encs (b k) ++ Bg k := by
    intro k hk0
    by_cases hk1 : k = 1
    · subst hk1; exact hs12_1
    · by_cases hk2 : k = 2
      · subst hk2; exact hs12_2
      · rw [ho12 k hk0, hfr11 k hk0 hk1 hk2, hfr k hk0, ← hbfr k hk0 hk1 hk2]
  -- ---- the cost bound
  rw [vsz_int_eq] at hn1 hn2 hn3 hn4 hn5 hn9 hn10 hn11
  have hTL := vsz_drop_le E L
  have hDR : vsz (ofList (E.drop L).reverse) ≤ vsz (ofList E) := by
    rw [vsz_ofList_reverse]; exact hTL
  have hE1 : 1 ≤ vsz (ofList E) := one_le_vsz _
  have hbound : n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))))))
      ≤ 100 * (Kd + Ksw + Kt + Kdl + Kr + Kdr + Kpeel + Kp + 1) *
        (vsz (ofList E) + isz (L : ℤ) + 1) := by
    nlinarith [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hTL, hDR, hE1]
  -- ---- assembly
  have hev8' : Ev main peelP s7 s8 n8 := ⟨n8, hev8, le_rfl⟩
  have e12 : Ev main (seqs [takeP]) s11 s12 n12 := by simpa only [seqs] using hev12
  have e11 : Ev main (seqs [mvVal 0 1 auSplitC auSplitD, takeP]) s10 s12 (n11 + n12) := by
    simpa only [seqs] using Ev.seq' hev11 e12 (le_refl (n11 + n12))
  have e10 : Ev main (seqs [dupP, mvVal 0 1 auSplitC auSplitD, takeP]) s9 s12
      (n10 + (n11 + n12)) := by
    simpa only [seqs] using Ev.seq' hev10 e11 (le_refl (n10 + (n11 + n12)))
  have e9 : Ev main (seqs [mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD, takeP])
      s8 s12 (n9 + (n10 + (n11 + n12))) := by
    simpa only [seqs] using Ev.seq' hev9 e10 (le_refl (n9 + (n10 + (n11 + n12))))
  have e8 : Ev main (seqs [peelP, mvVal 1 0 auSplitC auSplitD, dupP,
      mvVal 0 1 auSplitC auSplitD, takeP]) s7 s12 (n8 + (n9 + (n10 + (n11 + n12)))) := by
    simpa only [seqs] using Ev.seq' hev8' e9 (le_refl (n8 + (n9 + (n10 + (n11 + n12)))))
  have e7 : Ev main (seqs [revP, peelP, mvVal 1 0 auSplitC auSplitD, dupP,
      mvVal 0 1 auSplitC auSplitD, takeP]) s6 s12 (n7 + (n8 + (n9 + (n10 + (n11 + n12))))) := by
    simpa only [seqs] using Ev.seq' hev7 e8
      (le_refl (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))
  have e6 : Ev main (seqs [dropLP, revP, peelP, mvVal 1 0 auSplitC auSplitD, dupP,
      mvVal 0 1 auSplitC auSplitD, takeP]) s5 s12
      (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12)))))) := by
    simpa only [seqs] using Ev.seq' hev6 e7
      (le_refl (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12)))))))
  have e5 : Ev main (seqs [swapP, dropLP, revP, peelP, mvVal 1 0 auSplitC auSplitD, dupP,
      mvVal 0 1 auSplitC auSplitD, takeP]) s4 s12
      (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))) := by
    simpa only [seqs] using Ev.seq' hev5 e6
      (le_refl (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))))
  have e4 : Ev main (seqs [pickP 1, swapP, dropLP, revP, peelP, mvVal 1 0 auSplitC auSplitD, dupP,
      mvVal 0 1 auSplitC auSplitD, takeP]) s3 s12
      (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12)))))))) := by
    simpa only [seqs] using Ev.seq' hev4 e5
      (le_refl (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12)))))))))
  have e3 : Ev main (seqs [mvVal 0 1 auSplitC auSplitD, pickP 1, swapP, dropLP, revP, peelP,
      mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD, takeP]) s2 s12
      (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))))) := by
    simpa only [seqs] using Ev.seq' hev3 e4
      (le_refl (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))))))
  have e2 : Ev main (seqs [dupP, mvVal 0 1 auSplitC auSplitD, pickP 1, swapP, dropLP, revP, peelP,
      mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD, takeP]) s1 s12
      (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12)))))))))) := by
    simpa only [seqs] using Ev.seq' hev2 e3
      (le_refl (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12)))))))))))
  have e1 : Ev main (seqs [mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD, pickP 1,
      swapP, dropLP, revP, peelP, mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD,
      takeP]) s s12 (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))))))) := by
    simpa only [seqs] using Ev.seq' hev1 e2
      (le_refl (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12))))))))))))
  have hEvAll : Ev main (seqs [mvVal 1 0 auSplitC auSplitD, dupP, mvVal 0 1 auSplitC auSplitD,
      pickP 1, swapP, dropLP, revP, peelP, mvVal 1 0 auSplitC auSplitD, dupP,
      mvVal 0 1 auSplitC auSplitD, takeP]) s s12
      (100 * (Kd + Ksw + Kt + Kdl + Kr + Kdr + Kpeel + Kp + 1) *
        (vsz (ofList E) + isz (L : ℤ) + 1)) := e1.mono hbound
  obtain ⟨n, hev, hn⟩ := hEvAll
  exact ⟨ofList (E.take L) :: P, b, s12, n, ⟨rfl, hb1, hb2, hbfr⟩, hev, hn, hs12_0, hs12_fr⟩

end Work.Resample
