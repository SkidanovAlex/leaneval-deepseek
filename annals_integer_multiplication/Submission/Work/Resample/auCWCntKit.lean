import Mathlib
import Submission.Work.Resample.auCWCntDefs
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.ifNil
import Submission.Work.Kernel.ifZero
import Submission.Work.Kernel.consV
import Submission.Work.Kernel.unconsV
import Submission.Work.Kernel.dropValue
import Submission.Work.Kernel.dup
import Submission.Work.Kernel.swap
import Submission.Work.Kernel.pick
import Submission.Work.Kernel.roll

/-!
# Toolkit for the record-counting word `Work.Resample.auCWExtract`

* concrete sizes of the four carry records (`awRec`) and of the small values they are mapped to;
* `seqC` / `conseqC`: composition and window specialisation of `WordR` words with *concrete*
  windows (`vs = A` in, `out = B` out), which keep costs constant;
* window instances of the library words (`unconsWin`, `dupWin`, `swapWin`, `dropWin`, `pushWin`,
  `eqWin`, `consWin`);
* the per-record words `cntBody1`/`cntBody2` (keep only the `.int 1` / `.int 2` markers);
* the list identities `cntFlatLen1/2` (length of the flattened marker chain).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Concrete values and sizes -/

theorem vsz_int_one : vsz (Val.int 1) = 3 := by decide +kernel
theorem vsz_int_two : vsz (Val.int 2) = 4 := by decide +kernel
theorem vsz_nil_val : vsz Val.nil = 1 := by decide +kernel
theorem vsz_cons_one_nil : vsz (Val.cons (Val.int 1) Val.nil) = 5 := by decide +kernel
theorem vsz_cons_one_two : vsz (Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil)) = 10 := by decide +kernel
theorem vsz_cons_two_nil : vsz (Val.cons (Val.int 2) Val.nil) = 6 := by decide +kernel
theorem isz_one_z : isz (1 : ℤ) = 3 := by decide +kernel
theorem isz_two_z : isz (2 : ℤ) = 4 := by decide +kernel
theorem isz_zero_z : isz (0 : ℤ) = 2 := by decide +kernel

theorem awRec_00 : awRec 0 0 = Val.nil := rfl
theorem awRec_10 : awRec 1 0 = Val.cons (Val.int 1) Val.nil := rfl
theorem awRec_01 : awRec 0 1 = Val.cons (Val.int 2) Val.nil := rfl
theorem awRec_11 : awRec 1 1 = Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil) := rfl

theorem awSub1_00 : awSub1 (awRec 0 0) = Val.nil := by decide +kernel
theorem awSub1_10 : awSub1 (awRec 1 0) = Val.cons (Val.int 1) Val.nil := by decide +kernel
theorem awSub1_01 : awSub1 (awRec 0 1) = Val.nil := by decide +kernel
theorem awSub1_11 : awSub1 (awRec 1 1) = Val.cons (Val.int 1) Val.nil := by decide +kernel
theorem awSub2_00 : awSub2 (awRec 0 0) = Val.nil := by decide +kernel
theorem awSub2_10 : awSub2 (awRec 1 0) = Val.nil := by decide +kernel
theorem awSub2_01 : awSub2 (awRec 0 1) = Val.cons (Val.int 2) Val.nil := by decide +kernel
theorem awSub2_11 : awSub2 (awRec 1 1) = Val.cons (Val.int 2) Val.nil := by decide +kernel

/-! ## Composition on concrete windows -/

/-- Composition of two words with concrete windows `A → B → D`. -/
theorem seqC {main p q : HvdH.Cmd} {A B D : List HvdH.Val} {c d : ℕ}
    (h1 : HvdH.WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c))
    (h2 : HvdH.WordR main q (fun vs => vs = B) (fun _ out => out = D) (fun _ => d)) :
    HvdH.WordR main (HvdH.Cmd.seq p q) (fun vs => vs = A) (fun _ out => out = D) (fun _ => c + d) := by
  intro vs hvs s Rg hR
  obtain ⟨mid, s1, n1, hmid, hev1, hn1, h01, hk1⟩ := h1 vs hvs s Rg hR
  obtain ⟨out, s2, n2, hout, hev2, hn2, h02, hk2⟩ := h2 mid hmid s1 Rg h01
  have hn1' : n1 ≤ c := hn1
  have hn2' : n2 ≤ d := hn2
  have hcost : n1 + n2 ≤ c + d := by omega
  exact ⟨out, s2, n1 + n2, hout, Eval.seq hev1 hev2, hcost, h02,
    fun k hk => by rw [hk2 k hk, hk1 k hk]⟩

/-- Composition where the second word has an arbitrary postcondition. -/
theorem seqC2 {main p q : HvdH.Cmd} {A B : List HvdH.Val} {Q : List HvdH.Val → Prop}
    {c d : ℕ}
    (h1 : HvdH.WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c))
    (h2 : HvdH.WordR main q (fun vs => vs = B) (fun _ out => Q out) (fun _ => d)) :
    HvdH.WordR main (HvdH.Cmd.seq p q) (fun vs => vs = A) (fun _ out => Q out) (fun _ => c + d) := by
  intro vs hvs s Rg hR
  obtain ⟨mid, s1, n1, hmid, hev1, hn1, h01, hk1⟩ := h1 vs hvs s Rg hR
  obtain ⟨out, s2, n2, hout, hev2, hn2, h02, hk2⟩ := h2 mid hmid s1 Rg h01
  have hn1' : n1 ≤ c := hn1
  have hn2' : n2 ≤ d := hn2
  have hcost : n1 + n2 ≤ c + d := by omega
  exact ⟨out, s2, n1 + n2, hout, Eval.seq hev1 hev2, hcost, h02,
    fun k hk => by rw [hk2 k hk, hk1 k hk]⟩

/-- Specialisation of a `WordR` word to a concrete pre-window `A` and post-window `B`. -/
theorem conseqC {main p : HvdH.Cmd} {A B : List HvdH.Val} {c : ℕ}
    {P : List HvdH.Val → Prop} {Q : List HvdH.Val → List HvdH.Val → Prop} {C : List HvdH.Val → ℕ}
    (h : HvdH.WordR main p P Q C) (hP : P A) (hQ : ∀ out, Q A out → out = B) (hC : C A ≤ c) :
    HvdH.WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c) := by
  refine Work.Kernel.WordR_conseq h ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hP
  · intro vs out hvs hq; rw [hvs] at hq; exact hQ out hq
  · intro vs hvs; rw [hvs]; exact hC

/-- Monotone cost for a word with a concrete window. -/
theorem conseqC' {main p : HvdH.Cmd} {A B : List HvdH.Val} {c c' : ℕ}
    (h : HvdH.WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c)) (hc : c ≤ c') :
    HvdH.WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c') := by
  intro vs hvs s Rg hR
  obtain ⟨out, s1, n, hout, hev, hn, h0, hk⟩ := h vs hvs s Rg hR
  exact ⟨out, s1, n, hout, hev, le_trans hn hc, h0, hk⟩

/-! ## Window instances of the library words -/

theorem unconsWin {main p : HvdH.Cmd} {K c : ℕ} {a b : HvdH.Val} {r : List HvdH.Val} (hc : K ≤ c)
    (h : HvdH.WordR main p (fun vs => ∃ a b r, vs = HvdH.Val.cons a b :: r)
      (fun vs out => ∃ a b r, vs = HvdH.Val.cons a b :: r ∧ out = a :: b :: r) (fun _ => K)) :
    HvdH.WordR main p (fun vs => vs = HvdH.Val.cons a b :: r) (fun _ out => out = a :: b :: r)
      (fun _ => c) := by
  refine conseqC h ⟨a, b, r, rfl⟩ ?_ hc
  intro out hout
  obtain ⟨a', b', r', hv, ho⟩ := hout
  obtain ⟨h1, h2⟩ := List.cons.inj hv
  obtain ⟨h3, h4⟩ := HvdH.Val.cons.inj h1
  rw [← h3, ← h4, ← h2] at ho
  exact ho

theorem dupWin {main p : HvdH.Cmd} {K c : ℕ} {a : HvdH.Val} {r : List HvdH.Val}
    (hc : K * (HvdH.vsz a + 1) ≤ c)
    (h : HvdH.WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1))) :
    HvdH.WordR main p (fun vs => vs = a :: r) (fun _ out => out = a :: a :: r) (fun _ => c) := by
  refine conseqC h (by simp) ?_ hc
  intro out hout
  obtain ⟨v, rest, hv, ho⟩ := hout
  obtain ⟨h1, h2⟩ := List.cons.inj hv
  rw [← h1, ← h2] at ho
  exact ho

theorem swapWin {main p : HvdH.Cmd} {K c : ℕ} {a b : HvdH.Val} {r : List HvdH.Val}
    (hc : K * (HvdH.vsz a + HvdH.vsz b + 1) ≤ c)
    (h : HvdH.WordR main p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (HvdH.vsz (vs.getD 0 HvdH.Val.nil) + HvdH.vsz (vs.getD 1 HvdH.Val.nil) + 1))) :
    HvdH.WordR main p (fun vs => vs = a :: b :: r) (fun _ out => out = b :: a :: r) (fun _ => c) := by
  refine conseqC h (by simp) ?_ ?_
  · intro out hout
    obtain ⟨a', b', rest, hv, ho⟩ := hout
    obtain ⟨h1, h2⟩ := List.cons.inj hv
    obtain ⟨h3, h4⟩ := List.cons.inj h2
    rw [← h1, ← h3, ← h4] at ho
    exact ho
  · simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact hc

theorem dropWin {main p : HvdH.Cmd} {K c : ℕ} {a : HvdH.Val} {r : List HvdH.Val}
    (hc : K * (HvdH.vsz a + 1) ≤ c)
    (h : HvdH.WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1))) :
    HvdH.WordR main p (fun vs => vs = a :: r) (fun _ out => out = r) (fun _ => c) := by
  refine conseqC h (by simp) ?_ hc
  intro out hout
  obtain ⟨v, rest, hv, ho⟩ := hout
  obtain ⟨h1, h2⟩ := List.cons.inj hv
  rw [← h2] at ho
  exact ho

theorem pushWin {main p : HvdH.Cmd} {K c : ℕ} {v : HvdH.Val} {A : List HvdH.Val}
    (hc : K * (HvdH.vsz v + 1) ≤ c)
    (h : HvdH.WordR main p (fun _ => True) (fun vs out => out = v :: vs) (fun _ => K * (HvdH.vsz v + 1))) :
    HvdH.WordR main p (fun vs => vs = A) (fun _ out => out = v :: A) (fun _ => c) := by
  refine conseqC h trivial ?_ ?_
  · intro out hout; exact hout
  · exact hc

theorem ceqWin {main p : HvdH.Cmd} {K c : ℕ} {u w : ℤ} {r : List HvdH.Val}
    (hc : K * (HvdH.isz u + HvdH.isz w) ≤ c)
    (h : HvdH.WordR main p
      (fun vs => ∃ a b rest, vs = HvdH.Val.int a :: HvdH.Val.int b :: rest ∧ True)
      (fun vs out => ∃ a b rest, vs = HvdH.Val.int a :: HvdH.Val.int b :: rest ∧
        out = HvdH.Val.int (if a = b then 1 else 0) :: rest)
      (fun vs => binCost (fun a b => K * (HvdH.isz a + HvdH.isz b)) vs)) :
    HvdH.WordR main p (fun vs => vs = HvdH.Val.int u :: HvdH.Val.int w :: r)
      (fun _ out => out = HvdH.Val.int (if u = w then 1 else 0) :: r) (fun _ => c) := by
  refine conseqC h ⟨u, w, r, rfl, trivial⟩ ?_ hc
  intro out hout
  obtain ⟨a, b, rest, hv, ho⟩ := hout
  obtain ⟨h1, h2⟩ := List.cons.inj hv
  obtain ⟨h3, h4⟩ := List.cons.inj h2
  have e1 : u = a := HvdH.Val.int.inj h1
  have e2 : w = b := HvdH.Val.int.inj h3
  rw [← e1, ← e2, ← h4] at ho
  exact ho

theorem consWin {main p : HvdH.Cmd} {K c : ℕ} {a b : HvdH.Val} {r : List HvdH.Val} (hc : K ≤ c)
    (h : HvdH.WordR main p (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = HvdH.Val.cons a b :: rest) (fun _ => K)) :
    HvdH.WordR main p (fun vs => vs = a :: b :: r) (fun _ out => out = HvdH.Val.cons a b :: r)
      (fun _ => c) := by
  refine conseqC h (by simp) ?_ hc
  intro out hout
  obtain ⟨a', b', rest, hv, ho⟩ := hout
  obtain ⟨h1, h2⟩ := List.cons.inj hv
  obtain ⟨h3, h4⟩ := List.cons.inj h2
  rw [← h1, ← h3, ← h4] at ho
  exact ho

theorem max_le_add (a b : ℕ) : max a b ≤ a + b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega


theorem cntMulLe {K a b : ℕ} (h : a ≤ b) : K * a ≤ K * b := Nat.mul_le_mul_left K h

/-- Cost monotonicity for an arbitrary postcondition. -/
theorem monoC {main p : HvdH.Cmd} {P : List HvdH.Val → Prop} {Q : List HvdH.Val → List HvdH.Val → Prop}
    {c c' : ℕ} (h : HvdH.WordR main p P Q (fun _ => c)) (hc : c ≤ c') :
    HvdH.WordR main p P Q (fun _ => c') := by
  intro vs hvs s Rg hR
  obtain ⟨out, s1, n, hout, hev, hn, h0, hk⟩ := h vs hvs s Rg hR
  exact ⟨out, s1, n, hout, hev, le_trans hn hc, h0, hk⟩

theorem winEx {main : HvdH.Cmd} {p : HvdH.Cmd} {A B : List HvdH.Val} {c : ℕ} {X : List HvdH.Val}
    (h : HvdH.WordR main p (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    HvdH.WordR main p (fun vs => vs = A ++ X) (fun _ out => out = B ++ X) (fun _ => c) := by
  intro vs hvs s Rg hR
  obtain ⟨out, s1, n, hpost, hev, hn, h0, hk⟩ := h vs ⟨X, hvs⟩ s Rg hR
  obtain ⟨rest, hv, hout⟩ := hpost
  have hX : X = rest := (List.append_right_inj A).mp (by rw [← hvs]; exact hv)
  refine ⟨out, s1, n, ?_, hev, hn, h0, hk⟩
  rw [hout, ← hX]

/-! ## List identities -/

theorem cntFlatLen1 (qs : List (ℤ × ℤ)) :
    (∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1) → (∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1) →
    (((qs.map fun q => awRec q.1 q.2)).map awF1).flatten.length = awCnt1 qs := by
  intro h1 h2
  induction qs with
  | nil => simp [awCnt1]
  | cons q t ih =>
    rw [List.map_cons, List.map_cons, List.flatten_cons, List.length_append]
    rw [ih (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) (fun x hx => h2 x (List.mem_cons_of_mem _ hx))]
    rw [awF1_length_awRec (h1 q List.mem_cons_self) (h2 q List.mem_cons_self)]
    unfold awCnt1
    simp only [List.map_cons, List.sum_cons]

theorem cntFlatLen2 (qs : List (ℤ × ℤ)) :
    (∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1) → (∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1) →
    (((qs.map fun q => awRec q.1 q.2)).map awF2).flatten.length = awCnt2 qs := by
  intro h1 h2
  induction qs with
  | nil => simp [awCnt2]
  | cons q t ih =>
    rw [List.map_cons, List.map_cons, List.flatten_cons, List.length_append]
    rw [ih (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) (fun x hx => h2 x (List.mem_cons_of_mem _ hx))]
    rw [awF2_length_awRec (h1 q List.mem_cons_self) (h2 q List.mem_cons_self)]
    unfold awCnt2
    simp only [List.map_cons, List.sum_cons]

/-! ## The per-record bodies -/

theorem cntBody1 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (zr zi : ℤ) (rest : List HvdH.Val),
      (zr = 0 ∨ zr = 1) → (zi = 0 ∨ zi = 1) →
      HvdH.WordR main prog
        (fun vs => vs = awRec zr zi :: rest)
        (fun _ out => out = awSub1 (awRec zr zi) :: rest)
        (fun _ => K) := by
  obtain ⟨combNil, Kin, hIfNil⟩ := hk.ifNil
  obtain ⟨puncons, Ku, hUncons⟩ := hk.unconsV
  obtain ⟨pdup, Kd, hDup⟩ := hk.dup
  obtain ⟨pushP, Kp, hPush⟩ := hk.pushVal
  obtain ⟨peq, Ke, hEq⟩ := hi.eq
  obtain ⟨combZero, Kz, hIfZero⟩ := hk.ifZero
  obtain ⟨pdrop, Kdr, hDrop⟩ := hk.drop
  obtain ⟨pcons, Kc, hCons⟩ := hk.consV
  obtain ⟨pswap, Ks, hSwap⟩ := hk.swap
  let qOne : HvdH.Cmd := HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq pswap pdrop) (pushP HvdH.Val.nil)) pswap) pcons
  let qTwo : HvdH.Cmd := HvdH.Cmd.seq (HvdH.Cmd.seq pdrop pdrop) (pushP HvdH.Val.nil)
  let qIn : HvdH.Cmd := HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq puncons pdup) (pushP (HvdH.Val.int 1))) peq) (combZero qTwo qOne)
  refine ⟨combNil (pushP HvdH.Val.nil) qIn, Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))) + 4, ?_⟩
  intro main zr zi rest hzr hzi
  have hOne : ∀ (b : HvdH.Val) (r : List HvdH.Val), HvdH.vsz b ≤ 6 →
      HvdH.WordR main qOne (fun vs => vs = HvdH.Val.int 1 :: b :: r)
        (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: r)
        (fun _ => Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) := by
    intro b r hb
    have s1 := swapWin (h := hSwap main) (a := HvdH.Val.int 1) (b := b) (r := r) (c := Ks * 16)
      (cntMulLe (by rw [vsz_int_one]; omega))
    have s2 := dropWin (h := hDrop main) (a := b) (r := HvdH.Val.int 1 :: r) (c := Kdr * 8)
      (cntMulLe (by omega))
    have s3 := pushWin (h := hPush main HvdH.Val.nil) (A := HvdH.Val.int 1 :: r) (c := Kp * 4)
      (cntMulLe (by decide))
    have s4 := swapWin (h := hSwap main) (a := HvdH.Val.nil) (b := HvdH.Val.int 1) (r := r) (c := Ks * 16)
      (cntMulLe (by decide))
    have s5 := consWin (h := hCons main) (a := HvdH.Val.int 1) (b := HvdH.Val.nil) (r := r) (c := Kc) le_rfl
    have hs1 := seqC s1 s2
    have hs2 := seqC hs1 s3
    have hs3 := seqC hs2 s4
    have hs4 := seqC hs3 s5
    exact monoC hs4 (by omega)
  have hTwo : ∀ (b : HvdH.Val) (r : List HvdH.Val), HvdH.vsz b ≤ 6 →
      HvdH.WordR main qTwo (fun vs => vs = HvdH.Val.int 2 :: b :: r) (fun _ out => out = HvdH.Val.nil :: r)
        (fun _ => Kdr * 8 + Kdr * 8 + Kp * 4) := by
    intro b r hb
    have s1 := dropWin (h := hDrop main) (a := HvdH.Val.int 2) (r := b :: r) (c := Kdr * 8)
      (cntMulLe (by decide))
    have s2 := dropWin (h := hDrop main) (a := b) (r := r) (c := Kdr * 8) (cntMulLe (by omega))
    have s3 := pushWin (h := hPush main HvdH.Val.nil) (A := r) (c := Kp * 4) (cntMulLe (by decide))
    have hs1 := seqC s1 s2
    have hs2 := seqC hs1 s3
    exact hs2
  have hIn : ∀ (m : ℤ) (b : HvdH.Val) (r : List HvdH.Val), (m = 1 ∨ m = 2) → HvdH.vsz b ≤ 6 →
      HvdH.WordR main qIn (fun vs => vs = HvdH.Val.cons (HvdH.Val.int m) b :: r)
        (fun _ out => (m = 1 → out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: r) ∧
          (m ≠ 1 → out = HvdH.Val.nil :: r))
        (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) := by
    intro m b r hm hb
    have hvm : HvdH.vsz (HvdH.Val.int m) ≤ 4 := by
      rcases hm with h | h
      · subst h; decide +kernel
      · subst h; decide +kernel
    have him : HvdH.isz m ≤ 4 := by
      rcases hm with h | h
      · subst h; decide +kernel
      · subst h; decide +kernel
    have s1 := unconsWin (h := hUncons main) (a := HvdH.Val.int m) (b := b) (r := r) (c := Ku) le_rfl
    have s2 := dupWin (h := hDup main) (a := HvdH.Val.int m) (r := b :: r) (c := Kd * 8) (cntMulLe (by omega))
    have s3 := pushWin (h := hPush main (HvdH.Val.int 1)) (A := HvdH.Val.int m :: HvdH.Val.int m :: b :: r) (c := Kp * 4)
      (cntMulLe (by decide))
    have s4 := ceqWin (main := main) (p := peq) (h := hEq main) (K := Ke) (u := 1) (w := m)
      (r := HvdH.Val.int m :: b :: r) (c := Ke * 16) (cntMulLe (by rw [isz_one_z]; omega))
    have hz1 : (if (1 : ℤ) = m then (1 : ℤ) else 0) = 0 → m = 2 := by
      intro hz
      rcases hm with h | h
      · rw [h] at hz; norm_num at hz
      · exact h
    have hz2 : (if (1 : ℤ) = m then (1 : ℤ) else 0) ≠ 0 → m = 1 := by
      intro hz
      rcases hm with h | h
      · exact h
      · exfalso; rw [h] at hz; norm_num at hz
    have hq1 : (if (1 : ℤ) = m then (1 : ℤ) else 0) = 0 → HvdH.WordR main qTwo
        (fun vs => vs = HvdH.Val.int m :: b :: r) (fun _ out => out = HvdH.Val.nil :: r) (fun _ => Kdr * 8 + Kdr * 8 + Kp * 4) := by
      intro hz
      rw [hz1 hz]
      exact hTwo b r hb
    have hq2 : (if (1 : ℤ) = m then (1 : ℤ) else 0) ≠ 0 → HvdH.WordR main qOne
        (fun vs => vs = HvdH.Val.int m :: b :: r)
        (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: r) (fun _ => Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) := by
      intro hz
      rw [hz2 hz]
      exact hOne b r hb
    have hIZ := hIfZero main qTwo qOne (if (1 : ℤ) = m then (1 : ℤ) else 0) (HvdH.Val.int m :: b :: r)
      (fun out => out = HvdH.Val.nil :: r)
      (fun out => out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: r)
      (Kdr * 8 + Kdr * 8 + Kp * 4) (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) hq1 hq2
    have hcost : Kz * (HvdH.isz (if (1 : ℤ) = m then (1 : ℤ) else 0) + 1) + max (Kdr * 8 + Kdr * 8 + Kp * 4) (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc)
        ≤ Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4) := by
      have hz : HvdH.isz (if (1 : ℤ) = m then (1 : ℤ) else 0) ≤ 3 := by
        split <;> simp [isz_one_z, isz_two_z, isz_zero_z]
      have hk : Kz * (HvdH.isz (if (1 : ℤ) = m then (1 : ℤ) else 0) + 1) ≤ Kz * 4 :=
        cntMulLe (by omega)
      have hmx := max_le_add (Kdr * 8 + Kdr * 8 + Kp * 4) (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc)
      omega
    have hstep : HvdH.WordR main (combZero qTwo qOne) (fun vs => vs = HvdH.Val.int (if (1 : ℤ) = m then (1 : ℤ) else 0) :: HvdH.Val.int m :: b :: r)
        (fun _ out => (m = 1 → out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: r) ∧
          (m ≠ 1 → out = HvdH.Val.nil :: r))
        (fun _ => Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)) := by
      refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hout
        refine ⟨?_, ?_⟩
        · intro hm1
          have hz : (if (1 : ℤ) = m then (1 : ℤ) else 0) ≠ 0 := by rw [hm1]; norm_num
          exact hout.2 hz
        · intro hm1
          have hz : (if (1 : ℤ) = m then (1 : ℤ) else 0) = 0 := by
            rcases hm with h | h
            · rw [h] at hm1; exact absurd rfl hm1
            · rw [h]; norm_num
          exact hout.1 hz
      · intro vs hvs; exact hcost
    have hs1 := seqC s1 s2
    have hs2 := seqC hs1 s3
    have hs3 := seqC hs2 s4
    have hs4 := seqC2 hs3 hstep
    exact monoC hs4 (by omega)
  rcases hzr with hzr | hzr <;> rcases hzi with hzi | hzi
  · subst hzr; subst hzi
    rw [awSub1_00, awRec_00]
    have hq1 : (HvdH.Val.nil = HvdH.Val.nil) → HvdH.WordR main (pushP HvdH.Val.nil) (fun vs => vs = rest)
        (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) := fun _ => by
      refine conseqC (hPush main HvdH.Val.nil) trivial (fun _ h => h) ?_
      exact cntMulLe (by decide)
    have hq2 : (HvdH.Val.nil ≠ HvdH.Val.nil) → HvdH.WordR main qIn (fun vs => vs = HvdH.Val.nil :: rest)
        (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) := fun h => absurd rfl h
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn HvdH.Val.nil rest
      (fun out => out = HvdH.Val.nil :: rest) (fun out => out = HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.1 rfl
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))) + 4
      omega
  · subst hzr; subst hzi
    rw [awSub1_01, awRec_01]
    have hq1 : (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil = HvdH.Val.nil) → HvdH.WordR main (pushP HvdH.Val.nil)
        (fun vs => vs = rest) (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) :=
      fun h => absurd h (by decide)
    have hq2 : (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil ≠ HvdH.Val.nil) →
        HvdH.WordR main qIn (fun vs => vs = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: rest)
          (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) := by
      intro _
      have hb : HvdH.vsz HvdH.Val.nil ≤ 6 := by decide
      refine Work.Kernel.WordR_conseq (hIn 2 HvdH.Val.nil rest (Or.inr rfl) hb) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost; exact hpost.2 (by norm_num)
      · intro vs hvs; exact le_rfl
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) rest
      (fun out => out = HvdH.Val.nil :: rest) (fun out => out = HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.2 (by decide)
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))) + 4
      omega
  · subst hzr; subst hzi
    rw [awSub1_10, awRec_10]
    have hq1 : (HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil = HvdH.Val.nil) → HvdH.WordR main (pushP HvdH.Val.nil)
        (fun vs => vs = rest) (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) :=
      fun h => absurd h (by decide)
    have hq2 : (HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil ≠ HvdH.Val.nil) →
        HvdH.WordR main qIn (fun vs => vs = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: rest)
          (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) := by
      intro _
      have hb : HvdH.vsz HvdH.Val.nil ≤ 6 := by decide
      refine Work.Kernel.WordR_conseq (hIn 1 HvdH.Val.nil rest (Or.inl rfl) hb) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost; exact hpost.1 rfl
      · intro vs hvs; exact le_rfl
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn (HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil) rest
      (fun out => out = HvdH.Val.nil :: rest)
      (fun out => out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.2 (by decide)
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))) + 4
      omega
  · subst hzr; subst hzi
    rw [awSub1_11, awRec_11]
    have hq1 : (HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) = HvdH.Val.nil) →
        HvdH.WordR main (pushP HvdH.Val.nil) (fun vs => vs = rest)
          (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) :=
      fun h => absurd h (by decide)
    have hq2 : (HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) ≠ HvdH.Val.nil) →
        HvdH.WordR main qIn
          (fun vs => vs = HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) :: rest)
          (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) := by
      intro _
      have hb : HvdH.vsz (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) ≤ 6 := by rw [vsz_cons_two_nil]
      refine Work.Kernel.WordR_conseq (hIn 1 (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) rest (Or.inl rfl) hb) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost; exact hpost.1 rfl
      · intro vs hvs; exact le_rfl
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn
      (HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil)) rest
      (fun out => out = HvdH.Val.nil :: rest)
      (fun out => out = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.2 (by decide)
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Ks * 16 + Kdr * 8 + Kp * 4 + Ks * 16 + Kc) + (Kdr * 8 + Kdr * 8 + Kp * 4)))) + 4
      omega

theorem cntBody2 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (zr zi : ℤ) (rest : List HvdH.Val),
      (zr = 0 ∨ zr = 1) → (zi = 0 ∨ zi = 1) →
      HvdH.WordR main prog
        (fun vs => vs = awRec zr zi :: rest)
        (fun _ out => out = awSub2 (awRec zr zi) :: rest)
        (fun _ => K) := by
  obtain ⟨combNil, Kin, hIfNil⟩ := hk.ifNil
  obtain ⟨puncons, Ku, hUncons⟩ := hk.unconsV
  obtain ⟨pdup, Kd, hDup⟩ := hk.dup
  obtain ⟨pushP, Kp, hPush⟩ := hk.pushVal
  obtain ⟨peq, Ke, hEq⟩ := hi.eq
  obtain ⟨combZero, Kz, hIfZero⟩ := hk.ifZero
  obtain ⟨pdrop, Kdr, hDrop⟩ := hk.drop
  obtain ⟨pcons, Kc, hCons⟩ := hk.consV
  obtain ⟨pswap, Ks, hSwap⟩ := hk.swap
  let qOne : HvdH.Cmd := HvdH.Cmd.seq pdrop (combNil (pushP HvdH.Val.nil) HvdH.Cmd.skip)
  let qTwo : HvdH.Cmd := HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq pswap pdrop) (pushP HvdH.Val.nil)) pswap) pcons
  let qIn : HvdH.Cmd := HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq puncons pdup) (pushP (HvdH.Val.int 1))) peq) (combZero qTwo qOne)
  refine ⟨combNil (pushP HvdH.Val.nil) qIn, Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))) + 4, ?_⟩
  intro main zr zi rest hzr hzi
  have hOne : ∀ (b : HvdH.Val) (r : List HvdH.Val), HvdH.vsz b ≤ 6 →
      HvdH.WordR main qOne (fun vs => vs = HvdH.Val.int 1 :: b :: r)
        (fun _ out => (b = HvdH.Val.nil → out = HvdH.Val.nil :: r) ∧ (b ≠ HvdH.Val.nil → out = b :: r))
        (fun _ => Kdr * 8 + (Kin + (Kp * 2 + 1))) := by
    intro b r hb
    have s1 := dropWin (h := hDrop main) (a := HvdH.Val.int 1) (r := b :: r) (c := Kdr * 8)
      (cntMulLe (by decide))
    have hn : (b = HvdH.Val.nil) → HvdH.WordR main (pushP HvdH.Val.nil) (fun vs => vs = r)
        (fun _ out => out = HvdH.Val.nil :: r) (fun _ => Kp * 2) := fun _ => by
      refine conseqC (hPush main HvdH.Val.nil) trivial (fun _ h => h) ?_
      exact cntMulLe (by decide)
    have hy : (b ≠ HvdH.Val.nil) → HvdH.WordR main HvdH.Cmd.skip (fun vs => vs = b :: r)
        (fun _ out => out = b :: r) (fun _ => 1) := by
      intro _
      refine conseqC (hk.skip main) trivial (fun _ h => h) le_rfl
    have hIZ := hIfNil main (pushP HvdH.Val.nil) HvdH.Cmd.skip b r
      (fun out => out = HvdH.Val.nil :: r) (fun out => out = b :: r) (Kp * 2) 1 hn hy
    have hIZ' : HvdH.WordR main (combNil (pushP HvdH.Val.nil) HvdH.Cmd.skip) (fun vs => vs = b :: r)
        (fun _ out => (b = HvdH.Val.nil → out = HvdH.Val.nil :: r) ∧ (b ≠ HvdH.Val.nil → out = b :: r))
        (fun _ => Kin + (Kp * 2 + 1)) := by
      refine monoC hIZ ?_
      have hmx := max_le_add (Kp * 2) 1
      omega
    have hs := seqC2 s1 hIZ'
    exact monoC hs (by omega)
  have hTwo : ∀ (b : HvdH.Val) (r : List HvdH.Val), HvdH.vsz b ≤ 6 →
      HvdH.WordR main qTwo (fun vs => vs = HvdH.Val.int 2 :: b :: r)
        (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: r) (fun _ => Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc) := by
    intro b r hb
    have s1 := swapWin (h := hSwap main) (a := HvdH.Val.int 2) (b := b) (r := r) (c := Ks * 20)
      (cntMulLe (by rw [vsz_int_two]; omega))
    have s2 := dropWin (h := hDrop main) (a := b) (r := HvdH.Val.int 2 :: r) (c := Kdr * 8)
      (cntMulLe (by omega))
    have s3 := pushWin (h := hPush main HvdH.Val.nil) (A := HvdH.Val.int 2 :: r) (c := Kp * 4)
      (cntMulLe (by decide))
    have s4 := swapWin (h := hSwap main) (a := HvdH.Val.nil) (b := HvdH.Val.int 2) (r := r) (c := Ks * 20)
      (cntMulLe (by decide))
    have s5 := consWin (h := hCons main) (a := HvdH.Val.int 2) (b := HvdH.Val.nil) (r := r) (c := Kc) le_rfl
    have hs1 := seqC s1 s2
    have hs2 := seqC hs1 s3
    have hs3 := seqC hs2 s4
    have hs4 := seqC hs3 s5
    exact monoC hs4 (by omega)
  have hIn : ∀ (m : ℤ) (b : HvdH.Val) (r : List HvdH.Val), (m = 1 ∨ m = 2) → HvdH.vsz b ≤ 6 →
      HvdH.WordR main qIn (fun vs => vs = HvdH.Val.cons (HvdH.Val.int m) b :: r)
        (fun _ out => (m = 1 → (b = HvdH.Val.nil → out = HvdH.Val.nil :: r) ∧ (b ≠ HvdH.Val.nil → out = b :: r)) ∧
          (m ≠ 1 → out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: r))
        (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) := by
    intro m b r hm hb
    have hvm : HvdH.vsz (HvdH.Val.int m) ≤ 4 := by
      rcases hm with h | h
      · subst h; decide +kernel
      · subst h; decide +kernel
    have him : HvdH.isz m ≤ 4 := by
      rcases hm with h | h
      · subst h; decide +kernel
      · subst h; decide +kernel
    have s1 := unconsWin (h := hUncons main) (a := HvdH.Val.int m) (b := b) (r := r) (c := Ku) le_rfl
    have s2 := dupWin (h := hDup main) (a := HvdH.Val.int m) (r := b :: r) (c := Kd * 8) (cntMulLe (by omega))
    have s3 := pushWin (h := hPush main (HvdH.Val.int 1)) (A := HvdH.Val.int m :: HvdH.Val.int m :: b :: r) (c := Kp * 4)
      (cntMulLe (by decide))
    have s4 := ceqWin (main := main) (p := peq) (h := hEq main) (K := Ke) (u := 1) (w := m)
      (r := HvdH.Val.int m :: b :: r) (c := Ke * 16) (cntMulLe (by rw [isz_one_z]; omega))
    have hz1 : (if (1 : ℤ) = m then (1 : ℤ) else 0) = 0 → m = 2 := by
      intro hz
      rcases hm with h | h
      · rw [h] at hz; norm_num at hz
      · exact h
    have hz2 : (if (1 : ℤ) = m then (1 : ℤ) else 0) ≠ 0 → m = 1 := by
      intro hz
      rcases hm with h | h
      · exact h
      · exfalso; rw [h] at hz; norm_num at hz
    have hq1 : (if (1 : ℤ) = m then (1 : ℤ) else 0) = 0 → HvdH.WordR main qTwo
        (fun vs => vs = HvdH.Val.int m :: b :: r)
        (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: r) (fun _ => Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc) := by
      intro hz
      rw [hz1 hz]
      exact hTwo b r hb
    have hq2 : (if (1 : ℤ) = m then (1 : ℤ) else 0) ≠ 0 → HvdH.WordR main qOne
        (fun vs => vs = HvdH.Val.int m :: b :: r)
        (fun _ out => (b = HvdH.Val.nil → out = HvdH.Val.nil :: r) ∧ (b ≠ HvdH.Val.nil → out = b :: r))
        (fun _ => Kdr * 8 + (Kin + (Kp * 2 + 1))) := by
      intro hz
      rw [hz2 hz]
      exact hOne b r hb
    have hIZ := hIfZero main qTwo qOne (if (1 : ℤ) = m then (1 : ℤ) else 0) (HvdH.Val.int m :: b :: r)
      (fun out => out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: r)
      (fun out => (b = HvdH.Val.nil → out = HvdH.Val.nil :: r) ∧ (b ≠ HvdH.Val.nil → out = b :: r))
      (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc) (Kdr * 8 + (Kin + (Kp * 2 + 1))) hq1 hq2
    have hcost : Kz * (HvdH.isz (if (1 : ℤ) = m then (1 : ℤ) else 0) + 1) + max (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc) (Kdr * 8 + (Kin + (Kp * 2 + 1)))
        ≤ Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc) := by
      have hz : HvdH.isz (if (1 : ℤ) = m then (1 : ℤ) else 0) ≤ 3 := by
        split <;> simp [isz_one_z, isz_two_z, isz_zero_z]
      have hk : Kz * (HvdH.isz (if (1 : ℤ) = m then (1 : ℤ) else 0) + 1) ≤ Kz * 4 :=
        cntMulLe (by omega)
      have hmx := max_le_add (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc) (Kdr * 8 + (Kin + (Kp * 2 + 1)))
      omega
    have hstep : HvdH.WordR main (combZero qTwo qOne)
        (fun vs => vs = HvdH.Val.int (if (1 : ℤ) = m then (1 : ℤ) else 0) :: HvdH.Val.int m :: b :: r)
        (fun _ out => (m = 1 → (b = HvdH.Val.nil → out = HvdH.Val.nil :: r) ∧ (b ≠ HvdH.Val.nil → out = b :: r)) ∧
          (m ≠ 1 → out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: r))
        (fun _ => Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)) := by
      refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hout
        refine ⟨?_, ?_⟩
        · intro hm1
          have hz : (if (1 : ℤ) = m then (1 : ℤ) else 0) ≠ 0 := by rw [hm1]; norm_num
          exact hout.2 hz
        · intro hm1
          have hz : (if (1 : ℤ) = m then (1 : ℤ) else 0) = 0 := by
            rcases hm with h | h
            · rw [h] at hm1; exact absurd rfl hm1
            · rw [h]; norm_num
          exact hout.1 hz
      · intro vs hvs; exact hcost
    have hs1 := seqC s1 s2
    have hs2 := seqC hs1 s3
    have hs3 := seqC hs2 s4
    have hs4 := seqC2 hs3 hstep
    exact monoC hs4 (by omega)
  rcases hzr with hzr | hzr <;> rcases hzi with hzi | hzi
  · subst hzr; subst hzi
    rw [awSub2_00, awRec_00]
    have hq1 : (HvdH.Val.nil = HvdH.Val.nil) → HvdH.WordR main (pushP HvdH.Val.nil) (fun vs => vs = rest)
        (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) := fun _ => by
      refine conseqC (hPush main HvdH.Val.nil) trivial (fun _ h => h) ?_
      exact cntMulLe (by decide)
    have hq2 : (HvdH.Val.nil ≠ HvdH.Val.nil) → HvdH.WordR main qIn (fun vs => vs = HvdH.Val.nil :: rest)
        (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) := fun h => absurd rfl h
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn HvdH.Val.nil rest
      (fun out => out = HvdH.Val.nil :: rest) (fun out => out = HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.1 rfl
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))) + 4
      omega
  · subst hzr; subst hzi
    rw [awSub2_01, awRec_01]
    have hq1 : (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil = HvdH.Val.nil) → HvdH.WordR main (pushP HvdH.Val.nil)
        (fun vs => vs = rest) (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) :=
      fun h => absurd h (by decide)
    have hq2 : (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil ≠ HvdH.Val.nil) →
        HvdH.WordR main qIn (fun vs => vs = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: rest)
          (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) := by
      intro _
      have hb : HvdH.vsz HvdH.Val.nil ≤ 6 := by decide
      refine Work.Kernel.WordR_conseq (hIn 2 HvdH.Val.nil rest (Or.inr rfl) hb) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost; exact hpost.2 (by norm_num)
      · intro vs hvs; exact le_rfl
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) rest
      (fun out => out = HvdH.Val.nil :: rest)
      (fun out => out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.2 (by decide)
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))) + 4
      omega
  · subst hzr; subst hzi
    rw [awSub2_10, awRec_10]
    have hq1 : (HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil = HvdH.Val.nil) → HvdH.WordR main (pushP HvdH.Val.nil)
        (fun vs => vs = rest) (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) :=
      fun h => absurd h (by decide)
    have hq2 : (HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil ≠ HvdH.Val.nil) →
        HvdH.WordR main qIn (fun vs => vs = HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil :: rest)
          (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) := by
      intro _
      have hb : HvdH.vsz HvdH.Val.nil ≤ 6 := by decide
      refine Work.Kernel.WordR_conseq (hIn 1 HvdH.Val.nil rest (Or.inl rfl) hb) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        exact (hpost.1 rfl).1 rfl
      · intro vs hvs; exact le_rfl
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn (HvdH.Val.cons (HvdH.Val.int 1) HvdH.Val.nil) rest
      (fun out => out = HvdH.Val.nil :: rest) (fun out => out = HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.2 (by decide)
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))) + 4
      omega
  · subst hzr; subst hzi
    rw [awSub2_11, awRec_11]
    have hq1 : (HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) = HvdH.Val.nil) →
        HvdH.WordR main (pushP HvdH.Val.nil) (fun vs => vs = rest)
          (fun _ out => out = HvdH.Val.nil :: rest) (fun _ => Kp * 2) :=
      fun h => absurd h (by decide)
    have hq2 : (HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) ≠ HvdH.Val.nil) →
        HvdH.WordR main qIn
          (fun vs => vs = HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) :: rest)
          (fun _ out => out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: rest) (fun _ => Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) := by
      intro _
      have hb : HvdH.vsz (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) ≤ 6 := by rw [vsz_cons_two_nil]
      refine Work.Kernel.WordR_conseq (hIn 1 (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil) rest (Or.inl rfl) hb) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        exact (hpost.1 rfl).2 (by decide)
      · intro vs hvs; exact le_rfl
    have hIZ := hIfNil main (pushP HvdH.Val.nil) qIn
      (HvdH.Val.cons (HvdH.Val.int 1) (HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil)) rest
      (fun out => out = HvdH.Val.nil :: rest)
      (fun out => out = HvdH.Val.cons (HvdH.Val.int 2) HvdH.Val.nil :: rest) (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) hq1 hq2
    refine Work.Kernel.WordR_conseq hIZ ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; exact hpost.2 (by decide)
    · intro vs hvs
      have hmx := max_le_add (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))
      show Kin + max (Kp * 2) (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc))) ≤ Kin + (Kp * 2 + (Ku + Kd * 8 + Kp * 4 + Ke * 16 + (Kz * 4 + (Kdr * 8 + (Kin + (Kp * 2 + 1))) + (Ks * 20 + Kdr * 8 + Kp * 4 + Ks * 20 + Kc)))) + 4
      omega

