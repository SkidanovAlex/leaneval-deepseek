import Mathlib
import Submission.Work.Resample.auCWDefs
import Submission.Work.Fx.FxCommon

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## 1.  Size helpers -/

theorem cw_szl_ofList (l : List Val) : vsz (ofList l) = szl l + (l.length + 1) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      show vsz (Val.cons x (ofList t)) = szl (x :: t) + ((x :: t).length + 1)
      rw [vsz_cons, szl_cons, ih]
      simp only [List.length_cons]
      ring

theorem cw_szl_replicate (c : ℕ) (v : Val) : szl (List.replicate c v) = c * vsz v := by
  induction c with
  | zero => simp [szl]
  | succ k ih => rw [List.replicate_succ, szl_cons, ih]; ring

theorem cw_isz_one : isz (1 : ℤ) = 3 := by decide +kernel

theorem cw_vsz_int1 : vsz (Val.int 1) = 3 := by rw [vsz_int, cw_isz_one]

theorem cw_vsz_chain (c : ℕ) : vsz (ofList (List.replicate c (Val.int 1))) = 4 * c + 1 := by
  rw [cw_szl_ofList, cw_szl_replicate, cw_vsz_int1, List.length_replicate]
  ring

theorem cw_szl_le_len_mul {l : List Val} {n : ℕ} (h : ∀ v ∈ l, vsz v ≤ n) :
    szl l ≤ l.length * n := by
  induction l with
  | nil => simp [szl]
  | cons a t ih =>
      have ha : vsz a ≤ n := h a (by simp)
      have ht : ∀ v ∈ t, vsz v ≤ n := fun v hv => h v (by simp [hv])
      rw [szl_cons, List.length_cons]
      have := ih ht
      nlinarith [Nat.zero_le (vsz a), Nat.zero_le (szl t)]

theorem cw_vsz_ofList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ (B + 1) * l.length + 1 := by
  rw [cw_szl_ofList]
  have := cw_szl_le_len_mul h
  nlinarith [Nat.zero_le l.length]

/-! ## 2.  The four values `awRec zr zi` for `zr, zi ∈ {0,1}` -/

theorem cw_awRec_00 : awRec 0 0 = (Val.nil : Val) := by decide +kernel

theorem cw_awRec_10 : awRec 1 0 = Val.cons (Val.int 1) Val.nil := by decide +kernel

theorem cw_awRec_01 : awRec 0 1 = Val.cons (Val.int 2) Val.nil := by decide +kernel

theorem cw_awRec_11 : awRec 1 1 = Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil) := by
  decide +kernel

theorem cw_awRec_ne_nil_10 : awRec 1 0 ≠ (Val.nil : Val) := by decide +kernel

theorem cw_awRec_ne_nil_01 : awRec 0 1 ≠ (Val.nil : Val) := by decide +kernel

theorem cw_awRec_ne_nil_11 : awRec 1 1 ≠ (Val.nil : Val) := by decide +kernel

theorem cw_awRec_vsz_le (zr zi : ℤ) (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    vsz (awRec zr zi) ≤ 10 := by
  rcases hzr with h | h <;> rcases hzi with h' | h' <;> rw [h, h'] <;> decide +kernel

theorem cw_awRec_nil_iff (zr zi : ℤ) (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    awRec zr zi = Val.nil ↔ zr = 0 ∧ zi = 0 := by
  rcases hzr with h | h <;> rcases hzi with h' | h' <;> rw [h, h'] <;>
    simp [cw_awRec_00, cw_awRec_ne_nil_10, cw_awRec_ne_nil_01, cw_awRec_ne_nil_11]

/-- The three cons-shaped records, with the marker data. -/
theorem cw_awRec_cons_cases (zr zi : ℤ) (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1)
    (hne : awRec zr zi ≠ Val.nil) :
    (zr = 1 ∧ zi = 0 ∧ awRec zr zi = Val.cons (Val.int 1) Val.nil) ∨
    (zr = 0 ∧ zi = 1 ∧ awRec zr zi = Val.cons (Val.int 2) Val.nil) ∨
    (zr = 1 ∧ zi = 1 ∧ awRec zr zi = Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil)) := by
  rcases hzr with h | h <;> rcases hzi with h' | h' <;>
    · subst h; subst h'
      first
      | exact absurd cw_awRec_00 hne
      | exact Or.inl ⟨rfl, rfl, cw_awRec_10⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl, cw_awRec_01⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl, cw_awRec_11⟩)

/-! ## 3.  Arithmetic facts for the unary chain -/

theorem cw_list_range_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem cw_geom_two (c : ℕ) : ∑ j ∈ Finset.range c, 2 ^ j = 2 ^ c - 1 := by
  induction c with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

theorem cw_evalChunks_replicate (c : ℕ) : evalChunks (List.replicate c 1) 1 = 2 ^ c - 1 := by
  unfold evalChunks
  rw [List.length_replicate, cw_list_range_sum]
  rw [Finset.sum_congr rfl (fun j hj => ?_), cw_geom_two]
  rw [Finset.mem_range] at hj
  rw [List.getD_eq_getElem _ _ (by simpa [List.length_replicate] using hj)]
  simp

theorem cw_clog_two_pow (c : ℕ) : Nat.clog 2 (2 ^ c) = c := by
  refine le_antisymm ?_ ?_
  · rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  · by_contra h
    rw [not_le] at h
    have h2 : 2 ^ c ≤ 2 ^ Nat.clog 2 (2 ^ c) :=
      (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mp le_rfl
    have h3 : 2 ^ Nat.clog 2 (2 ^ c) < 2 ^ c := Nat.pow_lt_pow_right (by norm_num) h
    omega

theorem cw_intList_replicate (c : ℕ) :
    intList (List.replicate c 1) = ofList (List.replicate c (Val.int 1)) := by
  induction c with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ]
      show Val.cons (Val.int 1) (intList (List.replicate k 1)) =
        Val.cons (Val.int 1) (ofList (List.replicate k (Val.int 1)))
      rw [ih]

theorem cw_chain_succ (n : ℕ) :
    ofList (List.replicate (n + 1) (Val.int 1)) =
      Val.cons (Val.int 1) (ofList (List.replicate n (Val.int 1))) := by
  rw [List.replicate_succ]
  rfl

theorem cw_isz_two_pow_sub_one (c : ℕ) : isz ((2 : ℤ) ^ c - 1) ≤ c + 2 := by
  have hcast : (((2 ^ c - 1 : ℕ)) : ℤ) = (2 : ℤ) ^ c - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow (n := c)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [isz, ← hcast, Int.natAbs_natCast]
  have h1 : (2 ^ c - 1).size ≤ c := by
    rw [Nat.size_le]
    have h2 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    omega
  omega

theorem cw_isz_natCast_le (n : ℕ) : isz ((n : ℤ)) ≤ n + 2 := by
  rw [isz, Int.natAbs_natCast]
  have h : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

/-! ## 4.  Window words `PW` and adapters for `KernelLib` / `IntLib` -/

/-- `PW main prog A B c`: for every value stack `vs = A ++ rest`, `prog` turns it into `B ++ rest`
with cost `≤ c` (a `WordR` for a fixed window `A`, everything below untouched). -/
def PW (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val,
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c)

theorem PW.comp {main p q : Cmd} {A B D : List Val} {c d : ℕ} (h1 : PW main p A B c)
    (h2 : PW main q B D d) : PW main (.seq p q) A D (c + d) := by
  intro rest vs hvs s R hR
  obtain ⟨mid, s', n₁, hmid, hev₁, hn₁, hstk₁, hoth₁⟩ := h1 rest vs hvs s R hR
  obtain ⟨out, s'', n₂, hout, hev₂, hn₂, hstk₂, hoth₂⟩ := h2 rest mid hmid s' R hstk₁
  exact ⟨out, s'', n₁ + n₂, hout, Eval.seq hev₁ hev₂, Nat.add_le_add hn₁ hn₂, hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

theorem PW.le {main prog : Cmd} {A B : List Val} {c c' : ℕ} (h : PW main prog A B c)
    (hc : c ≤ c') : PW main prog A B c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, le_trans hn hc, hstk, hoth⟩

theorem PW.appendTail {main prog : Cmd} {A B : List Val} {c : ℕ} (T : List Val)
    (h : PW main prog A B c) : PW main prog (A ++ T) (B ++ T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    h (T ++ rest) vs (by rw [hvs, List.append_assoc]) s R hR
  exact ⟨out, s', n, by rw [hout, List.append_assoc], hev, hn, hstk, hoth⟩

theorem PW.drop {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (a : Val) :
    PW main prog [a] [] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv]; simp) s R hR
  have h1 : v = a := (List.cons.inj (hvs'.symm.trans hv)).1
  have h2 : rest' = rest := (List.cons.inj (hvs'.symm.trans hv)).2
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv] at hn
    simpa using hn
  exact ⟨out, s', n, by rw [hout, h2]; rfl, hev, hn', hstk, hoth⟩

theorem PW.dup {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (a : Val) :
    PW main prog [a] [a, a] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv]; simp) s R hR
  have h1 : v = a := (List.cons.inj (hvs'.symm.trans hv)).1
  have h2 : rest' = rest := (List.cons.inj (hvs'.symm.trans hv)).2
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv] at hn
    simpa using hn
  exact ⟨out, s', n, by rw [hout, h1, h2]; rfl, hev, hn', hstk, hoth⟩

theorem PW.swap {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))) (a b : Val) :
    PW main prog [a, b] [b, a] (K * (vsz a + vsz b + 1)) := by
  intro rest vs hvs s R hR
  have hv : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv)
  have hn' : n ≤ K * (vsz a + vsz b + 1) := by
    rw [hv] at hn
    simpa only [List.getD_cons_zero, List.getD_cons_succ] using hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem PW.pushOnAny {main prog : Cmd} {v : Val} {c : ℕ} {A : List Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => c)) :
    PW main prog A (v :: A) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hvs]; rfl, hev, hn, hstk, hoth⟩

theorem PW.pushVal {main : Cmd} {progV : Val → Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (v : Val), WordR m (progV v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) (v : Val) :
    PW main (progV v) [] [v] (K * (vsz v + 1)) := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main v vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hvs]; rfl, hev, hn, hstk, hoth⟩

theorem PW.consV {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = Val.cons a b :: rest)
      (fun _ => K)) (a b : Val) : PW main prog [a, b] [Val.cons a b] K := by
  intro rest vs hvs s R hR
  have hv : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

theorem PW.unconsV {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = Val.cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = Val.cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => K)) (a b : Val) : PW main prog [Val.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv : vs = Val.cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv⟩ s R hR
  have hhead : Val.cons a' b' = Val.cons a b := (List.cons.inj (hvs'.symm.trans hv)).1
  have hrest : rest' = rest := (List.cons.inj (hvs'.symm.trans hv)).2
  obtain ⟨h1, h2⟩ := Val.cons.inj hhead
  exact ⟨out, s', n, by rw [hout, h1, h2, hrest]; rfl, hev, hn, hstk, hoth⟩

theorem PW.binOp {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) :
    PW main prog [Val.int a, Val.int b] [Val.int (f a b)] (C a b) := by
  intro rest vs hvs s R hR
  have hv : vs = Val.int a :: Val.int b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, b, rest, hv, hab⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := int_cons_inj3 (hvs'.symm.trans hv)
  have hn' : n ≤ C a b := by
    rw [hv] at hn
    simpa [binCost] using hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem PW.unOp {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} (ha : P a) :
    PW main prog [Val.int a] [Val.int (f a)] (C a) := by
  intro rest vs hvs s R hR
  have hv : vs = Val.int a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, rest, hv, ha⟩ s R hR
  have h1 : a' = a := Val.int.inj (List.cons.inj (hvs'.symm.trans hv)).1
  have h2 : rest' = rest := (List.cons.inj (hvs'.symm.trans hv)).2
  have hn' : n ≤ C a := by
    rw [hv] at hn
    simpa [unCost] using hn
  exact ⟨out, s', n, by rw [hout, h1, h2]; rfl, hev, hn', hstk, hoth⟩

theorem PW.roll {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    PW main (prog k) A (A.getD k .nil :: A.eraseIdx k)
      (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have hh : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega : k + 1 ≤ A.length)] at hh
    simpa [szl] using hh
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, eraseIdx_append_of_lt hk]
  rfl

/-! ## 5.  Generic `WordR` consequence and sequencing -/

theorem cw_conseq {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (h1 : ∀ vs, P' vs → P vs)
    (h2 : ∀ vs out, P' vs → Q vs out → Q' vs out) (h3 : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hp s R hR
  obtain ⟨out, s', n, hQ, hev, hn, hstk, hoth⟩ := h vs (h1 vs hp) s R hR
  exact ⟨out, s', n, h2 vs out hp hQ, hev, le_trans hn (h3 vs hp), hstk, hoth⟩

theorem cw_seq {main p q : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {P' : List Val → Prop} {Q' : List Val → List Val → Prop}
    {C' B : List Val → ℕ} (hp : WordR main p P Q C) (hq : WordR main q P' Q' C')
    (hmid : ∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ B vs) :
    WordR main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out) (fun vs => C vs + B vs) := by
  intro vs hP s R hR
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, hstk₁, hoth₁⟩ := hp vs hP s R hR
  obtain ⟨hP', hC'm⟩ := hmid vs mid hP hQ
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, hstk₂, hoth₂⟩ := hq mid hP' s₂ R hstk₁
  exact ⟨out, s₃, n₁ + n₂, ⟨mid, hQ, hQ'⟩, Eval.seq he₁ he₂,
    Nat.add_le_add hn₁ (le_trans hn₂ hC'm), hstk₂, fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

/-- Weakening for a chain of `PW` steps with a fixed tail. -/
theorem cw_pwWordR {main p : Cmd} {A B : List Val} {c : ℕ} (h : PW main p A B c)
    (rest : List Val) :
    WordR main p (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c) := h rest

/-! ## 6.  The increment words -/

theorem auCWIncOne (hk : KernelLib) (hi : IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (rest : List Val) (C : Val) (zr zi : ℤ),
      (zr = 0 ∨ zr = 1) → (zi = 0 ∨ zi = 1) →
      WordR main prog
        (fun vs => vs = awRec zr zi :: C :: rest)
        (fun _ out => out = (if zr = 1 then Val.cons (Val.int 1) C else C) :: rest)
        (fun _ => K) := by
  obtain ⟨ifNilP, Knil, hifNil⟩ := hk.ifNil
  obtain ⟨ifZeroP, Kz, hifZero⟩ := hk.ifZero
  obtain ⟨unconsP, Ku, huncons⟩ := hk.unconsV
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  obtain ⟨consP, Kc, hcons⟩ := hk.consV
  obtain ⟨pushP, Kp, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Ks, hswap⟩ := hk.swap
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  let qinc : Cmd := .seq dropP (.seq dropP (.seq (pushP (.int 1)) consP))
  let qno : Cmd := .seq dropP dropP
  let qchk : Cmd := .seq (.seq dupP (.seq (pushP (.int 1)) (.seq swapP subP))) (ifZeroP qinc qno)
  let qcons : Cmd := .seq unconsP qchk
  refine ⟨ifNilP Cmd.skip qcons,
    Knil + (1 + (Ku + ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
      (4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr))))), ?_⟩
  intro main rest C zr zi hzr hzi
  have hqinc : ∀ (a : ℤ) (b C : Val) (rest : List Val), isz a ≤ 4 → vsz b ≤ 6 →
      WordR main qinc (fun vs => vs = Val.int a :: b :: C :: rest)
        (fun _ out => out = Val.cons (Val.int 1) C :: rest) (fun _ => 12 * Kdr + 4 * Kp + Kc) := by
    intro a b C rest ha hb
    have h1 : PW main dropP [Val.int a, b, C] [b, C] (5 * Kdr) := by
      have h0 : PW main dropP [Val.int a, b, C] [b, C] (Kdr * (vsz (Val.int a) + 1)) := by
        simpa using PW.appendTail [b, C] (PW.drop hdrop (Val.int a))
      refine PW.le h0 ?_
      rw [vsz_int]
      calc Kdr * (isz a + 1) ≤ Kdr * 5 := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kdr := by ring
    have h2 : PW main dropP [b, C] [C] (7 * Kdr) := by
      have h0 : PW main dropP [b, C] [C] (Kdr * (vsz b + 1)) := by
        simpa using PW.appendTail [C] (PW.drop hdrop b)
      refine PW.le h0 ?_
      calc Kdr * (vsz b + 1) ≤ Kdr * 7 := Nat.mul_le_mul_left _ (by omega)
        _ = 7 * Kdr := by ring
    have h3 : PW main (pushP (Val.int 1)) [C] [Val.int 1, C] (4 * Kp) := by
      have h0 := PW.pushOnAny (A := [C]) (hpush main (Val.int 1))
      refine PW.le h0 ?_
      rw [cw_vsz_int1]
      omega
    have h4 : PW main consP [Val.int 1, C] [Val.cons (Val.int 1) C] Kc :=
      PW.consV hcons (Val.int 1) C
    refine cw_conseq (PW.comp h1 (PW.comp h2 (PW.comp h3 h4)) rest) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hout; simpa using hout
    · intro vs hvs; omega
  have hqno : ∀ (a : ℤ) (b C : Val) (rest : List Val), isz a ≤ 4 → vsz b ≤ 6 →
      WordR main qno (fun vs => vs = Val.int a :: b :: C :: rest)
        (fun _ out => out = C :: rest) (fun _ => 12 * Kdr) := by
    intro a b C rest ha hb
    have h1 : PW main dropP [Val.int a, b, C] [b, C] (5 * Kdr) := by
      have h0 : PW main dropP [Val.int a, b, C] [b, C] (Kdr * (vsz (Val.int a) + 1)) := by
        simpa using PW.appendTail [b, C] (PW.drop hdrop (Val.int a))
      refine PW.le h0 ?_
      rw [vsz_int]
      calc Kdr * (isz a + 1) ≤ Kdr * 5 := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kdr := by ring
    have h2 : PW main dropP [b, C] [C] (7 * Kdr) := by
      have h0 : PW main dropP [b, C] [C] (Kdr * (vsz b + 1)) := by
        simpa using PW.appendTail [C] (PW.drop hdrop b)
      refine PW.le h0 ?_
      calc Kdr * (vsz b + 1) ≤ Kdr * 7 := Nat.mul_le_mul_left _ (by omega)
        _ = 7 * Kdr := by ring
    refine cw_conseq (PW.comp h1 h2 rest) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hout; simpa using hout
    · intro vs hvs; omega
  have hqchk : ∀ (a : ℤ) (b C : Val) (rest : List Val), isz a ≤ 4 → vsz b ≤ 6 →
      isz (a - 1) ≤ 3 →
      WordR main qchk (fun vs => vs = Val.int a :: b :: C :: rest)
        (fun _ out => out = (if a - 1 = 0 then Val.cons (Val.int 1) C else C) :: rest)
        (fun _ => (5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr))) := by
    intro a b C rest ha hb hs
    have h1 : PW main dupP [Val.int a, b, C] [Val.int a, Val.int a, b, C] (5 * Kd) := by
      have h0 : PW main dupP [Val.int a, b, C] [Val.int a, Val.int a, b, C]
          (Kd * (vsz (Val.int a) + 1)) := by
        simpa using PW.appendTail [b, C] (PW.dup hdup (Val.int a))
      refine PW.le h0 ?_
      rw [vsz_int]
      calc Kd * (isz a + 1) ≤ Kd * 5 := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kd := by ring
    have h2 : PW main (pushP (Val.int 1)) [Val.int a, Val.int a, b, C]
        [Val.int 1, Val.int a, Val.int a, b, C] (4 * Kp) := by
      have h0 := PW.pushOnAny (A := [Val.int a, Val.int a, b, C]) (hpush main (Val.int 1))
      refine PW.le h0 ?_
      rw [cw_vsz_int1]
      omega
    have h3 : PW main swapP [Val.int 1, Val.int a, Val.int a, b, C]
        [Val.int a, Val.int 1, Val.int a, b, C] (8 * Ks) := by
      have h0 : PW main swapP [Val.int 1, Val.int a] [Val.int a, Val.int 1]
          (Ks * (vsz (Val.int 1) + vsz (Val.int a) + 1)) := PW.swap hswap (Val.int 1) (Val.int a)
      have h0' := PW.appendTail [Val.int a, b, C] h0
      refine PW.le h0' ?_
      rw [cw_vsz_int1, vsz_int]
      calc Ks * (3 + isz a + 1) ≤ Ks * 8 := Nat.mul_le_mul_left _ (by omega)
        _ = 8 * Ks := by ring
    have h4 : PW main subP [Val.int a, Val.int 1, Val.int a, b, C]
        [Val.int (a - 1), Val.int a, b, C] (7 * Ksub) := by
      have h0 : PW main subP [Val.int a, Val.int 1] [Val.int (a - 1)] (Ksub * (isz a + isz 1)) :=
        PW.binOp (hsub main) (a := a) (b := 1) trivial
      have h0' := PW.appendTail [Val.int a, b, C] h0
      refine PW.le h0' ?_
      rw [cw_isz_one]
      calc Ksub * (isz a + 3) ≤ Ksub * 7 := Nat.mul_le_mul_left _ (by omega)
        _ = 7 * Ksub := by ring
    have hpre : PW main (.seq dupP (.seq (pushP (Val.int 1)) (.seq swapP subP)))
        [Val.int a, b, C] [Val.int (a - 1), Val.int a, b, C]
        (5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) :=
      PW.comp h1 (PW.comp h2 (PW.comp h3 h4))
    have hmid : WordR main (ifZeroP qinc qno)
        (fun vs => vs = Val.int (a - 1) :: Val.int a :: b :: C :: rest)
        (fun _ out => out = (if a - 1 = 0 then Val.cons (Val.int 1) C else C) :: rest)
        (fun _ => 4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr)) := by
      have hz := hifZero main qinc qno (a - 1) (Val.int a :: b :: C :: rest)
        (fun out => out = Val.cons (Val.int 1) C :: rest) (fun out => out = C :: rest)
        (12 * Kdr + 4 * Kp + Kc) (12 * Kdr)
        (fun _ => hqinc a b C rest ha hb) (fun _ => hqno a b C rest ha hb)
      refine cw_conseq hz ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        by_cases h0 : a - 1 = 0
        · rw [if_pos h0]; exact hpost.1 h0
        · rw [if_neg h0]; exact hpost.2 h0
      · intro vs hvs
        have hz' : Kz * (isz (a - 1) + 1) ≤ 4 * Kz := by
          calc Kz * (isz (a - 1) + 1) ≤ Kz * 4 := Nat.mul_le_mul_left _ (by omega)
            _ = 4 * Kz := by ring
        have hmax : max (12 * Kdr + 4 * Kp + Kc) (12 * Kdr)
            ≤ (12 * Kdr + 4 * Kp + Kc) + 12 * Kdr := max_le (by omega) (by omega)
        exact Nat.add_le_add hz' hmax
    refine cw_conseq (cw_seq (hpre rest) hmid
      (fun vs mid h1' h2' => ⟨by simpa using h2', le_rfl⟩)) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hpost
      obtain ⟨mid, hmid', hout⟩ := hpost
      exact hout
    · intro vs hvs; exact le_rfl
  have hqcons : ∀ (a : ℤ) (b C : Val) (rest : List Val), isz a ≤ 4 → vsz b ≤ 6 →
      isz (a - 1) ≤ 3 →
      WordR main qcons (fun vs => vs = Val.cons (Val.int a) b :: C :: rest)
        (fun _ out => out = (if a - 1 = 0 then Val.cons (Val.int 1) C else C) :: rest)
        (fun _ => Ku + ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr)))) := by
    intro a b C rest ha hb hs
    have hpre : WordR main unconsP (fun vs => vs = Val.cons (Val.int a) b :: C :: rest)
        (fun _ out => out = Val.int a :: b :: C :: rest) (fun _ => Ku) := by
      refine cw_conseq (PW.unconsV huncons (Val.int a) b (C :: rest)) ?_ ?_ ?_
      · intro vs hvs; simpa using hvs
      · intro vs out hvs hout; simpa using hout
      · intro vs hvs; exact le_rfl
    refine cw_conseq (cw_seq hpre (hqchk a b C rest ha hb hs)
      (fun vs mid h1' h2' => ⟨by simpa using h2', le_rfl⟩)) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hpost
      obtain ⟨mid, hmid', hout⟩ := hpost
      exact hout
    · intro vs hvs; exact le_rfl
  have hsk : WordR main Cmd.skip (fun vs => vs = C :: rest) (fun _ out => out = C :: rest)
      (fun _ => 1) := by
    refine cw_conseq (hk.skip main) ?_ ?_ ?_
    · intro vs hvs; trivial
    · intro vs out hvs hout; rw [hout]; exact hvs
    · intro vs hvs; exact le_rfl
  have hnilB : awRec zr zi = Val.nil → WordR main Cmd.skip (fun vs => vs = C :: rest)
      (fun _ out => out = C :: rest) (fun _ => 1) := fun _ => hsk
  have hconsB : awRec zr zi ≠ Val.nil → WordR main qcons (fun vs => vs = awRec zr zi :: C :: rest)
      (fun _ out => out = (if zr = 1 then Val.cons (Val.int 1) C else C) :: rest)
      (fun _ => Ku + ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
        (4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr)))) := by
    intro hne
    rcases cw_awRec_cons_cases zr zi hzr hzi hne with hc | hc | hc
    · obtain ⟨hzr1, hzi0, heq⟩ := hc
      have hq := hqcons 1 Val.nil C rest (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have hif : (if (1 : ℤ) - 1 = 0 then Val.cons (Val.int 1) C else C) = Val.cons (Val.int 1) C := by
        rw [if_pos (by norm_num : (1 : ℤ) - 1 = 0)]
      have hif2 : (if zr = 1 then Val.cons (Val.int 1) C else C) = Val.cons (Val.int 1) C := by
        rw [if_pos hzr1]
      refine cw_conseq hq ?_ ?_ ?_
      · intro vs hvs; rw [hvs, heq]
      · intro vs out hvs hout; rw [hout, hif, hif2]
      · intro vs hvs; exact le_rfl
    · obtain ⟨hzr0, hzi1, heq⟩ := hc
      have hq := hqcons 2 Val.nil C rest (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have hif : (if (2 : ℤ) - 1 = 0 then Val.cons (Val.int 1) C else C) = C := by
        rw [if_neg (by norm_num : ¬((2 : ℤ) - 1 = 0))]
      have hif2 : (if zr = 1 then Val.cons (Val.int 1) C else C) = C := by
        rw [if_neg (by rw [hzr0]; norm_num : ¬(zr = 1))]
      refine cw_conseq hq ?_ ?_ ?_
      · intro vs hvs; rw [hvs, heq]
      · intro vs out hvs hout; rw [hout, hif, hif2]
      · intro vs hvs; exact le_rfl
    · obtain ⟨hzr1, hzi1, heq⟩ := hc
      have hq := hqcons 1 (Val.cons (Val.int 2) Val.nil) C rest
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have hif : (if (1 : ℤ) - 1 = 0 then Val.cons (Val.int 1) C else C) = Val.cons (Val.int 1) C := by
        rw [if_pos (by norm_num : (1 : ℤ) - 1 = 0)]
      have hif2 : (if zr = 1 then Val.cons (Val.int 1) C else C) = Val.cons (Val.int 1) C := by
        rw [if_pos hzr1]
      refine cw_conseq hq ?_ ?_ ?_
      · intro vs hvs; rw [hvs, heq]
      · intro vs out hvs hout; rw [hout, hif, hif2]
      · intro vs hvs; exact le_rfl
  have hkey := hifNil main Cmd.skip qcons (awRec zr zi) (C :: rest)
      (fun out => out = C :: rest)
      (fun out => out = (if zr = 1 then Val.cons (Val.int 1) C else C) :: rest)
      1 (Ku + ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
        (4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr)))) hnilB hconsB
  refine cw_conseq hkey ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hpost
    by_cases hnil : awRec zr zi = Val.nil
    · have hz0 := (cw_awRec_nil_iff zr zi hzr hzi).mp hnil
      have hout := hpost.1 hnil
      have hthis : (if zr = 1 then Val.cons (Val.int 1) C else C) = C := by
        rw [if_neg (by rw [hz0.1]; norm_num : ¬(zr = 1))]
      rw [hout, hthis]
    · exact hpost.2 hnil
  · intro vs hvs
    have hmax : max 1 (Ku + ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
        (4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr))))
        ≤ 1 + (Ku + ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + ((12 * Kdr + 4 * Kp + Kc) + 12 * Kdr)))) :=
      max_le (by omega) (by omega)
    exact Nat.add_le_add_left hmax Knil

theorem auCWIncTwo (hk : KernelLib) (hi : IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (rest : List Val) (C : Val) (zr zi : ℤ),
      (zr = 0 ∨ zr = 1) → (zi = 0 ∨ zi = 1) →
      WordR main prog
        (fun vs => vs = awRec zr zi :: C :: rest)
        (fun _ out => out = (if zi = 1 then Val.cons (Val.int 1) C else C) :: rest)
        (fun _ => K) := by
  obtain ⟨ifNilP, Knil, hifNil⟩ := hk.ifNil
  obtain ⟨ifZeroP, Kz, hifZero⟩ := hk.ifZero
  obtain ⟨unconsP, Ku, huncons⟩ := hk.unconsV
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  obtain ⟨consP, Kc, hcons⟩ := hk.consV
  obtain ⟨pushP, Kp, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Ks, hswap⟩ := hk.swap
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  let qz0 : Cmd := dropP
  let qnz : Cmd := .seq dropP (.seq (pushP (.int 1)) consP)
  let qnb : Cmd := .seq (.seq dupP (.seq (pushP (.int 1)) (.seq swapP subP))) (ifZeroP qz0 qnz)
  let qbne : Cmd := .seq dropP (.seq dropP (.seq (pushP (.int 1)) consP))
  let qcons2 : Cmd := .seq unconsP (.seq swapP (ifNilP qnb qbne))
  refine ⟨ifNilP Cmd.skip qcons2,
    Knil + (1 + (Ku + (11 * Ks + (Knil + (((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
      (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
      (7 * Kdr + (5 * Kdr + (4 * Kp + Kc)))))))), ?_⟩
  intro main rest C zr zi hzr hzi
  have hqz0 : ∀ (a : ℤ) (C : Val) (rest : List Val), isz a ≤ 4 →
      WordR main qz0 (fun vs => vs = Val.int a :: C :: rest)
        (fun _ out => out = C :: rest) (fun _ => 5 * Kdr) := by
    intro a C rest ha
    have h0 : PW main dropP [Val.int a, C] [C] (Kdr * (vsz (Val.int a) + 1)) := by
      simpa using PW.appendTail [C] (PW.drop hdrop (Val.int a))
    have h0' : PW main dropP [Val.int a, C] [C] (5 * Kdr) := by
      refine PW.le h0 ?_
      rw [vsz_int]
      calc Kdr * (isz a + 1) ≤ Kdr * 5 := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kdr := by ring
    refine cw_conseq (h0' rest) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hout; simpa using hout
    · intro vs hvs; exact le_rfl
  have hqnz : ∀ (a : ℤ) (C : Val) (rest : List Val), isz a ≤ 4 →
      WordR main qnz (fun vs => vs = Val.int a :: C :: rest)
        (fun _ out => out = Val.cons (Val.int 1) C :: rest) (fun _ => 5 * Kdr + 4 * Kp + Kc) := by
    intro a C rest ha
    have h1 : PW main dropP [Val.int a, C] [C] (5 * Kdr) := by
      have h0 : PW main dropP [Val.int a, C] [C] (Kdr * (vsz (Val.int a) + 1)) := by
        simpa using PW.appendTail [C] (PW.drop hdrop (Val.int a))
      refine PW.le h0 ?_
      rw [vsz_int]
      calc Kdr * (isz a + 1) ≤ Kdr * 5 := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kdr := by ring
    have h2 : PW main (pushP (Val.int 1)) [C] [Val.int 1, C] (4 * Kp) := by
      have h0 := PW.pushOnAny (A := [C]) (hpush main (Val.int 1))
      refine PW.le h0 ?_
      rw [cw_vsz_int1]
      omega
    have h3 : PW main consP [Val.int 1, C] [Val.cons (Val.int 1) C] Kc :=
      PW.consV hcons (Val.int 1) C
    refine cw_conseq (PW.comp h1 (PW.comp h2 h3) rest) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hout; simpa using hout
    · intro vs hvs; omega
  have hqnb : ∀ (a : ℤ) (C : Val) (rest : List Val), isz a ≤ 4 → isz (a - 1) ≤ 3 →
      WordR main qnb (fun vs => vs = Val.int a :: C :: rest)
        (fun _ out => out = (if a - 1 = 0 then C else Val.cons (Val.int 1) C) :: rest)
        (fun _ => (5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) := by
    intro a C rest ha hs
    have h1 : PW main dupP [Val.int a, C] [Val.int a, Val.int a, C] (5 * Kd) := by
      have h0 : PW main dupP [Val.int a, C] [Val.int a, Val.int a, C]
          (Kd * (vsz (Val.int a) + 1)) := by
        simpa using PW.appendTail [C] (PW.dup hdup (Val.int a))
      refine PW.le h0 ?_
      rw [vsz_int]
      calc Kd * (isz a + 1) ≤ Kd * 5 := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kd := by ring
    have h2 : PW main (pushP (Val.int 1)) [Val.int a, Val.int a, C]
        [Val.int 1, Val.int a, Val.int a, C] (4 * Kp) := by
      have h0 := PW.pushOnAny (A := [Val.int a, Val.int a, C]) (hpush main (Val.int 1))
      refine PW.le h0 ?_
      rw [cw_vsz_int1]
      omega
    have h3 : PW main swapP [Val.int 1, Val.int a, Val.int a, C]
        [Val.int a, Val.int 1, Val.int a, C] (8 * Ks) := by
      have h0 : PW main swapP [Val.int 1, Val.int a] [Val.int a, Val.int 1]
          (Ks * (vsz (Val.int 1) + vsz (Val.int a) + 1)) := PW.swap hswap (Val.int 1) (Val.int a)
      have h0' := PW.appendTail [Val.int a, C] h0
      refine PW.le h0' ?_
      rw [cw_vsz_int1, vsz_int]
      calc Ks * (3 + isz a + 1) ≤ Ks * 8 := Nat.mul_le_mul_left _ (by omega)
        _ = 8 * Ks := by ring
    have h4 : PW main subP [Val.int a, Val.int 1, Val.int a, C]
        [Val.int (a - 1), Val.int a, C] (7 * Ksub) := by
      have h0 : PW main subP [Val.int a, Val.int 1] [Val.int (a - 1)] (Ksub * (isz a + isz 1)) :=
        PW.binOp (hsub main) (a := a) (b := 1) trivial
      have h0' := PW.appendTail [Val.int a, C] h0
      refine PW.le h0' ?_
      rw [cw_isz_one]
      calc Ksub * (isz a + 3) ≤ Ksub * 7 := Nat.mul_le_mul_left _ (by omega)
        _ = 7 * Ksub := by ring
    have hpre : PW main (.seq dupP (.seq (pushP (Val.int 1)) (.seq swapP subP))) [Val.int a, C]
        [Val.int (a - 1), Val.int a, C] (5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) :=
      PW.comp h1 (PW.comp h2 (PW.comp h3 h4))
    have hmid : WordR main (ifZeroP qz0 qnz)
        (fun vs => vs = Val.int (a - 1) :: Val.int a :: C :: rest)
        (fun _ out => out = (if a - 1 = 0 then C else Val.cons (Val.int 1) C) :: rest)
        (fun _ => 4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc)))) := by
      have hz := hifZero main qz0 qnz (a - 1) (Val.int a :: C :: rest)
        (fun out => out = C :: rest) (fun out => out = Val.cons (Val.int 1) C :: rest)
        (5 * Kdr) (5 * Kdr + 4 * Kp + Kc)
        (fun _ => hqz0 a C rest ha) (fun _ => hqnz a C rest ha)
      refine cw_conseq hz ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        by_cases h0 : a - 1 = 0
        · rw [if_pos h0]; exact hpost.1 h0
        · rw [if_neg h0]; exact hpost.2 h0
      · intro vs hvs
        have hz' : Kz * (isz (a - 1) + 1) ≤ 4 * Kz := by
          calc Kz * (isz (a - 1) + 1) ≤ Kz * 4 := Nat.mul_le_mul_left _ (by omega)
            _ = 4 * Kz := by ring
        have hmax : max (5 * Kdr) (5 * Kdr + 4 * Kp + Kc)
            ≤ 5 * Kdr + (5 * Kdr + (4 * Kp + Kc)) := max_le (by omega) (by omega)
        exact Nat.add_le_add hz' hmax
    refine cw_conseq (cw_seq (hpre rest) hmid
      (fun vs mid h1' h2' => ⟨by simpa using h2', le_rfl⟩)) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hpost
      obtain ⟨mid, hmid', hout⟩ := hpost
      exact hout
    · intro vs hvs; exact le_rfl
  have hqbne : ∀ (a : ℤ) (b C : Val) (rest : List Val), isz a ≤ 4 → vsz b ≤ 6 →
      WordR main qbne (fun vs => vs = b :: Val.int a :: C :: rest)
        (fun _ out => out = Val.cons (Val.int 1) C :: rest)
        (fun _ => 7 * Kdr + (5 * Kdr + (4 * Kp + Kc))) := by
    intro a b C rest ha hb
    have h1 : PW main dropP [b, Val.int a, C] [Val.int a, C] (7 * Kdr) := by
      have h0 : PW main dropP [b, Val.int a, C] [Val.int a, C] (Kdr * (vsz b + 1)) := by
        simpa using PW.appendTail [Val.int a, C] (PW.drop hdrop b)
      refine PW.le h0 ?_
      calc Kdr * (vsz b + 1) ≤ Kdr * 7 := Nat.mul_le_mul_left _ (by omega)
        _ = 7 * Kdr := by ring
    have h2 : PW main dropP [Val.int a, C] [C] (5 * Kdr) := by
      have h0 : PW main dropP [Val.int a, C] [C] (Kdr * (vsz (Val.int a) + 1)) := by
        simpa using PW.appendTail [C] (PW.drop hdrop (Val.int a))
      refine PW.le h0 ?_
      rw [vsz_int]
      calc Kdr * (isz a + 1) ≤ Kdr * 5 := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kdr := by ring
    have h3 : PW main (pushP (Val.int 1)) [C] [Val.int 1, C] (4 * Kp) := by
      have h0 := PW.pushOnAny (A := [C]) (hpush main (Val.int 1))
      refine PW.le h0 ?_
      rw [cw_vsz_int1]
      omega
    have h4 : PW main consP [Val.int 1, C] [Val.cons (Val.int 1) C] Kc :=
      PW.consV hcons (Val.int 1) C
    refine cw_conseq (PW.comp h1 (PW.comp h2 (PW.comp h3 h4)) rest) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hout; simpa using hout
    · intro vs hvs; omega
  have hqcons2 : ∀ (a : ℤ) (b C : Val) (rest : List Val), isz a ≤ 4 → vsz b ≤ 6 →
      isz (a - 1) ≤ 3 →
      WordR main qcons2 (fun vs => vs = Val.cons (Val.int a) b :: C :: rest)
        (fun _ out => out = (if b = Val.nil then
            (if a - 1 = 0 then C else Val.cons (Val.int 1) C) else Val.cons (Val.int 1) C) :: rest)
        (fun _ => Ku + (11 * Ks + (Knil + (((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
          (7 * Kdr + (5 * Kdr + (4 * Kp + Kc))))))) := by
    intro a b C rest ha hb hs
    have hpre : WordR main unconsP (fun vs => vs = Val.cons (Val.int a) b :: C :: rest)
        (fun _ out => out = Val.int a :: b :: C :: rest) (fun _ => Ku) := by
      refine cw_conseq (PW.unconsV huncons (Val.int a) b (C :: rest)) ?_ ?_ ?_
      · intro vs hvs; simpa using hvs
      · intro vs out hvs hout; simpa using hout
      · intro vs hvs; exact le_rfl
    have hsw : WordR main swapP (fun vs => vs = Val.int a :: b :: C :: rest)
        (fun _ out => out = b :: Val.int a :: C :: rest) (fun _ => 11 * Ks) := by
      have h0 : PW main swapP [Val.int a, b] [b, Val.int a]
          (Ks * (vsz (Val.int a) + vsz b + 1)) := PW.swap hswap (Val.int a) b
      have h0' := PW.appendTail [C] h0
      refine cw_conseq (h0' rest) ?_ ?_ ?_
      · intro vs hvs; simpa using hvs
      · intro vs out hvs hout; simpa using hout
      · intro vs hvs
        rw [vsz_int]
        calc Ks * (isz a + vsz b + 1) ≤ Ks * 11 := Nat.mul_le_mul_left _ (by omega)
          _ = 11 * Ks := by ring
    have hifn : WordR main (ifNilP qnb qbne) (fun vs => vs = b :: Val.int a :: C :: rest)
        (fun _ out => out = (if b = Val.nil then
            (if a - 1 = 0 then C else Val.cons (Val.int 1) C) else Val.cons (Val.int 1) C) :: rest)
        (fun _ => Knil + (((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
          (7 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) := by
      have h := hifNil main qnb qbne b (Val.int a :: C :: rest)
        (fun out => out = (if a - 1 = 0 then C else Val.cons (Val.int 1) C) :: rest)
        (fun out => out = Val.cons (Val.int 1) C :: rest)
        ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc)))))
        (7 * Kdr + (5 * Kdr + (4 * Kp + Kc)))
        (fun _ => hqnb a C rest ha hs) (fun _ => hqbne a b C rest ha hb)
      refine cw_conseq h ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        by_cases hb0 : b = Val.nil
        · rw [if_pos hb0]; exact hpost.1 hb0
        · rw [if_neg hb0]; exact hpost.2 hb0
      · intro vs hvs
        have hmax : max ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
              (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc)))))
            (7 * Kdr + (5 * Kdr + (4 * Kp + Kc)))
            ≤ ((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
              (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
              (7 * Kdr + (5 * Kdr + (4 * Kp + Kc))) := max_le (by omega) (by omega)
        exact Nat.add_le_add_left hmax Knil
    refine cw_conseq (cw_seq hpre (cw_seq hsw hifn
      (fun vs mid h1' h2' => ⟨by simpa using h2', le_rfl⟩))
      (fun vs mid h1' h2' => ⟨by simpa using h2', le_rfl⟩)) ?_ ?_ ?_
    · intro vs hvs; simpa using hvs
    · intro vs out hvs hpost
      obtain ⟨m1, hm1, m2, hm2, hout⟩ := hpost
      exact hout
    · intro vs hvs; exact le_rfl
  have hsk : WordR main Cmd.skip (fun vs => vs = C :: rest) (fun _ out => out = C :: rest)
      (fun _ => 1) := by
    refine cw_conseq (hk.skip main) ?_ ?_ ?_
    · intro vs hvs; trivial
    · intro vs out hvs hout; rw [hout]; exact hvs
    · intro vs hvs; exact le_rfl
  have hnilB : awRec zr zi = Val.nil → WordR main Cmd.skip (fun vs => vs = C :: rest)
      (fun _ out => out = C :: rest) (fun _ => 1) := fun _ => hsk
  have hconsB : awRec zr zi ≠ Val.nil → WordR main qcons2 (fun vs => vs = awRec zr zi :: C :: rest)
      (fun _ out => out = (if zi = 1 then Val.cons (Val.int 1) C else C) :: rest)
      (fun _ => Ku + (11 * Ks + (Knil + (((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
        (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
        (7 * Kdr + (5 * Kdr + (4 * Kp + Kc))))))) := by
    intro hne
    rcases cw_awRec_cons_cases zr zi hzr hzi hne with hc | hc | hc
    · obtain ⟨hzr1, hzi0, heq⟩ := hc
      have hq := hqcons2 1 Val.nil C rest (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have hif : (if Val.nil = Val.nil then
          (if (1 : ℤ) - 1 = 0 then C else Val.cons (Val.int 1) C) else Val.cons (Val.int 1) C) = C := by
        rw [if_pos rfl, if_pos (by norm_num : (1 : ℤ) - 1 = 0)]
      have hif2 : (if zi = 1 then Val.cons (Val.int 1) C else C) = C := by
        rw [if_neg (by rw [hzi0]; norm_num : ¬(zi = 1))]
      refine cw_conseq hq ?_ ?_ ?_
      · intro vs hvs; rw [hvs, heq]
      · intro vs out hvs hout; rw [hout, hif, hif2]
      · intro vs hvs; exact le_rfl
    · obtain ⟨hzr0, hzi1, heq⟩ := hc
      have hq := hqcons2 2 Val.nil C rest (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have hif : (if Val.nil = Val.nil then
          (if (2 : ℤ) - 1 = 0 then C else Val.cons (Val.int 1) C) else Val.cons (Val.int 1) C)
          = Val.cons (Val.int 1) C := by
        rw [if_pos rfl, if_neg (by norm_num : ¬((2 : ℤ) - 1 = 0))]
      have hif2 : (if zi = 1 then Val.cons (Val.int 1) C else C) = Val.cons (Val.int 1) C := by
        rw [if_pos hzi1]
      refine cw_conseq hq ?_ ?_ ?_
      · intro vs hvs; rw [hvs, heq]
      · intro vs out hvs hout; rw [hout, hif, hif2]
      · intro vs hvs; exact le_rfl
    · obtain ⟨hzr1, hzi1, heq⟩ := hc
      have hq := hqcons2 1 (Val.cons (Val.int 2) Val.nil) C rest
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have hbne : Val.cons (Val.int 2) Val.nil ≠ Val.nil := by decide +kernel
      have hif : (if Val.cons (Val.int 2) Val.nil = Val.nil then
          (if (1 : ℤ) - 1 = 0 then C else Val.cons (Val.int 1) C) else Val.cons (Val.int 1) C)
          = Val.cons (Val.int 1) C := by
        rw [if_neg hbne]
      have hif2 : (if zi = 1 then Val.cons (Val.int 1) C else C) = Val.cons (Val.int 1) C := by
        rw [if_pos hzi1]
      refine cw_conseq hq ?_ ?_ ?_
      · intro vs hvs; rw [hvs, heq]
      · intro vs out hvs hout; rw [hout, hif, hif2]
      · intro vs hvs; exact le_rfl
  have hkey := hifNil main Cmd.skip qcons2 (awRec zr zi) (C :: rest)
      (fun out => out = C :: rest)
      (fun out => out = (if zi = 1 then Val.cons (Val.int 1) C else C) :: rest)
      1 (Ku + (11 * Ks + (Knil + (((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
        (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
        (7 * Kdr + (5 * Kdr + (4 * Kp + Kc))))))) hnilB hconsB
  refine cw_conseq hkey ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hpost
    by_cases hnil : awRec zr zi = Val.nil
    · have hz0 := (cw_awRec_nil_iff zr zi hzr hzi).mp hnil
      have hout := hpost.1 hnil
      have hthis : (if zi = 1 then Val.cons (Val.int 1) C else C) = C := by
        rw [if_neg (by rw [hz0.2]; norm_num : ¬(zi = 1))]
      rw [hout, hthis]
    · exact hpost.2 hnil
  · intro vs hvs
    have hmax : max 1 (Ku + (11 * Ks + (Knil + (((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
        (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
        (7 * Kdr + (5 * Kdr + (4 * Kp + Kc)))))))
        ≤ 1 + (Ku + (11 * Ks + (Knil + (((5 * Kd + (4 * Kp + (8 * Ks + 7 * Ksub))) +
          (4 * Kz + (5 * Kdr + (5 * Kdr + (4 * Kp + Kc))))) +
          (7 * Kdr + (5 * Kdr + (4 * Kp + Kc))))))) := max_le (by omega) (by omega)
    exact Nat.add_le_add_left hmax Knil

theorem auCWIncAll (hk : KernelLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (rest : List Val) (C x : Val), vsz x ≤ 10 →
      WordR main prog (fun vs => vs = x :: C :: rest)
        (fun _ out => out = Val.cons (Val.int 1) C :: rest) (fun _ => K) := by
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  obtain ⟨consP, Kc, hcons⟩ := hk.consV
  obtain ⟨pushP, Kp, hpush⟩ := hk.pushVal
  let q : Cmd := .seq dropP (.seq (pushP (.int 1)) consP)
  refine ⟨q, 11 * Kdr + 4 * Kp + Kc, ?_⟩
  intro main rest C x hx
  have h1 : PW main dropP [x, C] [C] (11 * Kdr) := by
    have h0 : PW main dropP [x, C] [C] (Kdr * (vsz x + 1)) := by
      simpa using PW.appendTail [C] (PW.drop hdrop x)
    refine PW.le h0 ?_
    calc Kdr * (vsz x + 1) ≤ Kdr * 11 := Nat.mul_le_mul_left _ (by omega)
      _ = 11 * Kdr := by ring
  have h2 : PW main (pushP (Val.int 1)) [C] [Val.int 1, C] (4 * Kp) := by
    have h0 := PW.pushOnAny (A := [C]) (hpush main (Val.int 1))
    refine PW.le h0 ?_
    rw [cw_vsz_int1]
    omega
  have h3 : PW main consP [Val.int 1, C] [Val.cons (Val.int 1) C] Kc :=
    PW.consV hcons (Val.int 1) C
  refine cw_conseq (PW.comp h1 (PW.comp h2 h3) rest) ?_ ?_ ?_
  · intro vs hvs; simpa using hvs
  · intro vs out hvs hout; simpa using hout
  · intro vs hvs; omega

/-! ## 7.  Turning a unary chain into its length -/

theorem cw_cast_two_pow_sub_one (c : ℕ) :
    (((2 ^ c - 1 : ℕ)) : ℤ) = (2 : ℤ) ^ c - 1 := by
  rw [Nat.cast_sub (Nat.one_le_two_pow (n := c)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

theorem cw_add_one_two_pow (c : ℕ) :
    (1 : ℤ) + ((2 : ℤ) ^ c - 1) = (((2 ^ c : ℕ)) : ℤ) := by
  push_cast
  ring

theorem cw_isz_two_pow (c : ℕ) : isz (((2 ^ c : ℕ)) : ℤ) ≤ c + 3 := by
  rw [isz, Int.natAbs_natCast]
  have h : (2 ^ c).size ≤ c + 1 := by
    rw [Nat.size_le]
    calc 2 ^ c < 2 ^ c * 2 := by
          have h2 := pow_pos (by norm_num : (0 : ℕ) < 2) c
          omega
      _ = 2 ^ (c + 1) := by rw [pow_succ]
  omega

theorem cw_isz_natCast_one : isz (((1 : ℕ)) : ℤ) = 3 := by decide +kernel

theorem cw_cast_one : (((1 : ℕ)) : ℤ) = (1 : ℤ) := by norm_num

theorem cw_sum_replicate (n : ℕ) (a : ℕ) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.sum_cons, ih]; ring

theorem cw_sum_map_isz_replicate (c : ℕ) :
    (List.map (fun h : ℤ => isz h) (List.map (fun a : ℕ => (a : ℤ)) (List.replicate c 1))).sum
      = 3 * c := by
  rw [List.map_map, List.map_replicate, cw_sum_replicate]
  change c * isz (((1 : ℕ)) : ℤ) = 3 * c
  rw [cw_isz_natCast_one]
  ring

theorem cw_sum_map_isz_replicate' (c : ℕ) :
    (List.map (fun h : ℕ => isz (h : ℤ)) (List.replicate c 1)).sum = 3 * c := by
  rw [List.map_replicate, cw_sum_replicate]
  change c * isz (((1 : ℕ)) : ℤ) = 3 * c
  rw [cw_isz_natCast_one]
  ring

theorem cw_sum_map_isz_coe (l : List ℕ) (h : ∀ x ∈ l, x = 1) :
    ((l.map fun h => isz h)).sum = 3 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : a = 1 := h a (List.mem_cons_self ..)
      have ht : ∀ x ∈ t, x = 1 := fun x hx => h x (List.mem_cons_of_mem a hx)
      have hcoe : ((a :: t : List ℕ) : List ℤ) = ((a : ℤ) :: (t : List ℤ)) := rfl
      rw [hcoe, List.map_cons, List.sum_cons, ih ht, ha, List.length_cons]
      change 3 + 3 * t.length = 3 * (t.length + 1)
      ring

theorem auCWUnaryToIntLocal (hk : KernelLib) (hi : IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (c : ℕ) (rest : List Val),
      WordR main prog
        (fun vs => vs = ofList (List.replicate c (Val.int 1)) :: rest)
        (fun _ out => out = Val.int (c : ℤ) :: rest)
        (fun _ => K * (c + 1)) := by
  obtain ⟨pushP, Kp, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Ks, hswap⟩ := hk.swap
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨epP, Kep, hep⟩ := hi.evalPoly
  obtain ⟨clP, Kcl, hcl⟩ := hi.clog2
  let q : Cmd := .seq (.seq (pushP (.int 1)) swapP)
    (.seq epP (.seq (pushP (.int 1)) (.seq addP clP)))
  refine ⟨q, 8 * Kp + 5 * Ks + 5 * Kep + 5 * Kadd + 3 * Kcl, ?_⟩
  intro main c rest
  have hch : ofList (List.replicate c (Val.int 1)) = intList (List.replicate c 1) :=
    (cw_intList_replicate c).symm
  have h1 : PW main (pushP (Val.int 1)) [ofList (List.replicate c (Val.int 1))]
      [Val.int 1, ofList (List.replicate c (Val.int 1))] (4 * Kp) := by
    have h0 := PW.pushOnAny (A := [ofList (List.replicate c (Val.int 1))]) (hpush main (Val.int 1))
    refine PW.le h0 ?_
    rw [cw_vsz_int1]
    omega
  have h2 : PW main swapP [Val.int 1, ofList (List.replicate c (Val.int 1))]
      [ofList (List.replicate c (Val.int 1)), Val.int 1] (Ks * (4 * c + 5)) := by
    have h0 : PW main swapP [Val.int 1, ofList (List.replicate c (Val.int 1))]
        [ofList (List.replicate c (Val.int 1)), Val.int 1]
        (Ks * (vsz (Val.int 1) + vsz (ofList (List.replicate c (Val.int 1))) + 1)) :=
      PW.swap hswap (Val.int 1) (ofList (List.replicate c (Val.int 1)))
    refine PW.le h0 ?_
    rw [cw_vsz_int1, cw_vsz_chain]
    exact le_of_eq (by ring)
  have h3 : PW main epP [ofList (List.replicate c (Val.int 1)), Val.int 1]
      [Val.int ((2 : ℤ) ^ c - 1)] (Kep * (5 * c + 4)) := by
    intro r
    refine cw_conseq (hep main (List.replicate c 1) 1 le_rfl ?_) ?_ ?_ ?_
    · intro h hm
      obtain ⟨-, h1⟩ := List.mem_replicate.mp hm
      rw [h1]
      norm_num
    · intro vs hvs
      refine ⟨r, ?_⟩
      simpa only [cw_intList_replicate, cw_cast_one, List.cons_append, List.nil_append] using hvs
    · intro vs out hvs hpost
      obtain ⟨r', hvs', hout⟩ := hpost
      have hr : r' = r := by
        have h2 : intList (List.replicate c 1) :: Val.int (((1 : ℕ)) : ℤ) :: r' =
            ofList (List.replicate c (Val.int 1)) :: Val.int 1 :: r := hvs'.symm.trans hvs
        exact (List.cons.inj (List.cons.inj h2).2).2
      rw [hout, hr, cw_evalChunks_replicate, cw_cast_two_pow_sub_one, List.cons_append,
        List.nil_append]
    · intro vs hvs
      have h2 : isz (((1 : ℕ)) : ℤ) = 3 := cw_isz_natCast_one
      rw [cw_sum_map_isz_coe (List.replicate c 1) (by
            intro x hx
            exact (List.mem_replicate.mp hx).2), List.length_replicate, h2]
      exact Nat.mul_le_mul_left _ (by omega)
  have h4 : PW main (pushP (Val.int 1)) [Val.int ((2 : ℤ) ^ c - 1)]
      [Val.int 1, Val.int ((2 : ℤ) ^ c - 1)] (4 * Kp) := by
    have h0 := PW.pushOnAny (A := [Val.int ((2 : ℤ) ^ c - 1)]) (hpush main (Val.int 1))
    refine PW.le h0 ?_
    rw [cw_vsz_int1]
    omega
  have h5 : PW main addP [Val.int 1, Val.int ((2 : ℤ) ^ c - 1)]
      [Val.int (((2 ^ c : ℕ)) : ℤ)] (Kadd * (c + 5)) := by
    have h0 : PW main addP [Val.int 1, Val.int ((2 : ℤ) ^ c - 1)]
        [Val.int (1 + ((2 : ℤ) ^ c - 1))] (Kadd * (isz (1 : ℤ) + isz ((2 : ℤ) ^ c - 1))) :=
      PW.binOp (hadd main) (a := (1 : ℤ)) (b := ((2 : ℤ) ^ c - 1)) trivial
    have h0' : PW main addP [Val.int 1, Val.int ((2 : ℤ) ^ c - 1)]
        [Val.int (((2 ^ c : ℕ)) : ℤ)] (Kadd * (isz (1 : ℤ) + isz ((2 : ℤ) ^ c - 1))) := by
      simpa only [cw_add_one_two_pow] using h0
    refine PW.le h0' ?_
    rw [cw_isz_one]
    have hsz := cw_isz_two_pow_sub_one c
    calc Kadd * (3 + isz ((2 : ℤ) ^ c - 1)) ≤ Kadd * (3 + (c + 2)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = Kadd * (c + 5) := by ring
  have h6 : PW main clP [Val.int (((2 ^ c : ℕ)) : ℤ)] [Val.int (c : ℤ)] (Kcl * (c + 3)) := by
    have h0 := PW.unOp (hcl main)
      (show (0 : ℤ) ≤ (((2 ^ c : ℕ)) : ℤ) by positivity)
    have hval : Val.int ((Nat.clog 2 (((2 ^ c : ℕ)) : ℤ).toNat : ℤ)) = Val.int (c : ℤ) := by
      rw [Int.toNat_natCast, cw_clog_two_pow]
    rw [hval] at h0
    exact PW.le h0 (Nat.mul_le_mul_left _ (cw_isz_two_pow c))
  have hpre : PW main (.seq (pushP (Val.int 1)) swapP) [ofList (List.replicate c (Val.int 1))]
      [ofList (List.replicate c (Val.int 1)), Val.int 1] (4 * Kp + Ks * (4 * c + 5)) :=
    PW.comp h1 h2
  have hpost : PW main (.seq epP (.seq (pushP (Val.int 1)) (.seq addP clP)))
      [ofList (List.replicate c (Val.int 1)), Val.int 1] [Val.int (c : ℤ)]
      (Kep * (5 * c + 4) + (4 * Kp + (Kadd * (c + 5) + Kcl * (c + 3)))) := by
    refine PW.comp h3 (PW.comp h4 (PW.comp h5 h6))
  refine cw_conseq (PW.comp hpre hpost rest) ?_ ?_ ?_
  · intro vs hvs; simpa using hvs
  · intro vs out hvs hout; simpa using hout
  · intro vs hvs
    have e0 : 4 * Kp ≤ 4 * Kp * (c + 1) := by
      calc 4 * Kp = 4 * Kp * 1 := by ring
        _ ≤ 4 * Kp * (c + 1) := Nat.mul_le_mul_left _ (by omega)
    have e1 : Ks * (4 * c + 5) ≤ 5 * Ks * (c + 1) := by
      calc Ks * (4 * c + 5) ≤ Ks * (5 * (c + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Ks * (c + 1) := by ring
    have e2 : Kep * (5 * c + 4) ≤ 5 * Kep * (c + 1) := by
      calc Kep * (5 * c + 4) ≤ Kep * (5 * (c + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kep * (c + 1) := by ring
    have e3 : Kadd * (c + 5) ≤ 5 * Kadd * (c + 1) := by
      calc Kadd * (c + 5) ≤ Kadd * (5 * (c + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 5 * Kadd * (c + 1) := by ring
    have e4 : Kcl * (c + 3) ≤ 3 * Kcl * (c + 1) := by
      calc Kcl * (c + 3) ≤ Kcl * (3 * (c + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * Kcl * (c + 1) := by ring
    calc 4 * Kp + Ks * (4 * c + 5) +
          (Kep * (5 * c + 4) + (4 * Kp + (Kadd * (c + 5) + Kcl * (c + 3))))
        ≤ 4 * Kp * (c + 1) + 5 * Ks * (c + 1) +
          (5 * Kep * (c + 1) + (4 * Kp * (c + 1) + (5 * Kadd * (c + 1) + 3 * Kcl * (c + 1)))) :=
          add_le_add (add_le_add e0 e1) (add_le_add e2 (add_le_add e0 (add_le_add e3 e4)))
      _ = (8 * Kp + 5 * Ks + 5 * Kep + 5 * Kadd + 3 * Kcl) * (c + 1) := by ring

/-! ## 8.  The main counting word -/


/-! ## 9.  The per-record counts -/

def cwNum1 (qs : List (ℤ × ℤ)) (i : ℕ) : ℕ :=
  ((qs.map fun q => if q.1 = 1 then 1 else 0).take i).sum

def cwNum2 (qs : List (ℤ × ℤ)) (i : ℕ) : ℕ :=
  ((qs.map fun q => if q.2 = 1 then 1 else 0).take i).sum

theorem cw_list_take_sum_succ (l : List ℕ) (i : ℕ) :
    (l.take (i + 1)).sum = (l.take i).sum + l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
      cases i with
      | zero => simp
      | succ k =>
      rw [List.take_succ_cons, List.take_succ_cons]
      simp only [List.sum_cons, List.getD_cons_succ]
      rw [ih]
      ring

theorem cw_getD_default {α : Type} {l : List α} {d : α} {i : ℕ} (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]
  rfl

theorem cw_sum_take_le (l : List ℕ) (h : ∀ x ∈ l, x ≤ 1) (i : ℕ) : (l.take i).sum ≤ i := by
  induction i with
  | zero => simp
  | succ k ih =>
      rw [cw_list_take_sum_succ]
      have hk : l.getD k 0 ≤ 1 := by
        by_cases hlt : k < l.length
        · rw [List.getD_eq_getElem _ _ hlt]
          exact h _ (List.getElem_mem hlt)
        · rw [cw_getD_default (d := (0 : ℕ)) (by omega)]
          omega
      omega

theorem cwNum1_succ (qs : List (ℤ × ℤ)) {i : ℕ} (hi : i < qs.length) :
    cwNum1 qs (i + 1) = cwNum1 qs i + (if (qs.getD i (0, 0)).1 = 1 then 1 else 0) := by
  unfold cwNum1
  rw [cw_list_take_sum_succ]
  congr 1
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

theorem cwNum1_le (qs : List (ℤ × ℤ)) (i : ℕ) : cwNum1 qs i ≤ i := by
  unfold cwNum1
  refine cw_sum_take_le _ ?_ i
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
  split <;> omega

theorem cw_sum_map_int (f : ℤ × ℤ → ℕ) (l : List (ℤ × ℤ)) :
    (((l.map f).sum : ℕ) : ℤ) = (l.map fun q => ((f q : ℕ) : ℤ)).sum := by
  induction l with
  | nil => simp
  | cons q t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih]

theorem cwNum1_top (qs : List (ℤ × ℤ)) :
    ((cwNum1 qs qs.length : ℕ) : ℤ) =
      (qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum := by
  unfold cwNum1
  rw [List.take_of_length_le (by simp), cw_sum_map_int]
  congr 1
  apply List.map_congr_left
  intro q _
  by_cases h : q.1 = 1 <;> simp [h]

theorem cwNum2_succ (qs : List (ℤ × ℤ)) {i : ℕ} (hi : i < qs.length) :
    cwNum2 qs (i + 1) = cwNum2 qs i + (if (qs.getD i (0, 0)).2 = 1 then 1 else 0) := by
  unfold cwNum2
  rw [cw_list_take_sum_succ]
  congr 1
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

theorem cwNum2_le (qs : List (ℤ × ℤ)) (i : ℕ) : cwNum2 qs i ≤ i := by
  unfold cwNum2
  refine cw_sum_take_le _ ?_ i
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
  split <;> omega

theorem cwNum2_top (qs : List (ℤ × ℤ)) :
    ((cwNum2 qs qs.length : ℕ) : ℤ) =
      (qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum := by
  unfold cwNum2
  rw [List.take_of_length_le (by simp), cw_sum_map_int]
  congr 1
  apply List.map_congr_left
  intro q _
  by_cases h : q.2 = 1 <;> simp [h]

theorem auCWCount (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (qs : List (ℤ × ℤ)) (T : List HvdH.Val),
      (∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1) → (∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList (qs.map fun q => Work.Resample.awRec q.1 q.2) :: T)
        (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
        (fun _ => K * (qs.length + 1)) := by
  obtain ⟨inc1P, K1, hinc1⟩ := auCWIncOne hk hi
  obtain ⟨inc2P, K2, hinc2⟩ := auCWIncTwo hk hi
  obtain ⟨incAP, K3, hincA⟩ := auCWIncAll hk
  obtain ⟨cvP, Kcv, hcv⟩ := auCWUnaryToIntLocal hk hi
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨swapP, Ks, hswap⟩ := hk.swap
  obtain ⟨rollP, Krl, hroll⟩ := hk.roll
  obtain ⟨pushP, Kp, hpush⟩ := hk.pushVal
  obtain ⟨foldP, Kf, hfold⟩ := hk.foldList
  let P : Cmd := .seq dupP (.seq dupP (.seq (pushP Val.nil) (.seq swapP (.seq (foldP inc1P)
      (.seq swapP (.seq (pushP Val.nil) (.seq swapP (.seq (foldP inc2P)
      (.seq (rollP 2) (.seq (pushP Val.nil) (.seq swapP (.seq (foldP incAP)
      (.seq cvP (.seq swapP (.seq cvP (.seq (rollP 2) cvP))))))))))))))))
  refine ⟨P, 24 * Kd + 61 * Ks + 6 * Kp + 81 * Krl + (K1 + K2 + K3) + 36 * Kf + 3 * Kcv, ?_⟩
  intro main qs T h1 h2
  set KK : ℕ := 24 * Kd + 61 * Ks + 6 * Kp + 81 * Krl + (K1 + K2 + K3) + 36 * Kf + 3 * Kcv with hKK
  set L : ℕ := qs.length with hL
  set xs : List Val := qs.map (fun q => awRec q.1 q.2) with hxs
  set X : Val := ofList xs with hX
  set u1 : Val := ofList (List.replicate (cwNum1 qs qs.length) (Val.int 1)) with hu1
  set u2 : Val := ofList (List.replicate (cwNum2 qs qs.length) (Val.int 1)) with hu2
  set u3 : Val := ofList (List.replicate qs.length (Val.int 1)) with hu3
  have hxslen : xs.length = qs.length := by rw [hxs]; exact List.length_map _
  have hrec : ∀ x ∈ xs, vsz x ≤ 10 := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact cw_awRec_vsz_le q.1 q.2 (h1 q hq) (h2 q hq)
  have hXsz : vsz X ≤ 11 * L + 1 := by
    rw [hX, cw_szl_ofList]
    have h1' : szl xs ≤ xs.length * 10 := cw_szl_le_len_mul hrec
    rw [hxslen, ← hL]
    omega
  have hu1sz : vsz u1 ≤ 4 * L + 1 := by
    rw [hu1, cw_vsz_chain]
    have h1' : cwNum1 qs qs.length ≤ L := by
      have := cwNum1_le qs qs.length
      rw [← hL]; exact this
    omega
  have hu2sz : vsz u2 ≤ 4 * L + 1 := by
    rw [hu2, cw_vsz_chain]
    have h1' : cwNum2 qs qs.length ≤ L := by
      have := cwNum2_le qs qs.length
      rw [← hL]; exact this
    omega
  have hX12 : vsz X + 1 ≤ 12 * (L + 1) := by omega
  have hgetD : ∀ i < xs.length, xs.getD i Val.nil =
      awRec (qs.getD i (0, 0)).1 (qs.getD i (0, 0)).2 := by
    intro i hi
    have hiq : i < qs.length := by
      rw [hxslen] at hi
      rw [← hL] at hi
      exact hi
    rw [hxs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiq,
      List.getD_eq_getElem _ _ hiq]
    simp
  have hmemD : ∀ i < qs.length, qs.getD i (0, 0) ∈ qs := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  -- step 1, 2: two copies of the list
  have s1 : PW main dupP [X] [X, X] ((12 * Kd) * (L + 1)) :=
    PW.le (PW.dup hdup X) (by
      calc Kd * (vsz X + 1) ≤ Kd * (12 * (L + 1)) := Nat.mul_le_mul_left _ hX12
        _ = (12 * Kd) * (L + 1) := by ring)
  have s2 : PW main dupP [X, X] [X, X, X] ((12 * Kd) * (L + 1)) := by
    simpa using PW.appendTail [X] s1
  -- step 3: push the empty accumulator
  have s3 : PW main (pushP Val.nil) [X, X, X] [Val.nil, X, X, X] ((2 * Kp) * (L + 1)) := by
    have h0 : PW main (pushP Val.nil) [X, X, X] [Val.nil, X, X, X]
        (Kp * (vsz Val.nil + 1)) := PW.pushOnAny (A := [X, X, X]) (hpush main Val.nil)
    refine PW.le h0 ?_
    rw [vsz_nil]
    calc Kp * (1 + 1) = 2 * Kp := by ring
      _ = 2 * Kp * 1 := by ring
      _ ≤ 2 * Kp * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  -- step 4
  have s4 : PW main swapP [Val.nil, X, X, X] [X, Val.nil, X, X] ((13 * Ks) * (L + 1)) := by
    have h0 : PW main swapP [Val.nil, X, X, X] [X, Val.nil, X, X]
        (Ks * (vsz Val.nil + vsz X + 1)) := by
      simpa using PW.appendTail [X, X] (PW.swap hswap Val.nil X)
    refine PW.le h0 ?_
    rw [vsz_nil]
    calc Ks * (1 + vsz X + 1) ≤ Ks * (13 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (13 * Ks) * (L + 1) := by ring
  -- step 5: the first fold
  have s5 : PW main (foldP inc1P) [X, Val.nil, X, X] [u1, X, X] ((K1 + 12 * Kf) * (L + 1)) := by
    intro rest
    let I1 : ℕ → List Val → Prop := fun i acc =>
      ∃ r : List Val, acc = ofList (List.replicate (cwNum1 qs i) (Val.int 1)) :: r ∧
        r = X :: X :: rest
    have hbody : ∀ i acc, i < xs.length → I1 i acc →
        WordR main inc1P (fun vs => vs = xs.getD i Val.nil :: acc) (fun _ out => I1 (i + 1) out)
          (fun _ => K1) := by
      intro i acc hi hI
      obtain ⟨r, hr, hrX⟩ := hI
      have hiq : i < qs.length := by
        rw [hxslen] at hi
        rw [← hL] at hi
        exact hi
      have hbody1 := hinc1 main r (ofList (List.replicate (cwNum1 qs i) (Val.int 1)))
        (qs.getD i (0, 0)).1 (qs.getD i (0, 0)).2 (h1 _ (hmemD i hiq)) (h2 _ (hmemD i hiq))
      refine cw_conseq hbody1 ?_ ?_ ?_
      · intro vs hvs
        rw [hvs, hr, hgetD i hi]
      · intro vs out hvs hout
        refine ⟨r, ?_, hrX⟩
        rw [hout]
        by_cases hz : (qs.getD i (0, 0)).1 = 1
        · rw [if_pos hz, cwNum1_succ qs hiq, if_pos hz]
          simp only [cw_chain_succ]
        · rw [if_neg hz, cwNum1_succ qs hiq, if_neg hz]
          simp only [Nat.add_zero]
      · intro vs hvs
        exact le_rfl
    have hfl := hfold main inc1P xs I1 K1 10 hrec hbody
    refine cw_conseq hfl ?_ ?_ ?_
    · intro vs hvs
      refine ⟨Val.nil :: X :: X :: rest, ?_, X :: X :: rest, ?_, rfl⟩
      · simpa only [hvs, hX, List.cons_append, List.nil_append]
      · rfl
    · intro vs out hvs hpost
      obtain ⟨r, hr, hrX⟩ := hpost
      simpa only [hrX, hu1, hxslen, List.cons_append, List.nil_append] using hr
    · intro vs hvs
      rw [hxslen, ← hL]
      have h11 : Kf * (10 + 1) = Kf * 11 := by norm_num
      rw [h11]
      have h2' : L * (K1 + Kf * 11) ≤ (K1 + Kf * 11) * (L + 1) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_succ L)
      have h3' : Kf ≤ Kf * (L + 1) := by
        calc Kf = Kf * 1 := by ring
          _ ≤ Kf * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      calc L * (K1 + Kf * 11) + Kf ≤ (K1 + Kf * 11) * (L + 1) + Kf * (L + 1) :=
            Nat.add_le_add h2' h3'
        _ = (K1 + 12 * Kf) * (L + 1) := by ring
  -- step 6
  have s6 : PW main swapP [u1, X, X] [X, u1, X] ((16 * Ks) * (L + 1)) := by
    have h0 : PW main swapP [u1, X, X] [X, u1, X] (Ks * (vsz u1 + vsz X + 1)) := by
      simpa using PW.appendTail [X] (PW.swap hswap u1 X)
    refine PW.le h0 ?_
    calc Ks * (vsz u1 + vsz X + 1) ≤ Ks * (16 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (16 * Ks) * (L + 1) := by ring
  -- step 7
  have s7 : PW main (pushP Val.nil) [X, u1, X] [Val.nil, X, u1, X] ((2 * Kp) * (L + 1)) := by
    have h0 : PW main (pushP Val.nil) [X, u1, X] [Val.nil, X, u1, X]
        (Kp * (vsz Val.nil + 1)) := PW.pushOnAny (A := [X, u1, X]) (hpush main Val.nil)
    refine PW.le h0 ?_
    rw [vsz_nil]
    calc Kp * (1 + 1) = 2 * Kp := by ring
      _ = 2 * Kp * 1 := by ring
      _ ≤ 2 * Kp * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  -- step 8
  have s8 : PW main swapP [Val.nil, X, u1, X] [X, Val.nil, u1, X] ((13 * Ks) * (L + 1)) := by
    have h0 : PW main swapP [Val.nil, X, u1, X] [X, Val.nil, u1, X]
        (Ks * (vsz Val.nil + vsz X + 1)) := by
      simpa using PW.appendTail [u1, X] (PW.swap hswap Val.nil X)
    refine PW.le h0 ?_
    rw [vsz_nil]
    calc Ks * (1 + vsz X + 1) ≤ Ks * (13 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (13 * Ks) * (L + 1) := by ring
  -- step 9: the second fold
  have s9 : PW main (foldP inc2P) [X, Val.nil, u1, X] [u2, u1, X] ((K2 + 12 * Kf) * (L + 1)) := by
    intro rest
    let I2 : ℕ → List Val → Prop := fun i acc =>
      ∃ r : List Val, acc = ofList (List.replicate (cwNum2 qs i) (Val.int 1)) :: r ∧
        r = u1 :: X :: rest
    have hbody : ∀ i acc, i < xs.length → I2 i acc →
        WordR main inc2P (fun vs => vs = xs.getD i Val.nil :: acc) (fun _ out => I2 (i + 1) out)
          (fun _ => K2) := by
      intro i acc hi hI
      obtain ⟨r, hr, hrX⟩ := hI
      have hiq : i < qs.length := by
        rw [hxslen] at hi
        rw [← hL] at hi
        exact hi
      have hbody1 := hinc2 main r (ofList (List.replicate (cwNum2 qs i) (Val.int 1)))
        (qs.getD i (0, 0)).1 (qs.getD i (0, 0)).2 (h1 _ (hmemD i hiq)) (h2 _ (hmemD i hiq))
      refine cw_conseq hbody1 ?_ ?_ ?_
      · intro vs hvs
        rw [hvs, hr, hgetD i hi]
      · intro vs out hvs hout
        refine ⟨r, ?_, hrX⟩
        rw [hout]
        by_cases hz : (qs.getD i (0, 0)).2 = 1
        · rw [if_pos hz, cwNum2_succ qs hiq, if_pos hz]
          simp only [cw_chain_succ]
        · rw [if_neg hz, cwNum2_succ qs hiq, if_neg hz]
          simp only [Nat.add_zero]
      · intro vs hvs
        exact le_rfl
    have hfl := hfold main inc2P xs I2 K2 10 hrec hbody
    refine cw_conseq hfl ?_ ?_ ?_
    · intro vs hvs
      refine ⟨Val.nil :: u1 :: X :: rest, ?_, u1 :: X :: rest, ?_, rfl⟩
      · simpa only [hvs, hX, List.cons_append, List.nil_append]
      · rfl
    · intro vs out hvs hpost
      obtain ⟨r, hr, hrX⟩ := hpost
      simpa only [hrX, hu2, hxslen, List.cons_append, List.nil_append] using hr
    · intro vs hvs
      rw [hxslen, ← hL]
      have h11 : Kf * (10 + 1) = Kf * 11 := by norm_num
      rw [h11]
      have h2' : L * (K2 + Kf * 11) ≤ (K2 + Kf * 11) * (L + 1) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_succ L)
      have h3' : Kf ≤ Kf * (L + 1) := by
        calc Kf = Kf * 1 := by ring
          _ ≤ Kf * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      calc L * (K2 + Kf * 11) + Kf ≤ (K2 + Kf * 11) * (L + 1) + Kf * (L + 1) :=
            Nat.add_le_add h2' h3'
        _ = (K2 + 12 * Kf) * (L + 1) := by ring
  -- step 10: bring the third copy of the list to the top
  have s10 : PW main (rollP 2) [u2, u1, X] [X, u2, u1] ((60 * Krl) * (L + 1)) := by
    have h0 := PW.roll main hroll (A := [u2, u1, X]) (k := 2) (by simp)
    refine PW.le h0 ?_
    have hsz : szl (([u2, u1, X] : List Val).take (2 + 1)) + 1 ≤ 20 * (L + 1) := by
      have h2' : szl (([u2, u1, X] : List Val).take (2 + 1)) = vsz u2 + (vsz u1 + vsz X) := by
        simp [szl]
      rw [h2']
      omega
    calc Krl * (2 + 1) * (szl (([u2, u1, X] : List Val).take (2 + 1)) + 1)
        = Krl * 3 * (szl (([u2, u1, X] : List Val).take (2 + 1)) + 1) := by ring
      _ ≤ Krl * 3 * (20 * (L + 1)) := Nat.mul_le_mul_left _ hsz
      _ = (60 * Krl) * (L + 1) := by ring
  -- step 11
  have s11 : PW main (pushP Val.nil) [X, u2, u1] [Val.nil, X, u2, u1] ((2 * Kp) * (L + 1)) := by
    have h0 : PW main (pushP Val.nil) [X, u2, u1] [Val.nil, X, u2, u1]
        (Kp * (vsz Val.nil + 1)) := PW.pushOnAny (A := [X, u2, u1]) (hpush main Val.nil)
    refine PW.le h0 ?_
    rw [vsz_nil]
    calc Kp * (1 + 1) = 2 * Kp := by ring
      _ = 2 * Kp * 1 := by ring
      _ ≤ 2 * Kp * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  -- step 12
  have s12 : PW main swapP [Val.nil, X, u2, u1] [X, Val.nil, u2, u1] ((13 * Ks) * (L + 1)) := by
    have h0 : PW main swapP [Val.nil, X, u2, u1] [X, Val.nil, u2, u1]
        (Ks * (vsz Val.nil + vsz X + 1)) := by
      simpa using PW.appendTail [u2, u1] (PW.swap hswap Val.nil X)
    refine PW.le h0 ?_
    rw [vsz_nil]
    calc Ks * (1 + vsz X + 1) ≤ Ks * (13 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (13 * Ks) * (L + 1) := by ring
  -- step 13: the length fold
  have s13 : PW main (foldP incAP) [X, Val.nil, u2, u1] [u3, u2, u1] ((K3 + 12 * Kf) * (L + 1)) := by
    intro rest
    let I3 : ℕ → List Val → Prop := fun i acc =>
      ∃ r : List Val, acc = ofList (List.replicate i (Val.int 1)) :: r ∧ r = u2 :: u1 :: rest
    have hbody : ∀ i acc, i < xs.length → I3 i acc →
        WordR main incAP (fun vs => vs = xs.getD i Val.nil :: acc) (fun _ out => I3 (i + 1) out)
          (fun _ => K3) := by
      intro i acc hi hI
      obtain ⟨r, hr, hrX⟩ := hI
      have hxsd : vsz (xs.getD i Val.nil) ≤ 10 := by
        rw [List.getD_eq_getElem _ _ hi]
        exact hrec _ (List.getElem_mem hi)
      have hbody1 := hincA main r (ofList (List.replicate i (Val.int 1))) (xs.getD i Val.nil) hxsd
      refine cw_conseq hbody1 ?_ ?_ ?_
      · intro vs hvs
        rw [hvs, hr]
      · intro vs out hvs hout
        refine ⟨r, ?_, hrX⟩
        rw [hout, cw_chain_succ]
      · intro vs hvs
        exact le_rfl
    have hfl := hfold main incAP xs I3 K3 10 hrec hbody
    refine cw_conseq hfl ?_ ?_ ?_
    · intro vs hvs
      refine ⟨Val.nil :: u2 :: u1 :: rest, ?_, u2 :: u1 :: rest, ?_, rfl⟩
      · simpa only [hvs, hX, List.cons_append, List.nil_append]
      · rfl
    · intro vs out hvs hpost
      obtain ⟨r, hr, hrX⟩ := hpost
      simpa only [hrX, hu3, hxslen, List.cons_append, List.nil_append] using hr
    · intro vs hvs
      rw [hxslen, ← hL]
      have h11 : Kf * (10 + 1) = Kf * 11 := by norm_num
      rw [h11]
      have h2' : L * (K3 + Kf * 11) ≤ (K3 + Kf * 11) * (L + 1) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_succ L)
      have h3' : Kf ≤ Kf * (L + 1) := by
        calc Kf = Kf * 1 := by ring
          _ ≤ Kf * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      calc L * (K3 + Kf * 11) + Kf ≤ (K3 + Kf * 11) * (L + 1) + Kf * (L + 1) :=
            Nat.add_le_add h2' h3'
        _ = (K3 + 12 * Kf) * (L + 1) := by ring
  -- step 14: convert the length chain
  have hcvPW : ∀ c : ℕ, PW main cvP [ofList (List.replicate c (Val.int 1))] [Val.int (c : ℤ)]
      (Kcv * (c + 1)) := fun c r => hcv main c r
  have s14 : PW main cvP [u3, u2, u1] [Val.int (L : ℤ), u2, u1] (Kcv * (L + 1)) := by
    have h0 : PW main cvP [u3] [Val.int (L : ℤ)] (Kcv * (L + 1)) := by
      rw [hu3, ← hL]
      exact hcvPW L
    exact PW.appendTail [u2, u1] h0
  -- step 15
  have s15 : PW main swapP [Val.int (L : ℤ), u2, u1] [u2, Val.int (L : ℤ), u1]
      ((6 * Ks) * (L + 1)) := by
    have h0 : PW main swapP [Val.int (L : ℤ), u2, u1] [u2, Val.int (L : ℤ), u1]
        (Ks * (vsz (Val.int (L : ℤ)) + vsz u2 + 1)) := by
      simpa using PW.appendTail [u1] (PW.swap hswap (Val.int (L : ℤ)) u2)
    refine PW.le h0 ?_
    rw [vsz_int]
    have hLz : isz (L : ℤ) ≤ L + 2 := cw_isz_natCast_le L
    calc Ks * (isz (L : ℤ) + vsz u2 + 1) ≤ Ks * (6 * (L + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = (6 * Ks) * (L + 1) := by ring
  -- step 16: convert the marker-2 chain
  have s16 : PW main cvP [u2, Val.int (L : ℤ), u1]
      [Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ), u1] (Kcv * (L + 1)) := by
    have h00 : PW main cvP [u2] [Val.int ((cwNum2 qs qs.length : ℕ) : ℤ)]
        (Kcv * (cwNum2 qs qs.length + 1)) := by
      rw [hu2]
      exact hcvPW (cwNum2 qs qs.length)
    have h0 : PW main cvP [u2] [Val.int ((cwNum2 qs qs.length : ℕ) : ℤ)] (Kcv * (L + 1)) := by
      refine PW.le h00 ?_
      have h1' : cwNum2 qs qs.length ≤ L := by
        have := cwNum2_le qs qs.length
        rw [← hL]; exact this
      exact Nat.mul_le_mul_left _ (by omega)
    exact PW.appendTail [Val.int (L : ℤ), u1] h0
  -- step 17: bring the marker-1 chain to the top
  have s17 : PW main (rollP 2) [Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ), u1]
      [u1, Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ)] ((21 * Krl) * (L + 1)) := by
    have h0 := PW.roll main hroll
      (A := [Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ), u1]) (k := 2) (by simp)
    refine PW.le h0 ?_
    have hsz : szl (([Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ), u1] : List Val).take (2 + 1))
        = isz ((cwNum2 qs qs.length : ℕ) : ℤ) + (isz (L : ℤ) + vsz u1) := by
      simp [szl, vsz_int]
    have hn2 : isz ((cwNum2 qs qs.length : ℕ) : ℤ) ≤ L + 2 := by
      have h1' : cwNum2 qs qs.length ≤ L := by
        have := cwNum2_le qs qs.length
        rw [← hL]; exact this
      have h2' := cw_isz_natCast_le (cwNum2 qs qs.length)
      omega
    have hLz : isz (L : ℤ) ≤ L + 2 := cw_isz_natCast_le L
    have hsz' : szl (([Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ), u1] : List Val).take (2 + 1)) + 1
        ≤ 7 * (L + 1) := by
      rw [hsz]
      omega
    calc Krl * (2 + 1) *
          (szl (([Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ), u1] : List Val).take (2 + 1)) + 1)
        = Krl * 3 *
          (szl (([Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ), u1] : List Val).take (2 + 1)) + 1) := by ring
      _ ≤ Krl * 3 * (7 * (L + 1)) := Nat.mul_le_mul_left _ hsz'
      _ = (21 * Krl) * (L + 1) := by ring
  -- step 18: convert the marker-1 chain
  have s18 : PW main cvP [u1, Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ)]
      [Val.int ((cwNum1 qs qs.length : ℕ) : ℤ), Val.int ((cwNum2 qs qs.length : ℕ) : ℤ),
        Val.int (L : ℤ)] (Kcv * (L + 1)) := by
    have h00 : PW main cvP [u1] [Val.int ((cwNum1 qs qs.length : ℕ) : ℤ)]
        (Kcv * (cwNum1 qs qs.length + 1)) := by
      rw [hu1]
      exact hcvPW (cwNum1 qs qs.length)
    have h0 : PW main cvP [u1] [Val.int ((cwNum1 qs qs.length : ℕ) : ℤ)] (Kcv * (L + 1)) := by
      refine PW.le h00 ?_
      have h1' : cwNum1 qs qs.length ≤ L := by
        have := cwNum1_le qs qs.length
        rw [← hL]; exact this
      exact Nat.mul_le_mul_left _ (by omega)
    exact PW.appendTail [Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ)] h0
  -- assembly
  have hmain : PW main P [X] [Val.int ((cwNum1 qs qs.length : ℕ) : ℤ),
      Val.int ((cwNum2 qs qs.length : ℕ) : ℤ), Val.int (L : ℤ)] (KK * (L + 1)) := by
    have e17 := PW.comp s17 s18
    have e16 := PW.comp s16 e17
    have e15 := PW.comp s15 e16
    have e14 := PW.comp s14 e15
    have e13 := PW.comp s13 e14
    have e12 := PW.comp s12 e13
    have e11 := PW.comp s11 e12
    have e10 := PW.comp s10 e11
    have e9 := PW.comp s9 e10
    have e8 := PW.comp s8 e9
    have e7 := PW.comp s7 e8
    have e6 := PW.comp s6 e7
    have e5 := PW.comp s5 e6
    have e4 := PW.comp s4 e5
    have e3 := PW.comp s3 e4
    have e2 := PW.comp s2 e3
    have e1 := PW.comp s1 e2
    refine PW.le e1 ?_
    rw [hKK]
    exact le_of_eq (by ring)
  have hmainW := hmain T
  refine cw_conseq hmainW ?_ ?_ ?_
  · intro vs hvs
    simpa only [hX, hxs, List.cons_append, List.nil_append] using hvs
  · intro vs out hvs hout
    simp only [hout, hL, cwNum1_top, cwNum2_top, List.cons_append, List.nil_append]
  · intro vs hvs
    rw [hL]


end Work.Resample
