import Mathlib
import Submission.Work.Resample.auCWDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

namespace AuCW

/-- `Pipe main prog A B c`: `prog` turns the fixed window `A` of values at the top of the value
stack into the fixed window `B`, leaving everything below it untouched, at cost `≤ c`. -/
def Pipe (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val,
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c)

theorem Pipe.le {main prog : Cmd} {A B : List Val} {c c' : ℕ} (h : Pipe main prog A B c)
    (hc : c ≤ c') : Pipe main prog A B c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, le_trans hn hc, hstk, hoth⟩

theorem Pipe.rw {main prog : Cmd} {A B B' : List Val} {c : ℕ} (h : Pipe main prog A B c)
    (hB : B = B') : Pipe main prog A B' c := hB ▸ h

theorem Pipe.comp {main p q : Cmd} {A B D : List Val} {c d : ℕ} (h1 : Pipe main p A B c)
    (h2 : Pipe main q B D d) : Pipe main (.seq p q) A D (c + d) := by
  intro rest vs hvs s R hR
  obtain ⟨mid, s', n1, hmid, hev1, hn1, hstk1, hoth1⟩ := h1 rest vs hvs s R hR
  obtain ⟨out, s'', n2, hout, hev2, hn2, hstk2, hoth2⟩ := h2 rest mid hmid s' R hstk1
  exact ⟨out, s'', n1 + n2, hout, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem Pipe.appendTail {main prog : Cmd} {A B : List Val} {c : ℕ} (T : List Val)
    (h : Pipe main prog A B c) : Pipe main prog (A ++ T) (B ++ T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    h (T ++ rest) vs (by rw [hvs, List.append_assoc]) s R
      (by simpa only [hvs, List.append_assoc] using hR)
  exact ⟨out, s', n, by rw [hout, List.append_assoc], hev, hn, hstk, hoth⟩

theorem getD_append_of_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).getD k .nil = l.getD k .nil := List.getD_append l rest .nil k h

theorem eraseIdx_append_of_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).eraseIdx k = l.eraseIdx k ++ rest := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ j =>
      rw [List.cons_append, List.eraseIdx_cons_succ, ih (by simpa using h),
        List.eraseIdx_cons_succ, List.cons_append]

theorem cons_inj3 {a b a' b' : Val} {l l' : List Val} (h : a :: b :: l = a' :: b' :: l') :
    a = a' ∧ b = b' ∧ l = l' := by
  have h1 := List.cons.inj h
  have h2 := List.cons.inj h1.2
  exact ⟨h1.1, h2.1, h2.2⟩

theorem int_cons_inj3 {a b a' b' : ℤ} {l l' : List Val}
    (h : Val.int a :: Val.int b :: l = Val.int a' :: Val.int b' :: l') :
    a = a' ∧ b = b' ∧ l = l' := by
  have h1 := List.cons.inj h
  have h2 := List.cons.inj h1.2
  exact ⟨Val.int.inj h1.1, Val.int.inj h2.1, h2.2⟩

theorem Pipe.binOp {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) :
    Pipe main prog [.int a, .int b] [.int (f a b)] (C a b) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: .int b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, b, rest, hv2, hab⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := int_cons_inj3 (hvs'.symm.trans hv2)
  refine ⟨out, s', n, ?_, hev, ?_, hstk, hoth⟩
  · rw [hout, h1, h2, h3]; rfl
  · rw [hv2] at hn; exact hn

theorem Pipe.unOp {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} (ha : P a) :
    Pipe main prog [.int a] [.int (f a)] (C a) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, rest, hv2, ha⟩ s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have ha' : a' = a := Val.int.inj h1.1
  have hn' : n ≤ C a := by rw [hv2] at hn; exact hn
  exact ⟨out, s', n, by rw [hout, ha', h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.consV {consP : Cmd} {Kc : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kc))
    (a b : Val) : Pipe main consP [a, b] [.cons a b] Kc := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv2)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

theorem Pipe.dup {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Pipe main prog [a] [a, a] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.1, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.drop {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Pipe main prog [a] [] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.swap {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) : Pipe main prog [a, b] [b, a] (K * (vsz a + vsz b + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + vsz b + 1) := by
    rw [hv2] at hn
    simpa only [List.getD_cons_zero, List.getD_cons_succ] using hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.pick {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (prog k) A (A.getD k .nil :: A) (K * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1) := by
    have h1 : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h1
    simpa [Work.Fx.szl] using h1
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, ← List.cons_append]

theorem Pipe.roll {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (prog k) A (A.getD k .nil :: A.eraseIdx k)
      (K * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1) := by
    have h1 : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h1
    simpa [Work.Fx.szl] using h1
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, eraseIdx_append_of_lt hk, List.cons_append]

/-! ## size and cost helpers -/

theorem szl_le_len_mul {A : List Val} {n : ℕ} (h : ∀ v ∈ A, vsz v ≤ n) :
    Work.Fx.szl A ≤ A.length * n := by
  induction A with
  | nil => simp [Work.Fx.szl]
  | cons a t ih =>
    have ha : vsz a ≤ n := h a (by simp)
    have ht : ∀ v ∈ t, vsz v ≤ n := fun v hv => h v (by simp [hv])
    have hih := ih ht
    rw [Work.Fx.szl_cons, List.length_cons]
    nlinarith [Nat.zero_le (vsz a), Nat.zero_le (Work.Fx.szl t)]

theorem szl_take_le {A : List Val} {SEL k : ℕ} (hmem : ∀ v ∈ A, vsz v ≤ SEL) (hk : k ≤ 7) :
    Work.Fx.szl (A.take (k + 1)) ≤ 8 * SEL := by
  have h1 : Work.Fx.szl (A.take (k + 1)) ≤ (A.take (k + 1)).length * SEL :=
    szl_le_len_mul (fun v hv => hmem v (List.mem_of_mem_take hv))
  have h2 : (A.take (k + 1)).length ≤ 8 := by rw [List.length_take]; omega
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

theorem le_step_mover {K KS SEL k : ℕ} {A : List Val} (hK : K ≤ KS) (hk : k ≤ 7)
    (hsz : Work.Fx.szl (A.take (k + 1)) ≤ 8 * SEL) (hSEL : 1 ≤ SEL) :
    K * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1) ≤ 1000 * KS * SEL := by
  have h1 : K * (k + 1) ≤ KS * 8 := Nat.mul_le_mul hK (by omega)
  have h2 : Work.Fx.szl (A.take (k + 1)) + 1 ≤ 8 * SEL + 1 := by omega
  have h3 : (KS * 8) * (8 * SEL + 1) ≤ 1000 * KS * SEL := by
    have h4 : 64 * SEL + 8 ≤ 1000 * SEL := by omega
    calc (KS * 8) * (8 * SEL + 1) = KS * (64 * SEL + 8) := by ring
      _ ≤ KS * (1000 * SEL) := Nat.mul_le_mul_left KS h4
      _ = 1000 * KS * SEL := by ring
  exact le_trans (Nat.mul_le_mul h1 h2) h3

theorem le_step2 {K KS SEL a b : ℕ} (hK : K ≤ KS) (ha : a ≤ SEL) (hb : b ≤ SEL) :
    K * (a + b) ≤ 1000 * KS * SEL := by
  have h : a + b ≤ 2 * SEL := by omega
  refine le_trans (Nat.mul_le_mul hK h) ?_
  have h2 : 2 * SEL ≤ 1000 * SEL := by omega
  calc KS * (2 * SEL) ≤ KS * (1000 * SEL) := Nat.mul_le_mul_left KS h2
    _ = 1000 * KS * SEL := by ring

theorem le_step3 {K KS SEL a b c : ℕ} (hK : K ≤ KS) (ha : a ≤ SEL) (hb : b ≤ SEL)
    (hc : c ≤ SEL) : K * (a + b + c) ≤ 1000 * KS * SEL := by
  have h : a + b + c ≤ 3 * SEL := by omega
  refine le_trans (Nat.mul_le_mul hK h) ?_
  have h2 : 3 * SEL ≤ 1000 * SEL := by omega
  calc KS * (3 * SEL) ≤ KS * (1000 * SEL) := Nat.mul_le_mul_left KS h2
    _ = 1000 * KS * SEL := by ring

theorem le_step_c {K KS SEL : ℕ} (hK : K ≤ KS) (hSEL : 1 ≤ SEL) :
    K ≤ 1000 * KS * SEL := by
  calc K ≤ KS := hK
    _ = KS * 1 := by ring
    _ ≤ KS * (1000 * SEL) := Nat.mul_le_mul_left KS (by omega)
    _ = 1000 * KS * SEL := by ring

theorem natAbs_eq_toNat_of_nonneg {z : ℤ} (h : 0 ≤ z) : z.natAbs = z.toNat := by
  have h1 : ((z.natAbs : ℕ) : ℤ) = ((z.toNat : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h, Int.toNat_of_nonneg h]
  exact_mod_cast h1

theorem natAbs_lt_pow_of_lt {z : ℤ} {n : ℕ} (h0 : 0 ≤ z) (h : z < (2:ℤ)^n) :
    z.natAbs < 2 ^ n := by
  rw [natAbs_eq_toNat_of_nonneg h0]
  have h1 : ((z.toNat : ℕ) : ℤ) < ((2 ^ n : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]
    calc z < (2:ℤ)^n := h
      _ = ((2^n : ℕ) : ℤ) := by push_cast; ring
  exact_mod_cast h1

theorem isz_le_SEL {z : ℤ} {p : ℕ} {L : ℤ}
    (h : z.natAbs ≤ 2 ^ (2*p + L.natAbs + 3)) : isz z ≤ 10*p + 10*L.natAbs + 100 := by
  have h1 : z.natAbs.size ≤ 2*p + L.natAbs + 4 := by
    rw [Nat.size_le]
    calc z.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := h
      _ < 2 ^ (2*p + L.natAbs + 4) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only [isz]
  omega

end AuCW

theorem auCWFinal (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ)
      (lo_r lo_i Cr Ci L : ℤ) (rest : List HvdH.Val),
      1 ≤ p → 0 ≤ lo_r → lo_r < Work.Resample.awMod p → 0 ≤ lo_i → lo_i < Work.Resample.awMod p →
      0 ≤ Cr → Cr ≤ L → 0 ≤ Ci → Ci ≤ L → 0 ≤ L →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int lo_r :: HvdH.Val.int lo_i
          :: HvdH.Val.int Cr :: HvdH.Val.int Ci :: HvdH.Val.int L :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ out => out = HvdH.cfxVal (Work.Resample.awAns p lo_r Cr L, Work.Resample.awAns p lo_i Ci L)
          :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ => K * (p + 1) * (L.toNat + 1)) := by
  obtain ⟨pickP, KP, hpick⟩ := hk.pick
  obtain ⟨rollP, KR, hroll⟩ := hk.roll
  obtain ⟨dupP, KD, hdup⟩ := hk.dup
  obtain ⟨dropP, KDr, hdrop⟩ := hk.drop
  obtain ⟨swapP, KSw, hswap⟩ := hk.swap
  obtain ⟨consP, KCo, hcons⟩ := hk.consV
  obtain ⟨addP, KAd, hadd⟩ := hi.add
  obtain ⟨subP, KSu, hsub⟩ := hi.sub
  obtain ⟨shlP, KSh, hshl⟩ := hi.shl
  obtain ⟨shrP, KSr, hshr⟩ := hi.shrT
  have hKRle : KR ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKPle : KP ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKDle : KD ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKDrle : KDr ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKSwle : KSw ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKCole : KCo ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKAdle : KAd ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKSule : KSu ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKShle : KSh ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  have hKSrle : KSr ≤ KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1 := by omega
  let KS : ℕ := KP + KR + KD + KDr + KSw + KCo + KAd + KSu + KSh + KSr + 1
  let s1 : Cmd := rollP 3
  let s2 : Cmd := dupP
  let s3 : Cmd := addP
  let s4 : Cmd := pickP 1
  let s5 : Cmd := dupP
  let s6 : Cmd := addP
  let s7 : Cmd := rollP 1
  let s8 : Cmd := pickP 6
  let s9 : Cmd := swapP
  let s10 : Cmd := subP
  let s11 : Cmd := shlP
  let s12 : Cmd := rollP 2
  let s13 : Cmd := addP
  let s14 : Cmd := pickP 1
  let s15 : Cmd := swapP
  let s16 : Cmd := shrP
  let s17 : Cmd := rollP 3
  let s18 : Cmd := dupP
  let s19 : Cmd := addP
  let s20 : Cmd := pickP 2
  let s21 : Cmd := dupP
  let s22 : Cmd := addP
  let s23 : Cmd := rollP 1
  let s24 : Cmd := rollP 5
  let s25 : Cmd := swapP
  let s26 : Cmd := subP
  let s27 : Cmd := shlP
  let s28 : Cmd := rollP 3
  let s29 : Cmd := addP
  let s30 : Cmd := rollP 2
  let s31 : Cmd := swapP
  let s32 : Cmd := shrP
  let s33 : Cmd := swapP
  let s34 : Cmd := consP
  let Q1 : Cmd := s1
  let Q2 : Cmd := Q1 ;;; s2
  let Q3 : Cmd := Q2 ;;; s3
  let Q4 : Cmd := Q3 ;;; s4
  let Q5 : Cmd := Q4 ;;; s5
  let Q6 : Cmd := Q5 ;;; s6
  let Q7 : Cmd := Q6 ;;; s7
  let Q8 : Cmd := Q7 ;;; s8
  let Q9 : Cmd := Q8 ;;; s9
  let Q10 : Cmd := Q9 ;;; s10
  let Q11 : Cmd := Q10 ;;; s11
  let Q12 : Cmd := Q11 ;;; s12
  let Q13 : Cmd := Q12 ;;; s13
  let Q14 : Cmd := Q13 ;;; s14
  let Q15 : Cmd := Q14 ;;; s15
  let Q16 : Cmd := Q15 ;;; s16
  let Q17 : Cmd := Q16 ;;; s17
  let Q18 : Cmd := Q17 ;;; s18
  let Q19 : Cmd := Q18 ;;; s19
  let Q20 : Cmd := Q19 ;;; s20
  let Q21 : Cmd := Q20 ;;; s21
  let Q22 : Cmd := Q21 ;;; s22
  let Q23 : Cmd := Q22 ;;; s23
  let Q24 : Cmd := Q23 ;;; s24
  let Q25 : Cmd := Q24 ;;; s25
  let Q26 : Cmd := Q25 ;;; s26
  let Q27 : Cmd := Q26 ;;; s27
  let Q28 : Cmd := Q27 ;;; s28
  let Q29 : Cmd := Q28 ;;; s29
  let Q30 : Cmd := Q29 ;;; s30
  let Q31 : Cmd := Q30 ;;; s31
  let Q32 : Cmd := Q31 ;;; s32
  let Q33 : Cmd := Q32 ;;; s33
  let Q34 : Cmd := Q33 ;;; s34
  let prog : Cmd := Q34
  refine ⟨prog, 10000000 * KS, ?_⟩
  intro main p α s t lo_r lo_i Cr Ci L rest hp hlor0 hlorM hloi0 hloiM hCr0 hCrL hCi0 hCiL hL0
  let P : Val := .int (p:ℤ)
  let LR : Val := .int lo_r
  let LI : Val := .int lo_i
  let CR : Val := .int Cr
  let CI : Val := .int Ci
  let LN : Val := .int L
  let QQR : ℤ := (Cr + Cr) - L
  let RE : ℤ := (2:ℤ) ^ (((p:ℤ)+(p:ℤ)).toNat)
  let FR : ℤ := QQR * RE
  let GR : ℤ := lo_r + FR
  let AR : ℤ := Int.tdiv GR (2 ^ ((p:ℤ).toNat))
  let QQI : ℤ := (Ci + Ci) - L
  let FI : ℤ := QQI * RE
  let GI : ℤ := lo_i + FI
  let AI : ℤ := Int.tdiv GI (2 ^ ((p:ℤ).toNat))
  let V2CR : Val := .int (Cr + Cr)
  let V2p : Val := .int ((p:ℤ)+(p:ℤ))
  let VDR : Val := .int QQR
  let VFR : Val := .int FR
  let VGR : Val := .int GR
  let VAR : Val := .int AR
  let V2CI : Val := .int (Ci + Ci)
  let VDI : Val := .int QQI
  let VFI : Val := .int FI
  let VGI : Val := .int GI
  let VAI : Val := .int AI
  let VCX : Val := .cons VAR VAI
  let A0 : List Val := [P, LR, LI, CR, CI, LN]
  let A1 : List Val := [CR, P, LR, LI, CI, LN]
  let A2 : List Val := [CR, CR, P, LR, LI, CI, LN]
  let A3 : List Val := [V2CR, P, LR, LI, CI, LN]
  let A4 : List Val := [P, V2CR, P, LR, LI, CI, LN]
  let A5 : List Val := [P, P, V2CR, P, LR, LI, CI, LN]
  let A6 : List Val := [V2p, V2CR, P, LR, LI, CI, LN]
  let A7 : List Val := [V2CR, V2p, P, LR, LI, CI, LN]
  let A8 : List Val := [LN, V2CR, V2p, P, LR, LI, CI, LN]
  let A9 : List Val := [V2CR, LN, V2p, P, LR, LI, CI, LN]
  let A10 : List Val := [VDR, V2p, P, LR, LI, CI, LN]
  let A11 : List Val := [VFR, P, LR, LI, CI, LN]
  let A12 : List Val := [LR, VFR, P, LI, CI, LN]
  let A13 : List Val := [VGR, P, LI, CI, LN]
  let A14 : List Val := [P, VGR, P, LI, CI, LN]
  let A15 : List Val := [VGR, P, P, LI, CI, LN]
  let A16 : List Val := [VAR, P, LI, CI, LN]
  let A17 : List Val := [CI, VAR, P, LI, LN]
  let A18 : List Val := [CI, CI, VAR, P, LI, LN]
  let A19 : List Val := [V2CI, VAR, P, LI, LN]
  let A20 : List Val := [P, V2CI, VAR, P, LI, LN]
  let A21 : List Val := [P, P, V2CI, VAR, P, LI, LN]
  let A22 : List Val := [V2p, V2CI, VAR, P, LI, LN]
  let A23 : List Val := [V2CI, V2p, VAR, P, LI, LN]
  let A24 : List Val := [LN, V2CI, V2p, VAR, P, LI]
  let A25 : List Val := [V2CI, LN, V2p, VAR, P, LI]
  let A26 : List Val := [VDI, V2p, VAR, P, LI]
  let A27 : List Val := [VFI, VAR, P, LI]
  let A28 : List Val := [LI, VFI, VAR, P]
  let A29 : List Val := [VGI, VAR, P]
  let A30 : List Val := [P, VGI, VAR]
  let A31 : List Val := [VGI, P, VAR]
  let A32 : List Val := [VAI, VAR]
  let A33 : List Val := [VAR, VAI]
  let A34 : List Val := [VCX]
  let SEL : ℕ := 10 * p + 10 * L.natAbs + 100
  let STEP : ℕ := 1000 * KS * SEL
  have hSEL1 : 1 ≤ SEL := by
    show 1 ≤ 10 * p + 10 * L.natAbs + 100
    omega
  have hLabs : L.natAbs = L.toNat := AuCW.natAbs_eq_toNat_of_nonneg hL0
  have hCrmax : Cr.natAbs ≤ L.natAbs := by
    rw [hLabs]
    have h1 : ((Cr.toNat : ℕ) : ℤ) ≤ ((L.toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hCr0, Int.toNat_of_nonneg hL0]
      exact hCrL
    have h2 : Cr.toNat ≤ L.toNat := by exact_mod_cast h1
    rwa [AuCW.natAbs_eq_toNat_of_nonneg hCr0]
  have hCimax : Ci.natAbs ≤ L.natAbs := by
    rw [hLabs]
    have h1 : ((Ci.toNat : ℕ) : ℤ) ≤ ((L.toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hCi0, Int.toNat_of_nonneg hL0]
      exact hCiL
    have h2 : Ci.toNat ≤ L.toNat := by exact_mod_cast h1
    rwa [AuCW.natAbs_eq_toNat_of_nonneg hCi0]
  have hLRlt : lo_r.natAbs < 2 ^ (2*p+1) := by
    have h := hlorM
    rw [Work.Resample.awMod] at h
    exact AuCW.natAbs_lt_pow_of_lt hlor0 h
  have hLIlt : lo_i.natAbs < 2 ^ (2*p+1) := by
    have h := hloiM
    rw [Work.Resample.awMod] at h
    exact AuCW.natAbs_lt_pow_of_lt hloi0 h
  have h2pNat : ((p:ℤ) + (p:ℤ)).toNat = 2 * p := by
    have h : ((p:ℤ) + (p:ℤ)) = ((2 * p : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  have hpNat : ((p:ℤ)).toNat = p := Int.toNat_natCast p
  have hbP : (p:ℤ).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    rw [Int.natAbs_natCast]
    calc p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbLR : lo_r.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    calc lo_r.natAbs ≤ 2 ^ (2*p+1) := le_of_lt hLRlt
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbLI : lo_i.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    calc lo_i.natAbs ≤ 2 ^ (2*p+1) := le_of_lt hLIlt
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbCR : Cr.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    calc Cr.natAbs ≤ L.natAbs := hCrmax
      _ ≤ 2 ^ L.natAbs := le_of_lt (Nat.lt_two_pow_self)
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbCI : Ci.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    calc Ci.natAbs ≤ L.natAbs := hCimax
      _ ≤ 2 ^ L.natAbs := le_of_lt (Nat.lt_two_pow_self)
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbL : L.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    calc L.natAbs ≤ 2 ^ L.natAbs := le_of_lt (Nat.lt_two_pow_self)
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb2CR : (Cr + Cr).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    have h1 : (Cr + Cr).natAbs ≤ 2 * L.natAbs := by
      have h2 := Int.natAbs_add_le Cr Cr
      omega
    calc (Cr + Cr).natAbs ≤ 2 * L.natAbs := h1
      _ ≤ 2 ^ (L.natAbs + 1) := by
          calc 2 * L.natAbs ≤ 2 * 2 ^ L.natAbs :=
                Nat.mul_le_mul_left 2 (le_of_lt (Nat.lt_two_pow_self))
            _ = 2 ^ (L.natAbs + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb2CI : (Ci + Ci).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    have h1 : (Ci + Ci).natAbs ≤ 2 * L.natAbs := by
      have h2 := Int.natAbs_add_le Ci Ci
      omega
    calc (Ci + Ci).natAbs ≤ 2 * L.natAbs := h1
      _ ≤ 2 ^ (L.natAbs + 1) := by
          calc 2 * L.natAbs ≤ 2 * 2 ^ L.natAbs :=
                Nat.mul_le_mul_left 2 (le_of_lt (Nat.lt_two_pow_self))
            _ = 2 ^ (L.natAbs + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb2p : ((p:ℤ)+(p:ℤ)).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    have h1 : ((p:ℤ)+(p:ℤ)).natAbs ≤ 2 * p := by
      have h2 := Int.natAbs_add_le (p:ℤ) (p:ℤ)
      rw [Int.natAbs_natCast] at h2
      omega
    calc ((p:ℤ)+(p:ℤ)).natAbs ≤ 2 * p := h1
      _ ≤ 2 ^ (2*p) := le_of_lt (Nat.lt_two_pow_self)
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbQQR2 : ((Cr + Cr) - L).natAbs ≤ 2 ^ (L.natAbs + 2) := by
    have h2 := Int.natAbs_sub_le (Cr + Cr) L
    have h5 : (Cr+Cr).natAbs ≤ 2 * L.natAbs := by
      have h6 := Int.natAbs_add_le Cr Cr
      omega
    calc ((Cr + Cr) - L).natAbs ≤ (Cr+Cr).natAbs + L.natAbs := h2
      _ ≤ 2 * L.natAbs + L.natAbs := by omega
      _ = 3 * L.natAbs := by ring
      _ ≤ 2 ^ (L.natAbs + 2) := by
          calc 3 * L.natAbs ≤ 4 * L.natAbs := by omega
            _ ≤ 4 * 2 ^ L.natAbs :=
                Nat.mul_le_mul_left 4 (le_of_lt (Nat.lt_two_pow_self))
            _ = 2 ^ (L.natAbs + 2) := by rw [pow_succ, pow_succ]; ring
  have hbQQR : ((Cr + Cr) - L).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) :=
    le_trans hbQQR2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbQQI2 : ((Ci + Ci) - L).natAbs ≤ 2 ^ (L.natAbs + 2) := by
    have h2 := Int.natAbs_sub_le (Ci + Ci) L
    have h5 : (Ci+Ci).natAbs ≤ 2 * L.natAbs := by
      have h6 := Int.natAbs_add_le Ci Ci
      omega
    calc ((Ci + Ci) - L).natAbs ≤ (Ci+Ci).natAbs + L.natAbs := h2
      _ ≤ 2 * L.natAbs + L.natAbs := by omega
      _ = 3 * L.natAbs := by ring
      _ ≤ 2 ^ (L.natAbs + 2) := by
          calc 3 * L.natAbs ≤ 4 * L.natAbs := by omega
            _ ≤ 4 * 2 ^ L.natAbs :=
                Nat.mul_le_mul_left 4 (le_of_lt (Nat.lt_two_pow_self))
            _ = 2 ^ (L.natAbs + 2) := by rw [pow_succ, pow_succ]; ring
  have hbQQI : ((Ci + Ci) - L).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) :=
    le_trans hbQQI2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbFR2 : (QQR * RE).natAbs ≤ 2 ^ (2*p + L.natAbs + 2) := by
    show (((Cr + Cr) - L) * RE).natAbs ≤ 2 ^ (2*p + L.natAbs + 2)
    rw [show RE = (2:ℤ) ^ (((p:ℤ)+(p:ℤ)).toNat) from rfl, h2pNat,
      Int.natAbs_mul, Int.natAbs_pow]
    rw [show ((2:ℤ)).natAbs = 2 by norm_num]
    calc ((Cr + Cr) - L).natAbs * 2 ^ (2 * p)
        ≤ 2 ^ (L.natAbs + 2) * 2 ^ (2 * p) := Nat.mul_le_mul hbQQR2 (le_refl _)
      _ = 2 ^ (2*p + L.natAbs + 2) := by
          rw [← pow_add]
          congr 1
          omega
  have hbFR : (QQR * RE).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) :=
    le_trans hbFR2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbFI2 : (QQI * RE).natAbs ≤ 2 ^ (2*p + L.natAbs + 2) := by
    show (((Ci + Ci) - L) * RE).natAbs ≤ 2 ^ (2*p + L.natAbs + 2)
    rw [show RE = (2:ℤ) ^ (((p:ℤ)+(p:ℤ)).toNat) from rfl, h2pNat,
      Int.natAbs_mul, Int.natAbs_pow]
    rw [show ((2:ℤ)).natAbs = 2 by norm_num]
    calc ((Ci + Ci) - L).natAbs * 2 ^ (2 * p)
        ≤ 2 ^ (L.natAbs + 2) * 2 ^ (2 * p) := Nat.mul_le_mul hbQQI2 (le_refl _)
      _ = 2 ^ (2*p + L.natAbs + 2) := by
          rw [← pow_add]
          congr 1
          omega
  have hbFI : (QQI * RE).natAbs ≤ 2 ^ (2*p + L.natAbs + 3) :=
    le_trans hbFI2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbGR : GR.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    show (lo_r + FR).natAbs ≤ 2 ^ (2*p + L.natAbs + 3)
    calc (lo_r + FR).natAbs ≤ lo_r.natAbs + FR.natAbs := Int.natAbs_add_le _ _
      _ ≤ 2 ^ (2*p+1) + 2 ^ (2*p + L.natAbs + 2) := by
          refine Nat.add_le_add (le_of_lt hLRlt) ?_
          exact hbFR2
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := by
          have h7 : 2 ^ (2*p + L.natAbs + 3) = 2 * 2 ^ (2*p + L.natAbs + 2) := by
            rw [show 2*p + L.natAbs + 3 = 2*p + L.natAbs + 2 + 1 by omega, pow_succ]
            ring
          rw [h7]
          have h8 : 2 ^ (2*p+1) ≤ 2 ^ (2*p + L.natAbs + 2) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
  have hbGI : GI.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    show (lo_i + FI).natAbs ≤ 2 ^ (2*p + L.natAbs + 3)
    calc (lo_i + FI).natAbs ≤ lo_i.natAbs + FI.natAbs := Int.natAbs_add_le _ _
      _ ≤ 2 ^ (2*p+1) + 2 ^ (2*p + L.natAbs + 2) := by
          refine Nat.add_le_add (le_of_lt hLIlt) ?_
          exact hbFI2
      _ ≤ 2 ^ (2*p + L.natAbs + 3) := by
          have h7 : 2 ^ (2*p + L.natAbs + 3) = 2 * 2 ^ (2*p + L.natAbs + 2) := by
            rw [show 2*p + L.natAbs + 3 = 2*p + L.natAbs + 2 + 1 by omega, pow_succ]
            ring
          rw [h7]
          have h8 : 2 ^ (2*p+1) ≤ 2 ^ (2*p + L.natAbs + 2) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
  have hbAR : AR.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    show (Int.tdiv GR (2 ^ ((p:ℤ).toNat))).natAbs ≤ 2 ^ (2*p + L.natAbs + 3)
    rw [Int.natAbs_tdiv]
    exact le_trans (Nat.div_le_self _ _) hbGR
  have hbAI : AI.natAbs ≤ 2 ^ (2*p + L.natAbs + 3) := by
    show (Int.tdiv GI (2 ^ ((p:ℤ).toNat))).natAbs ≤ 2 ^ (2*p + L.natAbs + 3)
    rw [Int.natAbs_tdiv]
    exact le_trans (Nat.div_le_self _ _) hbGI
  have hPisz : isz ((p:ℤ)) ≤ SEL := AuCW.isz_le_SEL hbP
  have hLRisz : isz (lo_r) ≤ SEL := AuCW.isz_le_SEL hbLR
  have hLIisz : isz (lo_i) ≤ SEL := AuCW.isz_le_SEL hbLI
  have hCRisz : isz (Cr) ≤ SEL := AuCW.isz_le_SEL hbCR
  have hCIisz : isz (Ci) ≤ SEL := AuCW.isz_le_SEL hbCI
  have hLNisz : isz (L) ≤ SEL := AuCW.isz_le_SEL hbL
  have hV2CRisz : isz (Cr + Cr) ≤ SEL := AuCW.isz_le_SEL hb2CR
  have hV2pisz : isz ((p:ℤ)+(p:ℤ)) ≤ SEL := AuCW.isz_le_SEL hb2p
  have hQQisz : isz (QQR) ≤ SEL := AuCW.isz_le_SEL hbQQR
  have hVFRisz : isz (FR) ≤ SEL := AuCW.isz_le_SEL hbFR
  have hVGRisz : isz (GR) ≤ SEL := AuCW.isz_le_SEL hbGR
  have hVARisz : isz (AR) ≤ SEL := AuCW.isz_le_SEL hbAR
  have hV2CIisz : isz (Ci + Ci) ≤ SEL := AuCW.isz_le_SEL hb2CI
  have hVDIisz : isz (QQI) ≤ SEL := AuCW.isz_le_SEL hbQQI
  have hVFIisz : isz (FI) ≤ SEL := AuCW.isz_le_SEL hbFI
  have hVGIisz : isz (GI) ≤ SEL := AuCW.isz_le_SEL hbGI
  have hVAIisz : isz (AI) ≤ SEL := AuCW.isz_le_SEL hbAI
  have h2pNatSz : ((p:ℤ) + (p:ℤ)).toNat ≤ SEL := by
    rw [h2pNat]
    show 2 * p ≤ 10 * p + 10 * L.natAbs + 100
    omega
  have hPv : vsz P ≤ SEL := by
    show vsz (.int (p:ℤ)) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hPisz
  have hLRv : vsz LR ≤ SEL := by
    show vsz (.int lo_r) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hLRisz
  have hLIv : vsz LI ≤ SEL := by
    show vsz (.int lo_i) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hLIisz
  have hCRv : vsz CR ≤ SEL := by
    show vsz (.int Cr) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hCRisz
  have hCIv : vsz CI ≤ SEL := by
    show vsz (.int Ci) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hCIisz
  have hLNv : vsz LN ≤ SEL := by
    show vsz (.int L) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hLNisz
  have hV2CRv : vsz V2CR ≤ SEL := by
    show vsz (.int (Cr + Cr)) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hV2CRisz
  have hV2pv : vsz V2p ≤ SEL := by
    show vsz (.int ((p:ℤ)+(p:ℤ))) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hV2pisz
  have hVDRv : vsz VDR ≤ SEL := by
    show vsz (.int QQR) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hQQisz
  have hVFRv : vsz VFR ≤ SEL := by
    show vsz (.int FR) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hVFRisz
  have hVGRv : vsz VGR ≤ SEL := by
    show vsz (.int GR) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hVGRisz
  have hVARv : vsz VAR ≤ SEL := by
    show vsz (.int AR) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hVARisz
  have hV2CIv : vsz V2CI ≤ SEL := by
    show vsz (.int (Ci + Ci)) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hV2CIisz
  have hVDIv : vsz VDI ≤ SEL := by
    show vsz (.int QQI) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hVDIisz
  have hVFIv : vsz VFI ≤ SEL := by
    show vsz (.int FI) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hVFIisz
  have hVGIv : vsz VGI ≤ SEL := by
    show vsz (.int GI) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hVGIisz
  have hVAIv : vsz VAI ≤ SEL := by
    show vsz (.int AI) ≤ SEL
    rw [Work.Fx.vsz_int]
    exact hVAIisz
  have e1 : AuCW.Pipe main s1 A0 A1 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A0) (k := 3)
      (by rw [show A0 = [P, LR, LI, CR, CI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 3) hKRle (by omega) ?_ hSEL1
    rw [show A0.take 4 = [P, LR, LI, CR] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e2 : AuCW.Pipe main s2 A1 A2 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [P, LR, LI, CI, LN] (AuCW.Pipe.dup main hdup CR)) ?_
    exact AuCW.le_step3 (K := KD) (a := vsz CR) (b := 1) (c := 0)
      hKDle hCRv hSEL1 (Nat.zero_le _)
  have e3 : AuCW.Pipe main s3 A2 A3 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [P, LR, LI, CI, LN]
      (AuCW.Pipe.binOp (h := hadd main) (a := Cr) (b := Cr) trivial)) ?_
    exact AuCW.le_step2 (K := KAd) (a := isz (Cr)) (b := isz (Cr)) hKAdle hCRisz hCRisz
  have e4 : AuCW.Pipe main s4 A3 A4 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.pick main hpick (A := A3) (k := 1)
      (by rw [show A3 = [V2CR, P, LR, LI, CI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KP) (k := 1) hKPle (by omega) ?_ hSEL1
    rw [show A3.take 2 = [V2CR, P] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e5 : AuCW.Pipe main s5 A4 A5 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2CR, P, LR, LI, CI, LN] (AuCW.Pipe.dup main hdup P)) ?_
    exact AuCW.le_step3 (K := KD) (a := vsz P) (b := 1) (c := 0)
      hKDle hPv hSEL1 (Nat.zero_le _)
  have e6 : AuCW.Pipe main s6 A5 A6 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2CR, P, LR, LI, CI, LN]
      (AuCW.Pipe.binOp (h := hadd main) (a := (p:ℤ)) (b := (p:ℤ)) trivial)) ?_
    exact AuCW.le_step2 (K := KAd) (a := isz ((p:ℤ))) (b := isz ((p:ℤ))) hKAdle hPisz hPisz
  have e7 : AuCW.Pipe main s7 A6 A7 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A6) (k := 1)
      (by rw [show A6 = [V2p, V2CR, P, LR, LI, CI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 1) hKRle (by omega) ?_ hSEL1
    rw [show A6.take 2 = [V2p, V2CR] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e8 : AuCW.Pipe main s8 A7 A8 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.pick main hpick (A := A7) (k := 6)
      (by rw [show A7 = [V2CR, V2p, P, LR, LI, CI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KP) (k := 6) hKPle (by omega) ?_ hSEL1
    rw [show A7.take 7 = [V2CR, V2p, P, LR, LI, CI, LN] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e9 : AuCW.Pipe main s9 A8 A9 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2p, P, LR, LI, CI, LN]
      (AuCW.Pipe.swap main hswap LN V2CR)) ?_
    exact AuCW.le_step3 (K := KSw) (a := vsz LN) (b := vsz V2CR) (c := 1)
      hKSwle hLNv hV2CRv hSEL1
  have e10 : AuCW.Pipe main s10 A9 A10 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2p, P, LR, LI, CI, LN]
      (AuCW.Pipe.binOp (h := hsub main) (a := Cr + Cr) (b := L) trivial)) ?_
    exact AuCW.le_step2 (K := KSu) (a := isz (Cr + Cr)) (b := isz (L)) hKSule hV2CRisz hLNisz
  have e11 : AuCW.Pipe main s11 A10 A11 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [P, LR, LI, CI, LN]
      (AuCW.Pipe.binOp (h := hshl main) (a := QQR) (b := (p:ℤ)+(p:ℤ))
        (by exact Int.add_nonneg (Int.natCast_nonneg p) (Int.natCast_nonneg p)))) ?_
    exact AuCW.le_step3 (K := KSh) (a := isz (QQR)) (b := ((p:ℤ)+(p:ℤ)).toNat)
      (c := isz ((p:ℤ)+(p:ℤ))) hKShle hQQisz h2pNatSz hV2pisz
  have e12 : AuCW.Pipe main s12 A11 A12 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A11) (k := 2)
      (by rw [show A11 = [VFR, P, LR, LI, CI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 2) hKRle (by omega) ?_ hSEL1
    rw [show A11.take 3 = [VFR, P, LR] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e13 : AuCW.Pipe main s13 A12 A13 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [P, LI, CI, LN]
      (AuCW.Pipe.binOp (h := hadd main) (a := lo_r) (b := FR) trivial)) ?_
    exact AuCW.le_step2 (K := KAd) (a := isz (lo_r)) (b := isz (FR)) hKAdle hLRisz hVFRisz
  have e14 : AuCW.Pipe main s14 A13 A14 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.pick main hpick (A := A13) (k := 1)
      (by rw [show A13 = [VGR, P, LI, CI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KP) (k := 1) hKPle (by omega) ?_ hSEL1
    rw [show A13.take 2 = [VGR, P] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e15 : AuCW.Pipe main s15 A14 A15 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [P, LI, CI, LN]
      (AuCW.Pipe.swap main hswap P VGR)) ?_
    exact AuCW.le_step3 (K := KSw) (a := vsz P) (b := vsz VGR) (c := 1)
      hKSwle hPv hVGRv hSEL1
  have e16 : AuCW.Pipe main s16 A15 A16 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [P, LI, CI, LN]
      (AuCW.Pipe.binOp (h := hshr main) (a := GR) (b := (p:ℤ))
        (by exact Int.natCast_nonneg p))) ?_
    exact AuCW.le_step2 (K := KSr) (a := isz (GR)) (b := isz ((p:ℤ))) hKSrle hVGRisz hPisz
  have e17 : AuCW.Pipe main s17 A16 A17 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A16) (k := 3)
      (by rw [show A16 = [VAR, P, LI, CI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 3) hKRle (by omega) ?_ hSEL1
    rw [show A16.take 4 = [VAR, P, LI, CI] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e18 : AuCW.Pipe main s18 A17 A18 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [VAR, P, LI, LN] (AuCW.Pipe.dup main hdup CI)) ?_
    exact AuCW.le_step3 (K := KD) (a := vsz CI) (b := 1) (c := 0)
      hKDle hCIv hSEL1 (Nat.zero_le _)
  have e19 : AuCW.Pipe main s19 A18 A19 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [VAR, P, LI, LN]
      (AuCW.Pipe.binOp (h := hadd main) (a := Ci) (b := Ci) trivial)) ?_
    exact AuCW.le_step2 (K := KAd) (a := isz (Ci)) (b := isz (Ci)) hKAdle hCIisz hCIisz
  have e20 : AuCW.Pipe main s20 A19 A20 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.pick main hpick (A := A19) (k := 2)
      (by rw [show A19 = [V2CI, VAR, P, LI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KP) (k := 2) hKPle (by omega) ?_ hSEL1
    rw [show A19.take 3 = [V2CI, VAR, P] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e21 : AuCW.Pipe main s21 A20 A21 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2CI, VAR, P, LI, LN] (AuCW.Pipe.dup main hdup P)) ?_
    exact AuCW.le_step3 (K := KD) (a := vsz P) (b := 1) (c := 0)
      hKDle hPv hSEL1 (Nat.zero_le _)
  have e22 : AuCW.Pipe main s22 A21 A22 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2CI, VAR, P, LI, LN]
      (AuCW.Pipe.binOp (h := hadd main) (a := (p:ℤ)) (b := (p:ℤ)) trivial)) ?_
    exact AuCW.le_step2 (K := KAd) (a := isz ((p:ℤ))) (b := isz ((p:ℤ))) hKAdle hPisz hPisz
  have e23 : AuCW.Pipe main s23 A22 A23 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A22) (k := 1)
      (by rw [show A22 = [V2p, V2CI, VAR, P, LI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 1) hKRle (by omega) ?_ hSEL1
    rw [show A22.take 2 = [V2p, V2CI] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e24 : AuCW.Pipe main s24 A23 A24 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A23) (k := 5)
      (by rw [show A23 = [V2CI, V2p, VAR, P, LI, LN] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 5) hKRle (by omega) ?_ hSEL1
    rw [show A23.take 6 = [V2CI, V2p, VAR, P, LI, LN] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e25 : AuCW.Pipe main s25 A24 A25 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2p, VAR, P, LI]
      (AuCW.Pipe.swap main hswap LN V2CI)) ?_
    exact AuCW.le_step3 (K := KSw) (a := vsz LN) (b := vsz V2CI) (c := 1)
      hKSwle hLNv hV2CIv hSEL1
  have e26 : AuCW.Pipe main s26 A25 A26 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [V2p, VAR, P, LI]
      (AuCW.Pipe.binOp (h := hsub main) (a := Ci + Ci) (b := L) trivial)) ?_
    exact AuCW.le_step2 (K := KSu) (a := isz (Ci + Ci)) (b := isz (L)) hKSule hV2CIisz hLNisz
  have e27 : AuCW.Pipe main s27 A26 A27 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [VAR, P, LI]
      (AuCW.Pipe.binOp (h := hshl main) (a := QQI) (b := (p:ℤ)+(p:ℤ))
        (by exact Int.add_nonneg (Int.natCast_nonneg p) (Int.natCast_nonneg p)))) ?_
    exact AuCW.le_step3 (K := KSh) (a := isz (QQI)) (b := ((p:ℤ)+(p:ℤ)).toNat)
      (c := isz ((p:ℤ)+(p:ℤ))) hKShle hVDIisz h2pNatSz hV2pisz
  have e28 : AuCW.Pipe main s28 A27 A28 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A27) (k := 3)
      (by rw [show A27 = [VFI, VAR, P, LI] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 3) hKRle (by omega) ?_ hSEL1
    rw [show A27.take 4 = [VFI, VAR, P, LI] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e29 : AuCW.Pipe main s29 A28 A29 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [VAR, P]
      (AuCW.Pipe.binOp (h := hadd main) (a := lo_i) (b := FI) trivial)) ?_
    exact AuCW.le_step2 (K := KAd) (a := isz (lo_i)) (b := isz (FI)) hKAdle hLIisz hVFIisz
  have e30 : AuCW.Pipe main s30 A29 A30 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.rw (AuCW.Pipe.roll main hroll (A := A29) (k := 2)
      (by rw [show A29 = [VGI, VAR, P] from rfl]; simp)) (by rfl)) ?_
    refine AuCW.le_step_mover (K := KR) (k := 2) hKRle (by omega) ?_ hSEL1
    rw [show A29.take 3 = [VGI, VAR, P] from rfl]
    simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e31 : AuCW.Pipe main s31 A30 A31 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [VAR]
      (AuCW.Pipe.swap main hswap P VGI)) ?_
    exact AuCW.le_step3 (K := KSw) (a := vsz P) (b := vsz VGI) (c := 1)
      hKSwle hPv hVGIv hSEL1
  have e32 : AuCW.Pipe main s32 A31 A32 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail [VAR]
      (AuCW.Pipe.binOp (h := hshr main) (a := GI) (b := (p:ℤ))
        (by exact Int.natCast_nonneg p))) ?_
    exact AuCW.le_step2 (K := KSr) (a := isz (GI)) (b := isz ((p:ℤ))) hKSrle hVGIisz hPisz
  have e33 : AuCW.Pipe main s33 A32 A33 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail []
      (AuCW.Pipe.swap main hswap VAI VAR)) ?_
    exact AuCW.le_step3 (K := KSw) (a := vsz VAI) (b := vsz VAR) (c := 1)
      hKSwle hVAIv hVARv hSEL1
  have e34 : AuCW.Pipe main s34 A33 A34 STEP := by
    refine AuCW.Pipe.le (AuCW.Pipe.appendTail []
      (AuCW.Pipe.consV main hcons VAR VAI)) ?_
    exact AuCW.le_step_c (K := KCo) hKCole hSEL1
  have c1 : AuCW.Pipe main Q1 A0 A1 STEP := e1
  have c2 : AuCW.Pipe main Q2 A0 A2 (2 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c1 e2) (by omega)
  have c3 : AuCW.Pipe main Q3 A0 A3 (3 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c2 e3) (by omega)
  have c4 : AuCW.Pipe main Q4 A0 A4 (4 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c3 e4) (by omega)
  have c5 : AuCW.Pipe main Q5 A0 A5 (5 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c4 e5) (by omega)
  have c6 : AuCW.Pipe main Q6 A0 A6 (6 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c5 e6) (by omega)
  have c7 : AuCW.Pipe main Q7 A0 A7 (7 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c6 e7) (by omega)
  have c8 : AuCW.Pipe main Q8 A0 A8 (8 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c7 e8) (by omega)
  have c9 : AuCW.Pipe main Q9 A0 A9 (9 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c8 e9) (by omega)
  have c10 : AuCW.Pipe main Q10 A0 A10 (10 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c9 e10) (by omega)
  have c11 : AuCW.Pipe main Q11 A0 A11 (11 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c10 e11) (by omega)
  have c12 : AuCW.Pipe main Q12 A0 A12 (12 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c11 e12) (by omega)
  have c13 : AuCW.Pipe main Q13 A0 A13 (13 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c12 e13) (by omega)
  have c14 : AuCW.Pipe main Q14 A0 A14 (14 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c13 e14) (by omega)
  have c15 : AuCW.Pipe main Q15 A0 A15 (15 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c14 e15) (by omega)
  have c16 : AuCW.Pipe main Q16 A0 A16 (16 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c15 e16) (by omega)
  have c17 : AuCW.Pipe main Q17 A0 A17 (17 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c16 e17) (by omega)
  have c18 : AuCW.Pipe main Q18 A0 A18 (18 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c17 e18) (by omega)
  have c19 : AuCW.Pipe main Q19 A0 A19 (19 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c18 e19) (by omega)
  have c20 : AuCW.Pipe main Q20 A0 A20 (20 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c19 e20) (by omega)
  have c21 : AuCW.Pipe main Q21 A0 A21 (21 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c20 e21) (by omega)
  have c22 : AuCW.Pipe main Q22 A0 A22 (22 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c21 e22) (by omega)
  have c23 : AuCW.Pipe main Q23 A0 A23 (23 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c22 e23) (by omega)
  have c24 : AuCW.Pipe main Q24 A0 A24 (24 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c23 e24) (by omega)
  have c25 : AuCW.Pipe main Q25 A0 A25 (25 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c24 e25) (by omega)
  have c26 : AuCW.Pipe main Q26 A0 A26 (26 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c25 e26) (by omega)
  have c27 : AuCW.Pipe main Q27 A0 A27 (27 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c26 e27) (by omega)
  have c28 : AuCW.Pipe main Q28 A0 A28 (28 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c27 e28) (by omega)
  have c29 : AuCW.Pipe main Q29 A0 A29 (29 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c28 e29) (by omega)
  have c30 : AuCW.Pipe main Q30 A0 A30 (30 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c29 e30) (by omega)
  have c31 : AuCW.Pipe main Q31 A0 A31 (31 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c30 e31) (by omega)
  have c32 : AuCW.Pipe main Q32 A0 A32 (32 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c31 e32) (by omega)
  have c33 : AuCW.Pipe main Q33 A0 A33 (33 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c32 e33) (by omega)
  have c34 : AuCW.Pipe main Q34 A0 A34 (34 * STEP) :=
    AuCW.Pipe.le (AuCW.Pipe.comp c33 e34) (by omega)
  have hAr : AR = Work.Resample.awAns p lo_r Cr L := by
    show Int.tdiv (lo_r + (((Cr + Cr) - L) * (2:ℤ) ^ (((p:ℤ)+(p:ℤ)).toNat)))
      (2 ^ ((p:ℤ).toNat)) = Work.Resample.awAns p lo_r Cr L
    rw [Work.Resample.awAns, Work.Resample.awSh, h2pNat, hpNat]
    congr 1
    ring
  have hAi : AI = Work.Resample.awAns p lo_i Ci L := by
    show Int.tdiv (lo_i + (((Ci + Ci) - L) * (2:ℤ) ^ (((p:ℤ)+(p:ℤ)).toNat)))
      (2 ^ ((p:ℤ).toNat)) = Work.Resample.awAns p lo_i Ci L
    rw [Work.Resample.awAns, Work.Resample.awSh, h2pNat, hpNat]
    congr 1
    ring
  have hB : A34 = [HvdH.cfxVal (Work.Resample.awAns p lo_r Cr L, Work.Resample.awAns p lo_i Ci L)] := by
    have h1 : VCX = HvdH.cfxVal (Work.Resample.awAns p lo_r Cr L, Work.Resample.awAns p lo_i Ci L) := by
      show HvdH.Val.cons (.int AR) (.int AI)
        = HvdH.cfxVal (Work.Resample.awAns p lo_r Cr L, Work.Resample.awAns p lo_i Ci L)
      rw [hAr, hAi]
      rfl
    show [VCX] = [HvdH.cfxVal (Work.Resample.awAns p lo_r Cr L, Work.Resample.awAns p lo_i Ci L)]
    rw [h1]
  have hSELle : SEL ≤ 120 * ((p + 1) * (L.toNat + 1)) := by
    show 10 * p + 10 * L.natAbs + 100 ≤ 120 * ((p + 1) * (L.toNat + 1))
    rw [hLabs]
    have hB1 : 1 ≤ (p + 1) * (L.toNat + 1) := by
      have h := Nat.mul_le_mul (show 1 ≤ p + 1 by omega) (show 1 ≤ L.toNat + 1 by omega)
      simpa using h
    have hp1 : p ≤ (p + 1) * (L.toNat + 1) := by
      have h := Nat.mul_le_mul (show p ≤ p + 1 by omega) (show 1 ≤ L.toNat + 1 by omega)
      simpa using h
    have hL1 : L.toNat ≤ (p + 1) * (L.toNat + 1) := by
      have h := Nat.mul_le_mul (show 1 ≤ p + 1 by omega) (show L.toNat ≤ L.toNat + 1 by omega)
      simpa using h
    have h100 : 100 ≤ 100 * ((p + 1) * (L.toNat + 1)) := by
      have h := Nat.mul_le_mul_left 100 hB1
      simpa using h
    calc 10 * p + 10 * L.toNat + 100
        ≤ 10 * ((p+1)*(L.toNat+1)) + 10 * ((p+1)*(L.toNat+1)) + 100 * ((p+1)*(L.toNat+1)) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 10 hp1) (Nat.mul_le_mul_left 10 hL1)) h100
      _ = 120 * ((p+1)*(L.toNat+1)) := by ring
  have hcost : 34 * STEP ≤ 10000000 * KS * (p + 1) * (L.toNat + 1) := by
    have hKSx : KS * SEL ≤ KS * (120 * ((p+1)*(L.toNat+1))) := Nat.mul_le_mul_left KS hSELle
    have h34 : 34 * (1000 * (KS * SEL)) ≤
        34 * (1000 * (KS * (120 * ((p+1)*(L.toNat+1))))) :=
      Nat.mul_le_mul_left 34 (Nat.mul_le_mul_left 1000 hKSx)
    calc 34 * STEP
        = 34 * (1000 * (KS * SEL)) := by rw [show STEP = 1000 * KS * SEL from rfl]; ring
      _ ≤ 34 * (1000 * (KS * (120 * ((p+1)*(L.toNat+1))))) := h34
      _ = 4080000 * KS * (p+1) * (L.toNat+1) := by ring
      _ ≤ 10000000 * KS * (p+1) * (L.toNat+1) := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_))
          norm_num
  exact (AuCW.Pipe.rw (AuCW.Pipe.le c34 hcost) hB) (Work.Resample.auPvals p α s t ++ rest)



end Work.Resample
