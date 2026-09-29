import Mathlib
import Submission.HvdH.Interfaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Main.word

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## Sizes of encoded values -/

theorem encodePosNum_length (q : PosNum) : (Computability.encodePosNum q).length = q.natSize := by
  induction q with
  | one => rfl
  | bit0 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]
  | bit1 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]

theorem encodeNum_length (x : Num) : (Computability.encodeNum x).length = x.natSize := by
  cases x with
  | zero => rfl
  | pos q => exact encodePosNum_length q

theorem castNum_ofNat'_nat (n : ℕ) : ((Num.ofNat' n : Num) : ℕ) = n := by simp

theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  change (Computability.encodeNum (Num.ofNat' n)).length = n.size
  rw [encodeNum_length, Num.natSize_to_nat, castNum_ofNat'_nat]


theorem vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  show ((if z < 0 then Glyph.neg else Glyph.pos) ::
    ((Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend])).length = isz z
  rw [List.length_cons, List.length_append, List.length_map, List.length_singleton,
    encodeNat_length, isz]

theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (Glyph.cons :: (a.enc ++ b.enc)).length = a.enc.length + b.enc.length + 1
  rw [List.length_cons, List.length_append]

theorem isz_le_of_natAbs_le {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ p + 3 := by
  have h1 : z.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
  simp only [isz]
  omega

/-- Total encoding size of a window of values. -/
def szl (l : List Val) : ℕ := (l.map vsz).sum

/-! ## `Pipe`: words acting on a fixed window of values -/

/-- `Pipe main prog A B c` is a `WordR` spec for a word that transforms the fixed window `A` of
values at the top of the value stack into the fixed window `B`, leaving everything below untouched,
at cost `≤ c`. -/
def Pipe (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val,
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c)

theorem Pipe.le {main prog : Cmd} {A B : List Val} {c c' : ℕ} (h : Pipe main prog A B c)
    (hc : c ≤ c') : Pipe main prog A B c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, le_trans hn hc, hstk, hoth⟩

theorem Pipe.rw {main prog : Cmd} {A B B' : List Val} {c : ℕ} (h : Pipe main prog A B c)
    (hB : B = B') : Pipe main prog A B' c := by
  subst hB; exact h

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

/-! ## List and value helpers -/

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

/-! ## Adapters from the libraries to `Pipe` -/

theorem Pipe.pushValAny {main prog : Cmd} {v : Val} {c : ℕ} {T : List Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => c)) :
    Pipe main prog T (v :: T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hvs]; rfl, hev, hn, hstk, hoth⟩

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

theorem Pipe.pick {pickP : ℕ → Cmd} {KP : ℕ}
    (main : Cmd) (h : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => KP * (k + 1) * (szl (vs.take (k + 1)) + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (pickP k) A (A.getD k .nil :: A) (KP * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ KP * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have h1 : n ≤ KP * (k + 1) * (szl (vs.take (k + 1)) + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h1
    exact h1
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, ← List.cons_append]

theorem Pipe.roll {rollP : ℕ → Cmd} {KR : ℕ}
    (main : Cmd) (h : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (szl (vs.take (k + 1)) + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (rollP k) A (A.getD k .nil :: A.eraseIdx k)
      (KR * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ KR * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have h1 : n ≤ KR * (k + 1) * (szl (vs.take (k + 1)) + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h1
    exact h1
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, eraseIdx_append_of_lt hk, ← List.cons_append]

/-! ## The word -/

/-- `toCfxElem`: from `int n :: int p :: int b :: rest` (`b ≤ p`, `n < 2^b`) produce the
fixed-point complex value `cfxVal (n * 2^(p-b), 0)` above `int p :: int b :: rest`. -/
theorem toCfxElem (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p b n : ℕ) (rest : List HvdH.Val),
      b ≤ p → n < 2 ^ b →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (n : ℤ) :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (b : ℤ) :: rest)
        (fun _ out => out = HvdH.cfxVal (((n : ℤ) * 2 ^ (p - b)), 0) ::
          HvdH.Val.int (p : ℤ) :: HvdH.Val.int (b : ℤ) :: rest)
        (fun _ => K * (p + 1) + K) := by
  obtain ⟨pickP, KP, hpick⟩ := hKer.pick
  obtain ⟨rollP, KR, hroll⟩ := hKer.roll
  obtain ⟨pushP, Kpush, hpush⟩ := hKer.pushVal
  obtain ⟨consP, Kcons, hcons⟩ := hKer.consV
  obtain ⟨subP, Ksub, hsub⟩ := hInt.sub
  obtain ⟨shlP, Ksh, hshl⟩ := hInt.shl
  refine ⟨pickP 2 ;;; pickP 2 ;;; subP ;;; rollP 1 ;;; shlP ;;; pushP (Val.int 0) ;;; rollP 1 ;;; consP,
    120 * (KP + KR + Kpush + Kcons + Ksub + Ksh + 1), ?_⟩
  intro main p b n rest hbp hnb
  -- size facts
  have hszn : isz (n:ℤ) ≤ p + 3 := by
    refine isz_le_of_natAbs_le ?_
    rw [Int.natAbs_natCast]
    exact le_of_lt (lt_of_lt_of_le hnb (Nat.pow_le_pow_right (by norm_num) hbp))
  have hszp : isz (p:ℤ) ≤ p + 3 := by
    refine isz_le_of_natAbs_le ?_
    rw [Int.natAbs_natCast]
    exact le_of_lt Nat.lt_two_pow_self
  have hszb : isz (b:ℤ) ≤ p + 3 := by
    refine isz_le_of_natAbs_le ?_
    rw [Int.natAbs_natCast]
    exact le_trans hbp (le_of_lt Nat.lt_two_pow_self)
  have hk_nat : ((p:ℤ) - (b:ℤ)).toNat = p - b := by
    rw [← Nat.cast_sub hbp, Int.toNat_natCast]
  have hszkv : isz ((p:ℤ) - (b:ℤ)) ≤ p + 3 := by
    refine isz_le_of_natAbs_le ?_
    have h1 : ((p:ℤ) - (b:ℤ)).natAbs = p - b := by
      rw [← Nat.cast_sub hbp, Int.natAbs_natCast]
    rw [h1]
    exact le_of_lt (lt_of_le_of_lt (Nat.sub_le p b) Nat.lt_two_pow_self)
  have hZ : (n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat) = (n:ℤ) * 2 ^ (p - b) := by rw [hk_nat]
  have hszz : isz ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)) ≤ p + 3 := by
    refine isz_le_of_natAbs_le ?_
    have h1 : (n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat) = ((n * 2 ^ (p - b) : ℕ) : ℤ) := by
      rw [hZ]; push_cast; ring
    rw [h1, Int.natAbs_natCast]
    have h2 : n * 2 ^ (p - b) < 2 ^ p := by
      have h3 : 2 ^ b * 2 ^ (p - b) = 2 ^ p := by rw [← pow_add]; congr 1; omega
      calc n * 2 ^ (p - b) < 2 ^ b * 2 ^ (p - b) :=
            Nat.mul_lt_mul_of_pos_right hnb (pow_pos (by norm_num) _)
        _ = 2 ^ p := h3
    exact le_of_lt h2
  have hpre : (0:ℤ) ≤ (p:ℤ) - (b:ℤ) := sub_nonneg.mpr (by exact_mod_cast hbp)
  -- step 1: copy `b` to the front
  have H1 : Pipe main (pickP 2) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int (b:ℤ), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1)) :=
    Pipe.le (Pipe.rw (Pipe.pick main hpick (A := [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)]) (k := 2) (by simp)) (by simp)) (by
      have hszl : szl (([Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] : List Val).take (2 + 1)) = isz (n:ℤ) + isz (p:ℤ) + isz (b:ℤ) := by
        simp [szl, vsz_int]; omega
      rw [hszl]
      have hs : isz (n:ℤ) + isz (p:ℤ) + isz (b:ℤ) + 1 ≤ 13 * (p + 1) := by omega
      calc KP * (2 + 1) * (isz (n:ℤ) + isz (p:ℤ) + isz (b:ℤ) + 1)
          ≤ KP * (2 + 1) * (13 * (p + 1)) := Nat.mul_le_mul_left (KP * (2 + 1)) hs
        _ = 39 * KP * (p + 1) := by ring)
  -- step 2: copy `p` to the front
  have H2 : Pipe main (pickP 2) [Val.int (b:ℤ), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int (p:ℤ), Val.int (b:ℤ), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1)) :=
    Pipe.le (Pipe.rw (Pipe.pick main hpick (A := [Val.int (b:ℤ), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)]) (k := 2) (by simp)) (by simp)) (by
      have hszl : szl (([Val.int (b:ℤ), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] : List Val).take (2 + 1)) = isz (b:ℤ) + isz (n:ℤ) + isz (p:ℤ) := by
        simp [szl, vsz_int]; omega
      rw [hszl]
      have hs : isz (b:ℤ) + isz (n:ℤ) + isz (p:ℤ) + 1 ≤ 13 * (p + 1) := by omega
      calc KP * (2 + 1) * (isz (b:ℤ) + isz (n:ℤ) + isz (p:ℤ) + 1)
          ≤ KP * (2 + 1) * (13 * (p + 1)) := Nat.mul_le_mul_left (KP * (2 + 1)) hs
        _ = 39 * KP * (p + 1) := by ring)
  -- step 3: `p - b`
  have H3 : Pipe main subP [Val.int (p:ℤ), Val.int (b:ℤ), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int ((p:ℤ) - (b:ℤ)), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] (6 * Ksub * (p + 1)) := by
    refine Pipe.le (Pipe.appendTail [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)]
      (Pipe.binOp (h := hsub main) (a := (p:ℤ)) (b := (b:ℤ)) trivial)) ?_
    have hs : isz (p:ℤ) + isz (b:ℤ) ≤ 6 * (p + 1) := by omega
    calc Ksub * (isz (p:ℤ) + isz (b:ℤ)) ≤ Ksub * (6 * (p + 1)) := Nat.mul_le_mul_left Ksub hs
      _ = 6 * Ksub * (p + 1) := by ring
  -- step 4: bring `n` to the front
  have H4 : Pipe main (rollP 1) [Val.int ((p:ℤ) - (b:ℤ)), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int (n:ℤ), Val.int ((p:ℤ) - (b:ℤ)), Val.int (p:ℤ), Val.int (b:ℤ)] (14 * KR * (p + 1)) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int ((p:ℤ) - (b:ℤ)), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)]) (k := 1) (by simp)) (by simp)) (by
      have hszl : szl (([Val.int ((p:ℤ) - (b:ℤ)), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] : List Val).take (1 + 1)) = isz ((p:ℤ) - (b:ℤ)) + isz (n:ℤ) := by
        simp [szl, vsz_int]
      rw [hszl]
      have hs : isz ((p:ℤ) - (b:ℤ)) + isz (n:ℤ) + 1 ≤ 7 * (p + 1) := by omega
      calc KR * (1 + 1) * (isz ((p:ℤ) - (b:ℤ)) + isz (n:ℤ) + 1)
          ≤ KR * (1 + 1) * (7 * (p + 1)) := Nat.mul_le_mul_left (KR * (1 + 1)) hs
        _ = 14 * KR * (p + 1) := by ring)
  -- step 5: `n * 2^(p-b)`
  have H5 : Pipe main shlP [Val.int (n:ℤ), Val.int ((p:ℤ) - (b:ℤ)), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)] (6 * Ksh * (p + 1)) := by
    refine Pipe.le (Pipe.appendTail [Val.int (p:ℤ), Val.int (b:ℤ)]
      (Pipe.binOp (h := hshl main) (a := (n:ℤ)) (b := (p:ℤ) - (b:ℤ)) hpre)) ?_
    have hle : ((p:ℤ) - (b:ℤ)).toNat ≤ p := by rw [hk_nat]; omega
    have hs : isz (n:ℤ) + ((p:ℤ) - (b:ℤ)).toNat + isz ((p:ℤ) - (b:ℤ)) ≤ 6 * (p + 1) := by omega
    calc Ksh * (isz (n:ℤ) + ((p:ℤ) - (b:ℤ)).toNat + isz ((p:ℤ) - (b:ℤ)))
        ≤ Ksh * (6 * (p + 1)) := Nat.mul_le_mul_left Ksh hs
      _ = 6 * Ksh * (p + 1) := by ring
  -- step 6: push the imaginary part `0`
  have H6 : Pipe main (pushP (Val.int 0)) [Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int 0, Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)] (3 * Kpush * (p + 1)) := by
    refine Pipe.le (Pipe.pushValAny (hpush main (Val.int 0))) ?_
    have h3 : vsz (Val.int (0:ℤ)) + 1 = 3 := by simp [vsz_int, isz]
    calc Kpush * (vsz (Val.int (0:ℤ)) + 1) = 3 * Kpush := by rw [h3]; ring
      _ = 3 * Kpush * 1 := by ring
      _ ≤ 3 * Kpush * (p + 1) := Nat.mul_le_mul_left (3 * Kpush) (by omega)
  -- step 7: bring `Z` back to the front
  have H7 : Pipe main (rollP 1) [Val.int 0, Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int 0, Val.int (p:ℤ), Val.int (b:ℤ)] (12 * KR * (p + 1)) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int 0, Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)]) (k := 1) (by simp)) (by simp)) (by
      have hszl : szl (([Val.int 0, Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)] : List Val).take (1 + 1))
          = isz (0:ℤ) + isz ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)) := by
        simp [szl, vsz_int]
      rw [hszl]
      have h0 : isz (0:ℤ) = 2 := by simp [isz]
      rw [h0]
      have hs : 2 + isz ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)) + 1 ≤ 6 * (p + 1) := by omega
      calc KR * (1 + 1) * (2 + isz ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)) + 1)
          ≤ KR * (1 + 1) * (6 * (p + 1)) := Nat.mul_le_mul_left (KR * (1 + 1)) hs
        _ = 12 * KR * (p + 1) := by ring)
  -- step 8: build the complex fixed-point value
  have H8 : Pipe main consP [Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int 0, Val.int (p:ℤ), Val.int (b:ℤ)] [HvdH.cfxVal (((n:ℤ) * 2 ^ (p - b)), 0), Val.int (p:ℤ), Val.int (b:ℤ)] (Kcons * (p + 1)) := by
    refine Pipe.le (Pipe.rw (Pipe.appendTail [Val.int (p:ℤ), Val.int (b:ℤ)]
      (Pipe.consV main hcons
        (Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat))) (Val.int 0))) (by
        rw [hZ]
        rfl)) ?_
    calc Kcons = Kcons * 1 := by ring
      _ ≤ Kcons * (p + 1) := Nat.mul_le_mul_left Kcons (by omega)
  -- compose
  have h12 : Pipe main (pickP 2 ;;; pickP 2) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int (p:ℤ), Val.int (b:ℤ), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1) + 39 * KP * (p + 1)) :=
    Pipe.comp H1 H2
  have h123 : Pipe main (pickP 2 ;;; pickP 2 ;;; subP) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int ((p:ℤ) - (b:ℤ)), Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1)) :=
    Pipe.comp h12 H3
  have h1234 : Pipe main (pickP 2 ;;; pickP 2 ;;; subP ;;; rollP 1) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int (n:ℤ), Val.int ((p:ℤ) - (b:ℤ)), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1) + 14 * KR * (p + 1)) :=
    Pipe.comp h123 H4
  have h12345 : Pipe main (pickP 2 ;;; pickP 2 ;;; subP ;;; rollP 1 ;;; shlP) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1) + 14 * KR * (p + 1) + 6 * Ksh * (p + 1)) :=
    Pipe.comp h1234 H5
  have h123456 : Pipe main (pickP 2 ;;; pickP 2 ;;; subP ;;; rollP 1 ;;; shlP ;;; pushP (Val.int 0)) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int 0, Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1) + 14 * KR * (p + 1) + 6 * Ksh * (p + 1) + 3 * Kpush * (p + 1)) :=
    Pipe.comp h12345 H6
  have h1234567 : Pipe main (pickP 2 ;;; pickP 2 ;;; subP ;;; rollP 1 ;;; shlP ;;; pushP (Val.int 0) ;;; rollP 1) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [Val.int ((n:ℤ) * 2 ^ (((p:ℤ) - (b:ℤ)).toNat)), Val.int 0, Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1) + 14 * KR * (p + 1) + 6 * Ksh * (p + 1) + 3 * Kpush * (p + 1) + 12 * KR * (p + 1)) :=
    Pipe.comp h123456 H7
  have hAll : Pipe main (pickP 2 ;;; pickP 2 ;;; subP ;;; rollP 1 ;;; shlP ;;; pushP (Val.int 0) ;;; rollP 1 ;;; consP) [Val.int (n:ℤ), Val.int (p:ℤ), Val.int (b:ℤ)] [HvdH.cfxVal (((n:ℤ) * 2 ^ (p - b)), 0), Val.int (p:ℤ), Val.int (b:ℤ)] (39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1) + 14 * KR * (p + 1) + 6 * Ksh * (p + 1) + 3 * Kpush * (p + 1) + 12 * KR * (p + 1) + Kcons * (p + 1)) :=
    Pipe.comp h1234567 H8
  -- cost
  have hcoef : 39 * KP + 39 * KP + 6 * Ksub + 14 * KR + 6 * Ksh + 3 * Kpush + 12 * KR + Kcons
      ≤ 120 * (KP + KR + Kpush + Kcons + Ksub + Ksh + 1) := by omega
  have hcost : 39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1) + 14 * KR * (p + 1)
      + 6 * Ksh * (p + 1) + 3 * Kpush * (p + 1) + 12 * KR * (p + 1) + Kcons * (p + 1)
      ≤ 120 * (KP + KR + Kpush + Kcons + Ksub + Ksh + 1) * (p + 1) := by
    calc 39 * KP * (p + 1) + 39 * KP * (p + 1) + 6 * Ksub * (p + 1) + 14 * KR * (p + 1)
          + 6 * Ksh * (p + 1) + 3 * Kpush * (p + 1) + 12 * KR * (p + 1) + Kcons * (p + 1)
        = (39 * KP + 39 * KP + 6 * Ksub + 14 * KR + 6 * Ksh + 3 * Kpush + 12 * KR + Kcons) * (p + 1) := by
          ring
      _ ≤ 120 * (KP + KR + Kpush + Kcons + Ksub + Ksh + 1) * (p + 1) :=
          Nat.mul_le_mul_right _ hcoef
  refine (Pipe.le hAll (le_trans hcost (Nat.le_add_right _ _))) rest

end Work.Main.word
