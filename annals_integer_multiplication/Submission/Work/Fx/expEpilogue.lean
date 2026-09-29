import Mathlib
import Submission.Work.Fx.ExpDefs


set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- The input window of the epilogue word (top first). -/
def epiWin (Qre Qim dd Zs Zt Pow : ℤ) (d0 : ℕ) : List Val :=
  [.int Qre, .int Qim, .int dd, .int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]

/-- Linear size budget of the epilogue window. -/
def epiSz (Qre Qim dd Zs Zt Pow : ℤ) (d0 : ℕ) : ℕ :=
  isz Qre + isz Qim + isz dd + isz Zs + isz Zt + isz Pow + isz (d0 : ℤ)

/-- The value `tdiv Qre (2^d0)`. -/
def epiR (Qre : ℤ) (d0 : ℕ) : Val := .int (Int.tdiv Qre ((2 : ℤ) ^ d0))

/-- The value `tdiv Qim (2^d0)`. -/
def epiQ (Qim : ℤ) (d0 : ℕ) : Val := .int (Int.tdiv Qim ((2 : ℤ) ^ d0))

theorem szl_epiWin (Qre Qim dd Zs Zt Pow : ℤ) (d0 : ℕ) :
    szl (epiWin Qre Qim dd Zs Zt Pow d0) = epiSz Qre Qim dd Zs Zt Pow d0 := by
  simp [epiWin, epiSz, szl_cons, szl_nil, vsz_int, Nat.add_assoc]

theorem vsz_epiR (Qre : ℤ) (d0 : ℕ) :
    vsz (epiR Qre d0) = isz (Int.tdiv Qre ((2 : ℤ) ^ d0)) := by
  simp [epiR, vsz_int]

theorem vsz_epiQ (Qim : ℤ) (d0 : ℕ) :
    vsz (epiQ Qim d0) = isz (Int.tdiv Qim ((2 : ℤ) ^ d0)) := by
  simp [epiQ, vsz_int]


/-! ## A minimal "window pipe" layer (self-contained)

`Win main prog A B c` is a `WordR` spec for a word that rewrites the fixed window `A` (on top of an
arbitrary list of values) into the fixed window `B`, at cost at most `c`.  This is the shape in which
the library words (`roll`, `dup`, `drop`, `swap`, the fixed-point shifts) are chained below.
-/

def Win (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val,
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c)

theorem Win.le {main prog : Cmd} {A B : List Val} {c c' : ℕ} (h : Win main prog A B c)
    (hc : c ≤ c') : Win main prog A B c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, le_trans hn hc, hstk, hoth⟩

theorem Win.comp {main p q : Cmd} {A B D : List Val} {c d : ℕ} (h1 : Win main p A B c)
    (h2 : Win main q B D d) : Win main (.seq p q) A D (c + d) := by
  intro rest vs hvs s R hR
  obtain ⟨mid, s', n1, hmid, hev1, hn1, hstk1, hoth1⟩ := h1 rest vs hvs s R hR
  obtain ⟨out, s'', n2, hout, hev2, hn2, hstk2, hoth2⟩ := h2 rest mid hmid s' R hstk1
  exact ⟨out, s'', n1 + n2, hout, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem Win.appendTail {main prog : Cmd} {A B : List Val} {c : ℕ} (T : List Val)
    (h : Win main prog A B c) : Win main prog (A ++ T) (B ++ T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    h (T ++ rest) vs (by rw [hvs, List.append_assoc]) s R
      (by simpa only [hvs, List.append_assoc] using hR)
  exact ⟨out, s', n, by rw [hout, List.append_assoc], hev, hn, hstk, hoth⟩

theorem Win.binOp {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) :
    Win main prog [.int a, .int b] [.int (f a b)] (C a b) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: .int b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, b, rest, hv2, hab⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := int_cons_inj3 (hvs'.symm.trans hv2)
  have hn' : n ≤ C a b := by rw [hv2] at hn; exact hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem Win.swap {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) : Win main prog [a, b] [b, a] (K * (vsz a + vsz b + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + vsz b + 1) := by
    rw [hv2] at hn
    simpa only [List.getD_cons_zero, List.getD_cons_succ] using hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem Win.drop {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Win main prog [a] [] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Win.dup {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Win main prog [a] [a, a] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.1, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem szl_take_le' (A : List Val) (m : ℕ) : szl (A.take m) ≤ szl A := by
  have h := szl_append (A.take m) (A.drop m)
  rw [List.take_append_drop] at h
  omega

theorem Win.roll {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Win main (prog k) A (A.getD k .nil :: A.eraseIdx k)
      (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have h' : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h'
    simpa [szl] using h'
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, eraseIdx_append_of_lt hk, List.cons_append]

/-- Window renaming for `Win`. -/
theorem Win.castWin {main prog : Cmd} {A A' B B' : List Val} {c : ℕ} (hA : A = A')
    (hB : B = B') (h : Win main prog A B c) : Win main prog A' B' c := by
  rw [← hA, ← hB]; exact h

theorem cost_roll3 {K X Y : ℕ} (h : X ≤ 3 * Y) : K * (2 + 1) * (X + 1) ≤ 9 * K * (Y + 1) := by
  nlinarith

theorem cost_one {K X Y : ℕ} (h : X ≤ Y) : K * (X + 1) ≤ K * (Y + 1) := by nlinarith

theorem cost_swap2 {K A B Y : ℕ} (hA : A ≤ Y) (hB : B ≤ Y) :
    K * (A + B + 1) ≤ 2 * K * (Y + 1) := by nlinarith

theorem cost_shr2 {K A B Y : ℕ} (hA : A ≤ Y) (hB : B ≤ Y) : K * (A + B) ≤ 2 * K * (Y + 1) := by
  nlinarith

set_option maxHeartbeats 4000000 in
theorem expEpilogue (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (d0 : ℕ) (Qre Qim dd Zs Zt Pow : ℤ),
      Spec main prog 7
        (fun t => t = [HvdH.Val.int Qre, HvdH.Val.int Qim, HvdH.Val.int dd, HvdH.Val.int Zs,
          HvdH.Val.int Zt, HvdH.Val.int Pow, HvdH.Val.int (d0 : ℤ)])
        (fun t o => o = [HvdH.Val.int (Int.tdiv Qre ((2 : ℤ) ^ d0)),
          HvdH.Val.int (Int.tdiv Qim ((2 : ℤ) ^ d0))])
        (fun t => K * (szl t + 1) ^ K) := by
  obtain ⟨rprog, rK, hroll⟩ := hk.roll
  obtain ⟨dprog, dK, hdup⟩ := hk.dup
  obtain ⟨wprog, wK, hswap⟩ := hk.swap
  obtain ⟨pprog, pK, hdrop⟩ := hk.drop
  obtain ⟨sprog, sK, hshr⟩ := hi.shrT
  let PROG : Cmd := Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (rprog 2) (pprog)) (rprog 2)) (pprog)) (rprog 2)) (pprog)) (rprog 2)) (pprog)) (wprog)) (rprog 2)) (dprog)) (rprog 2)) (sprog)) (rprog 2)) (rprog 2)) (wprog)) (sprog)
  refine ⟨PROG, 72 * rK + 5 * pK + dK + 4 * wK + 4 * sK + 1, ?_⟩
  intro main d0 Qre Qim dd Zs Zt Pow
  let sA : ℕ := epiSz Qre Qim dd Zs Zt Pow d0
  have hsA : epiSz Qre Qim dd Zs Zt Pow d0 = sA := rfl
  have hsA' : sA = isz Qre + isz Qim + isz dd + isz Zs + isz Zt + isz Pow + isz (d0 : ℤ) := rfl
  have hQre : isz Qre ≤ sA := by rw [hsA']; omega
  have hQim : isz Qim ≤ sA := by rw [hsA']; omega
  have hdd : isz dd ≤ sA := by rw [hsA']; omega
  have hZs : isz Zs ≤ sA := by rw [hsA']; omega
  have hZt : isz Zt ≤ sA := by rw [hsA']; omega
  have hPow : isz Pow ≤ sA := by rw [hsA']; omega
  have hD : isz (d0 : ℤ) ≤ sA := by rw [hsA']; omega
  have hr : isz (Int.tdiv Qre ((2 : ℤ) ^ d0)) ≤ sA := le_trans (isz_tdiv_le _ _) hQre
  have hq : isz (Int.tdiv Qim ((2 : ℤ) ^ d0)) ≤ sA := le_trans (isz_tdiv_le _ _) hQim
  have szl1 : ∀ a : Val, vsz a ≤ sA → szl [a] ≤ sA := by
    intro a ha; simpa [szl_singleton] using ha
  have szl2 : ∀ a b : Val, vsz a ≤ sA → vsz b ≤ sA → szl [a, b] ≤ 2 * sA := by
    intro a b ha hb
    simp only [szl_cons, szl_nil, Nat.add_zero]
    omega
  have szl3 : ∀ a b c : Val, vsz a ≤ sA → vsz b ≤ sA → vsz c ≤ sA → szl [a, b, c] ≤ 3 * sA := by
    intro a b c ha hb hc
    simp only [szl_cons, szl_nil, Nat.add_zero]
    omega
  -- step 1: roll the third value (dd) to the top
  have h1 : Win main (rprog 2)
      [.int Qre, .int Qim, .int dd, .int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]
      [.int dd, .int Qre, .int Qim, .int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([.int Qre, .int Qim, .int dd] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_int]; exact hQre) (by simp only [vsz_int]; exact hQim)
        (by simp only [vsz_int]; exact hdd)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]
        (Win.roll hroll (A := [.int Qre, .int Qim, .int dd]) (k := 2) (by simp))) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 2: drop dd
  have h2 : Win main pprog
      [.int dd, .int Qre, .int Qim, .int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]
      [.int Qre, .int Qim, .int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]
      (pK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Qre, .int Qim, .int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]
        (Win.drop hdrop (.int dd))) ?_)
    exact cost_one (by simp only [vsz_int]; exact hdd)
  -- step 3
  have h3 : Win main (rprog 2)
      [.int Qre, .int Qim, .int Zs, .int Zt, .int Pow, .int (d0 : ℤ)]
      [.int Zs, .int Qre, .int Qim, .int Zt, .int Pow, .int (d0 : ℤ)]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([.int Qre, .int Qim, .int Zs] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_int]; exact hQre) (by simp only [vsz_int]; exact hQim)
        (by simp only [vsz_int]; exact hZs)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Zt, .int Pow, .int (d0 : ℤ)]
        (Win.roll hroll (A := [.int Qre, .int Qim, .int Zs]) (k := 2) (by simp))) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 4
  have h4 : Win main pprog
      [.int Zs, .int Qre, .int Qim, .int Zt, .int Pow, .int (d0 : ℤ)]
      [.int Qre, .int Qim, .int Zt, .int Pow, .int (d0 : ℤ)]
      (pK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Qre, .int Qim, .int Zt, .int Pow, .int (d0 : ℤ)]
        (Win.drop hdrop (.int Zs))) ?_)
    exact cost_one (by simp only [vsz_int]; exact hZs)
  -- step 5
  have h5 : Win main (rprog 2)
      [.int Qre, .int Qim, .int Zt, .int Pow, .int (d0 : ℤ)]
      [.int Zt, .int Qre, .int Qim, .int Pow, .int (d0 : ℤ)]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([.int Qre, .int Qim, .int Zt] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_int]; exact hQre) (by simp only [vsz_int]; exact hQim)
        (by simp only [vsz_int]; exact hZt)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Pow, .int (d0 : ℤ)]
        (Win.roll hroll (A := [.int Qre, .int Qim, .int Zt]) (k := 2) (by simp))) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 6
  have h6 : Win main pprog
      [.int Zt, .int Qre, .int Qim, .int Pow, .int (d0 : ℤ)]
      [.int Qre, .int Qim, .int Pow, .int (d0 : ℤ)]
      (pK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Qre, .int Qim, .int Pow, .int (d0 : ℤ)]
        (Win.drop hdrop (.int Zt))) ?_)
    exact cost_one (by simp only [vsz_int]; exact hZt)
  -- step 7
  have h7 : Win main (rprog 2)
      [.int Qre, .int Qim, .int Pow, .int (d0 : ℤ)]
      [.int Pow, .int Qre, .int Qim, .int (d0 : ℤ)]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([.int Qre, .int Qim, .int Pow] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_int]; exact hQre) (by simp only [vsz_int]; exact hQim)
        (by simp only [vsz_int]; exact hPow)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int (d0 : ℤ)]
        (Win.roll hroll (A := [.int Qre, .int Qim, .int Pow]) (k := 2) (by simp))) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 8
  have h8 : Win main pprog
      [.int Pow, .int Qre, .int Qim, .int (d0 : ℤ)]
      [.int Qre, .int Qim, .int (d0 : ℤ)]
      (pK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Qre, .int Qim, .int (d0 : ℤ)]
        (Win.drop hdrop (.int Pow))) ?_)
    exact cost_one (by simp only [vsz_int]; exact hPow)
  -- step 9: swap Qre and Qim
  have h9 : Win main wprog
      [.int Qre, .int Qim, .int (d0 : ℤ)]
      [.int Qim, .int Qre, .int (d0 : ℤ)]
      (2 * wK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int (d0 : ℤ)]
        (Win.swap hswap (.int Qre) (.int Qim))) ?_)
    exact cost_swap2 (by simp only [vsz_int]; exact hQre) (by simp only [vsz_int]; exact hQim)
  -- step 10: roll d0 to the top
  have h10 : Win main (rprog 2)
      [.int Qim, .int Qre, .int (d0 : ℤ)]
      [.int (d0 : ℤ), .int Qim, .int Qre]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([.int Qim, .int Qre, .int (d0 : ℤ)] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_int]; exact hQim) (by simp only [vsz_int]; exact hQre)
        (by simp only [vsz_int]; exact hD)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.roll hroll (A := [.int Qim, .int Qre, .int (d0 : ℤ)]) (k := 2) (by simp)) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 11: duplicate d0
  have h11 : Win main dprog
      [.int (d0 : ℤ), .int Qim, .int Qre]
      [.int (d0 : ℤ), .int (d0 : ℤ), .int Qim, .int Qre]
      (dK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Qim, .int Qre]
        (Win.dup hdup (.int (d0 : ℤ)))) ?_)
    exact cost_one (by simp only [vsz_int]; exact hD)
  -- step 12
  have h12 : Win main (rprog 2)
      [.int (d0 : ℤ), .int (d0 : ℤ), .int Qim, .int Qre]
      [.int Qim, .int (d0 : ℤ), .int (d0 : ℤ), .int Qre]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([.int (d0 : ℤ), .int (d0 : ℤ), .int Qim] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_int]; exact hD) (by simp only [vsz_int]; exact hD)
        (by simp only [vsz_int]; exact hQim)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [.int Qre]
        (Win.roll hroll (A := [.int (d0 : ℤ), .int (d0 : ℤ), .int Qim]) (k := 2) (by simp))) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 13: divide Qim by 2^d0
  have h13 : Win main sprog
      [.int Qim, .int (d0 : ℤ), .int (d0 : ℤ), .int Qre]
      [epiQ Qim d0, .int (d0 : ℤ), .int Qre]
      (2 * sK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rw [epiQ, Int.toNat_natCast]; rfl)
      (Win.le (Win.appendTail [.int (d0 : ℤ), .int Qre]
        (Win.binOp (hshr main) (a := Qim) (b := (d0 : ℤ)) (by exact Int.natCast_nonneg d0))) ?_)
    exact cost_shr2 hQim hD
  -- step 14
  have h14 : Win main (rprog 2)
      [epiQ Qim d0, .int (d0 : ℤ), .int Qre]
      [.int Qre, epiQ Qim d0, .int (d0 : ℤ)]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([epiQ Qim d0, .int (d0 : ℤ), .int Qre] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_epiQ]; exact hq) (by simp only [vsz_int]; exact hD)
        (by simp only [vsz_int]; exact hQre)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.roll hroll (A := [epiQ Qim d0, .int (d0 : ℤ), .int Qre]) (k := 2) (by simp)) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 15
  have h15 : Win main (rprog 2)
      [.int Qre, epiQ Qim d0, .int (d0 : ℤ)]
      [.int (d0 : ℤ), .int Qre, epiQ Qim d0]
      (9 * rK * (sA + 1)) := by
    have hsz : szl ([.int Qre, epiQ Qim d0, .int (d0 : ℤ)] : List Val) ≤ 3 * sA :=
      szl3 _ _ _ (by simp only [vsz_int]; exact hQre) (by simp only [vsz_epiQ]; exact hq)
        (by simp only [vsz_int]; exact hD)
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.roll hroll (A := [.int Qre, epiQ Qim d0, .int (d0 : ℤ)]) (k := 2) (by simp)) ?_)
    exact cost_roll3 (le_trans (szl_take_le' _ 3) hsz)
  -- step 16
  have h16 : Win main wprog
      [.int (d0 : ℤ), .int Qre, epiQ Qim d0]
      [.int Qre, .int (d0 : ℤ), epiQ Qim d0]
      (2 * wK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rfl)
      (Win.le (Win.appendTail [epiQ Qim d0]
        (Win.swap hswap (.int (d0 : ℤ)) (.int Qre))) ?_)
    exact cost_swap2 (by simp only [vsz_int]; exact hD) (by simp only [vsz_int]; exact hQre)
  -- step 17: divide Qre by 2^d0
  have h17 : Win main sprog
      [.int Qre, .int (d0 : ℤ), epiQ Qim d0]
      [epiR Qre d0, epiQ Qim d0]
      (2 * sK * (sA + 1)) := by
    refine Win.castWin (by rfl) (by rw [epiR, Int.toNat_natCast]; rfl)
      (Win.le (Win.appendTail [epiQ Qim d0]
        (Win.binOp (hshr main) (a := Qre) (b := (d0 : ℤ)) (by exact Int.natCast_nonneg d0))) ?_)
    exact cost_shr2 hQre hD
  have p2 := Win.comp h1 h2
  have p3 := Win.comp p2 h3
  have p4 := Win.comp p3 h4
  have p5 := Win.comp p4 h5
  have p6 := Win.comp p5 h6
  have p7 := Win.comp p6 h7
  have p8 := Win.comp p7 h8
  have p9 := Win.comp p8 h9
  have p10 := Win.comp p9 h10
  have p11 := Win.comp p10 h11
  have p12 := Win.comp p11 h12
  have p13 := Win.comp p12 h13
  have p14 := Win.comp p13 h14
  have p15 := Win.comp p14 h15
  have p16 := Win.comp p15 h16
  have p17 := Win.comp p16 h17
  intro top rest ht hP
  have htop : top = epiWin Qre Qim dd Zs Zt Pow d0 := by rw [hP]; rfl
  rw [htop]
  intro vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := p17 rest vs hvs s R hR
  refine ⟨out, s', n, ⟨[epiR Qre d0, epiQ Qim d0], hout, rfl⟩, hev, ?_, hstk, hoth⟩
  refine le_trans hn ?_
  simp only [szl_epiWin, hsA]
  set P : ℕ := (sA + 1) ^ (72 * rK + 5 * pK + dK + 4 * wK + 4 * sK + 1) with hPdef
  have hpow : sA + 1 ≤ P := by
    rw [hPdef]
    calc sA + 1 = (sA + 1) ^ 1 := (pow_one _).symm
      _ ≤ (sA + 1) ^ (72 * rK + 5 * pK + dK + 4 * wK + 4 * sK + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith [hpow]

end Work.Fx
