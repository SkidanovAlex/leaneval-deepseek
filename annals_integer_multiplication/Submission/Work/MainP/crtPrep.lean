import Mathlib
import Submission.Work.MainP.crtLib

/-!
# `crtPrep`: the argument shuffling before the two CRT directions

From `[.int dir, intList ss, ofList xs, rest]` (`dir ≤ 1`, `xs.length = S`) produce
`[.int dir, .int S, intList ss, ofList xs, rest]`: compute the length of the list value with
`pLen`, then move it into place with six `pRoll` moves. The value stack is rearranged as

`[dir,ss,xs] →(roll 2) [xs,dir,ss] →(pLen) [S,xs,dir,ss] →(roll 2) [dir,S,xs,ss]
→(roll 3) [ss,dir,S,xs] →(roll 1) [dir,ss,S,xs] →(roll 2) [S,dir,ss,xs] →(roll 1) [dir,S,ss,xs]`

Every value on the stack injects into `SB ss S xs` (`dir` is `≤ 1`, so `vsz (.int dir) ≤ 3`,
`vsz (.int S) ≤ 2 * SB`, `vsz (intList ss) ≤ PB ≤ SB`, `vsz (ofList xs) ≤ PB ≤ SB`), so each phase
costs at most `100 * CU` and the whole word `700 * CU`; we return the round constant `1000`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Phase lemmas: `pLen` and `pRoll` from an exact state, at a prescribed constant cost -/

/-- A `pRoll k` move from an exact state, with the cost hypothesis `t` for the top `k+1` sizes. -/
private theorem rollTo (L : CrtLib) (main : Cmd) (k : ℕ) (l0 out0 : List Val) (t c : ℕ)
    (hk : k < l0.length) (hpost : l0.getD k .nil :: l0.eraseIdx k = out0)
    (ht : ((l0.take (k + 1)).map vsz).sum + 1 ≤ t)
    (hc : L.KRoll * (k + 1) * t ≤ c) :
    WordR main (L.pRoll k) (fun vs => vs = l0) (fun _ out => out = out0) (fun _ => c) :=
  WordR.conseqK (L.hRoll main k) L.hK (fun vs h => by rw [h]; exact hk)
    (fun vs out h hq => by rw [h] at hq; rw [hq, hpost])
    (fun vs h => by rw [h]; exact le_trans (Nat.mul_le_mul_left _ ht) hc)

/-- `pLen` from an exact state: `ofList xs :: rest ↦ .int S :: ofList xs :: rest` (with `xs.length = S`). -/
private theorem lenTo (L : CrtLib) (main : Cmd) (xs : List Val) (S : ℕ) (rest : List Val)
    (t c : ℕ) (hxs : xs.length = S) (ht : vsz (ofList xs) + 1 ≤ t) (hc : L.KLen * t ≤ c) :
    WordR main L.pLen (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = Val.int (S : ℤ) :: ofList xs :: rest) (fun _ => c) :=
  WordR.conseqK (L.hLen main xs) L.hK (fun vs h => ⟨rest, h⟩)
    (fun vs out h hq => by
      obtain ⟨r, hr, hout⟩ := hq
      rw [h] at hr
      obtain ⟨-, rfl⟩ := List.cons.inj hr
      rw [hout, hxs])
    (fun _ _ => le_trans (Nat.mul_le_mul_left _ ht) hc)

/-- Sequential composition of two exact-state words, adding the constant costs. -/
private theorem seqEx (hK : KernelLib) {main p q : Cmd} {A B D : List Val} {c₁ c₂ : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = D) (fun _ => c₂)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = D) (fun _ => c₁ + c₂) :=
  WordR.conseqK (hK.seq main p q (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁)
      (fun vs => vs = B) (fun _ out => out = D) (fun _ => c₂) (fun _ => c₂) h1 h2
      (fun vs mid ha hb => ⟨hb, le_rfl⟩)) hK (fun vs h => h)
    (fun vs out h hq => by obtain ⟨mid, rfl, hout⟩ := hq; exact hout)
    (fun _ _ => le_rfl)

/-! ## Budget arithmetic -/

/-- `pRoll`'s constant, times `k+1 ≤ 4`, is at most `KF L`. -/
private theorem rollConst_le (L : CrtLib) {k : ℕ} (hk : k ≤ 3) : L.KRoll * (k + 1) ≤ KF L := by
  have hKS : L.KRoll ≤ KS L := by simp only [KS]; omega
  calc L.KRoll * (k + 1) ≤ L.KRoll * 4 := Nat.mul_le_mul_left _ (by omega)
    _ ≤ KS L * 4 := Nat.mul_le_mul_right 4 hKS
    _ ≤ KF L := by rw [KF]; omega

/-- Every library constant bounded by `KS L` is bounded by `KF L`. -/
private theorem Kconst_le_KF (L : CrtLib) {x : ℕ} (hx : x ≤ KS L) : x ≤ KF L := by
  rw [KF]
  calc x ≤ KS L := hx
    _ ≤ 1000 * (KS L + 1) := by omega

/-- A single phase: a constant `cc ≤ KF L` times at most the sizes of four values (all `≤ 3 * SZ`),
plus one, is at most `100 * (KF L * SZ)`. -/
private theorem cost_le_CU (L : CrtLib) {SZ cc t : ℕ} (hcc : cc ≤ KF L) (ht : t ≤ 12 * SZ) :
    cc * t ≤ 100 * (KF L * SZ) := by
  calc cc * t ≤ KF L * (12 * SZ) := Nat.mul_le_mul hcc ht
    _ = 12 * (KF L * SZ) := by ring
    _ ≤ 100 * (KF L * SZ) := Nat.mul_le_mul_right _ (by norm_num)

theorem crtPrep (L : Work.MainP.CrtLib) :
    ∃ (prog : HvdH.Cmd) (C : ℕ),
      ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ) (xs : List HvdH.Val) (dir : ℕ),
        1 ≤ S → dir ≤ 1 → xs.length = S →
        HvdH.WordR main prog
          (fun vs => ∃ rest, vs = HvdH.Val.int (dir : ℤ) :: HvdH.intList ss :: HvdH.ofList xs :: rest)
          (fun vs out => ∃ rest, vs = HvdH.Val.int (dir : ℤ) :: HvdH.intList ss :: HvdH.ofList xs :: rest ∧
            out = HvdH.Val.int (dir : ℤ) :: HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: HvdH.ofList xs :: rest)
          (fun _ => C * Work.MainP.CU L ss S xs) := by
  let prog : Cmd := .seq (.seq (.seq (.seq (.seq (.seq (L.pRoll 2) L.pLen) (L.pRoll 2))
    (L.pRoll 3)) (L.pRoll 1)) (L.pRoll 2)) (L.pRoll 1)
  refine ⟨prog, 1000, ?_⟩
  intro main ss S xs dir hS hdir hxs
  have hSZ1 : 1 ≤ SB ss S xs := one_le_SB ss S xs
  have hV : vsz (ofList xs) ≤ SB ss S xs := le_trans (V_le_PB ss S xs) (PB_le_SB ss S xs)
  have hW : vsz (intList ss) ≤ SB ss S xs :=
    le_trans (W_le_PB (ss := ss) (S := S) (xs := xs) hS) (PB_le_SB ss S xs)
  have hA : vsz (Val.int (dir : ℤ)) ≤ 3 * SB ss S xs := by
    have hd : dir.size ≤ 1 := by simpa using Nat.size_le_size hdir
    rw [vsz_intNat, iszN]; omega
  have hLb : vsz (Val.int (S : ℤ)) ≤ 2 * SB ss S xs := by
    rw [SB, QB, vsz_intNat, iszN]
    have hPB : 1 ≤ PB ss S xs := one_le_PB ss S xs
    calc S.size + 2 ≤ 2 * (S.size + 1) := by omega
      _ ≤ 2 * (PB ss S xs * (S.size + 1)) := by
            have h1 : S.size + 1 ≤ PB ss S xs * (S.size + 1) :=
              calc S.size + 1 = 1 * (S.size + 1) := (one_mul _).symm
                _ ≤ PB ss S xs * (S.size + 1) := Nat.mul_le_mul_right _ hPB
            exact Nat.mul_le_mul_left 2 h1
  have hcost : ∀ cc t : ℕ, cc ≤ KF L → t ≤ 12 * SB ss S xs → cc * t ≤ 100 * CU L ss S xs :=
    fun cc t h1 h2 => cost_le_CU L h1 h2
  have hroll : ∀ k : ℕ, k ≤ 3 → L.KRoll * (k + 1) ≤ KF L := fun k hk => rollConst_le L hk
  have hKLen : L.KLen ≤ KF L := Kconst_le_KF L (by simp only [KS]; omega)
  have hchain : ∀ rest : List Val,
      WordR main prog (fun vs => vs = Val.int (dir : ℤ) :: intList ss :: ofList xs :: rest)
        (fun _ out => out = Val.int (dir : ℤ) :: Val.int (S : ℤ) :: intList ss :: ofList xs :: rest)
        (fun _ => 1000 * CU L ss S xs) := by
    intro rest
    set A0 : List Val := Val.int (dir : ℤ) :: intList ss :: ofList xs :: rest with hA0
    set A1 : List Val := ofList xs :: Val.int (dir : ℤ) :: intList ss :: rest with hA1
    set A2 : List Val := Val.int (S : ℤ) :: ofList xs :: Val.int (dir : ℤ) :: intList ss :: rest with hA2
    set A3 : List Val :=
      Val.int (dir : ℤ) :: Val.int (S : ℤ) :: ofList xs :: intList ss :: rest with hA3
    set A4 : List Val :=
      intList ss :: Val.int (dir : ℤ) :: Val.int (S : ℤ) :: ofList xs :: rest with hA4
    set A5 : List Val :=
      Val.int (dir : ℤ) :: intList ss :: Val.int (S : ℤ) :: ofList xs :: rest with hA5
    set A6 : List Val :=
      Val.int (S : ℤ) :: Val.int (dir : ℤ) :: intList ss :: ofList xs :: rest with hA6
    set A7 : List Val :=
      Val.int (dir : ℤ) :: Val.int (S : ℤ) :: intList ss :: ofList xs :: rest with hA7
    have s1 : WordR main (L.pRoll 2) (fun vs => vs = A0) (fun _ out => out = A1)
        (fun _ => 100 * CU L ss S xs) :=
      rollTo L main 2 A0 A1 (12 * SB ss S xs) (100 * CU L ss S xs)
        (by simp [hA0]) (by simp [hA0, hA1])
        (by simp only [hA0, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil]; omega)
        (hcost (L.KRoll * 3) (12 * SB ss S xs) (hroll 2 (by norm_num)) le_rfl)
    have s2 : WordR main L.pLen (fun vs => vs = A1) (fun _ out => out = A2)
        (fun _ => 100 * CU L ss S xs) :=
      lenTo L main xs S (Val.int (dir : ℤ) :: intList ss :: rest) (12 * SB ss S xs)
        (100 * CU L ss S xs) hxs (by omega) (hcost L.KLen (12 * SB ss S xs) hKLen le_rfl)
    have s3 : WordR main (L.pRoll 2) (fun vs => vs = A2) (fun _ out => out = A3)
        (fun _ => 100 * CU L ss S xs) :=
      rollTo L main 2 A2 A3 (12 * SB ss S xs) (100 * CU L ss S xs)
        (by simp [hA2]) (by simp [hA2, hA3])
        (by simp only [hA2, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil]; omega)
        (hcost (L.KRoll * 3) (12 * SB ss S xs) (hroll 2 (by norm_num)) le_rfl)
    have s4 : WordR main (L.pRoll 3) (fun vs => vs = A3) (fun _ out => out = A4)
        (fun _ => 100 * CU L ss S xs) :=
      rollTo L main 3 A3 A4 (12 * SB ss S xs) (100 * CU L ss S xs)
        (by simp [hA3]) (by simp [hA3, hA4])
        (by simp only [hA3, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil]; omega)
        (hcost (L.KRoll * 4) (12 * SB ss S xs) (hroll 3 (by norm_num)) le_rfl)
    have s5 : WordR main (L.pRoll 1) (fun vs => vs = A4) (fun _ out => out = A5)
        (fun _ => 100 * CU L ss S xs) :=
      rollTo L main 1 A4 A5 (12 * SB ss S xs) (100 * CU L ss S xs)
        (by simp [hA4]) (by simp [hA4, hA5])
        (by simp only [hA4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil]; omega)
        (hcost (L.KRoll * 2) (12 * SB ss S xs) (hroll 1 (by norm_num)) le_rfl)
    have s6 : WordR main (L.pRoll 2) (fun vs => vs = A5) (fun _ out => out = A6)
        (fun _ => 100 * CU L ss S xs) :=
      rollTo L main 2 A5 A6 (12 * SB ss S xs) (100 * CU L ss S xs)
        (by simp [hA5]) (by simp [hA5, hA6])
        (by simp only [hA5, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil]; omega)
        (hcost (L.KRoll * 3) (12 * SB ss S xs) (hroll 2 (by norm_num)) le_rfl)
    have s7 : WordR main (L.pRoll 1) (fun vs => vs = A6) (fun _ out => out = A7)
        (fun _ => 100 * CU L ss S xs) :=
      rollTo L main 1 A6 A7 (12 * SB ss S xs) (100 * CU L ss S xs)
        (by simp [hA6]) (by simp [hA6, hA7])
        (by simp only [hA6, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil]; omega)
        (hcost (L.KRoll * 2) (12 * SB ss S xs) (hroll 1 (by norm_num)) le_rfl)
    have c12 := seqEx L.hK s1 s2
    have c123 := seqEx L.hK c12 s3
    have c1234 := seqEx L.hK c123 s4
    have c12345 := seqEx L.hK c1234 s5
    have c123456 := seqEx L.hK c12345 s6
    have cAll := seqEx L.hK c123456 s7
    have hfin : WordR main prog (fun vs => vs = A0) (fun _ out => out = A7)
        (fun _ => 1000 * CU L ss S xs) :=
      WordR.conseqK cAll L.hK (fun vs h => h) (fun vs out _ hq => hq) (fun _ _ => by omega)
    exact hfin
  intro vs hpre s R hstk
  obtain ⟨rest, rfl⟩ := hpre
  obtain ⟨out, s', n, hpost, hev, hn, hstk', hfr⟩ := hchain rest _ rfl s R hstk
  exact ⟨out, s', n, ⟨rest, rfl, hpost⟩, hev, hn, hstk', hfr⟩

end Work.MainP
