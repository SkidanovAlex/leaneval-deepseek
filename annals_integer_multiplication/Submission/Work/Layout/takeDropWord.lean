import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.Take.Basic
import Submission.Work.Layout.Take.readInt_ev
import Submission.Work.Layout.Take.walk_ev
import Submission.Work.Layout.Take.shift_ev
import Submission.Work.Layout.Take.buildN_ev
import Submission.Work.Layout.Take.cmp_ev
import Submission.Work.Layout.Take.decProg_decStep
import Submission.Work.Layout.Take.takeListFacts

namespace Work.Layout

open HvdH
def ListFacts : Prop :=
  (∀ xs : List Val, vsz (ofList xs) = xs.length + (xs.map vsz).sum + 1) ∧
  (∀ xs : List Val, ((xs.reverse).map vsz).sum = (xs.map vsz).sum) ∧
  (∀ (xs : List Val) (n : ℕ), ((xs.take n).map vsz).sum ≤ (xs.map vsz).sum) ∧
  (∀ (xs : List Val) (n : ℕ), ((xs.drop n).map vsz).sum ≤ (xs.map vsz).sum) ∧
  (∀ ys : List Val, (encs ys).length = (ys.map vsz).sum) ∧
  (∀ ys : List Val, ys.length ≤ (ys.map vsz).sum)

theorem take_aux (main : Cmd) (k : ℕ) (xs : List Val) :
    WordR main splitTakeProg
      (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.take k) :: rest)
      (fun _ => 400 * (vsz (ofList xs) + isz (k : ℤ) + 1)) := by
  have hF : ListFacts := Take.takeListFacts
  intro vs hPre s R hR
  obtain ⟨rest, rfl⟩ := hPre
  -- the content below `int k` and below the list
  set Lbig : List Glyph := (ofList xs).enc ++ encs rest ++ R with hLbig
  set Lrest : List Glyph := encs rest ++ R with hLrest
  have hLsplit : Lbig = (ofList xs).enc ++ Lrest := by rw [hLbig, hLrest, List.append_assoc]
  have h0 : s.stk 0 = (Val.int (k : ℤ)).enc ++ Lbig := by
    rw [hR, Work.Kernel.encs_cons, Work.Kernel.encs_cons, hLbig]; simp only [List.append_assoc]
  -- ===== 1. init =====
  obtain ⟨s1, n1, he1, hn1, hS1, hT1, hD1, hDp1, hB1, ho1⟩ := init_ev main s.reg s.stk
  have h0₁ : s1.stk 0 = (Val.int (k : ℤ)).enc ++ Lbig := by
    rw [ho1 0 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h0
  -- ===== 2. readInt =====
  obtain ⟨s2, n2, he2, hn2, h0₂, hTmp2, hB2, ho2⟩ :=
    Take.readInt_ev main k Lbig s1.reg s1.stk h0₁
  -- ===== 3. walk =====
  have h0₂' : s2.stk 0 = (ofList xs).enc ++ Lrest := by rw [h0₂, hLsplit]
  obtain ⟨s3, n3, he3, hn3, h0₃, hS3, hD3, ho3⟩ :=
    Take.walk_ev main xs Lrest s2.reg s2.stk h0₂'
  -- facts for the comparison phase
  have hBit3 : s3.stk sBit = bitsG_x k.bits ++ gMark :: s.stk sBit := by
    have f0 : s3.stk sBit = s2.stk sBit := ho3 sBit sBit_ne_zero sBit_ne_sS sBit_ne_sD
    have f1 : s2.stk sBit = bitsG_x k.bits ++ s1.stk sBit := hB2
    have f2 : s1.stk sBit = gMark :: s.stk sBit := hB1
    rw [f0, f1, f2]
  have hD3' : s3.stk sD = List.replicate xs.length gU ++ gMark :: s.stk sD := by
    have f0 : s3.stk sD = List.replicate xs.length gU ++ s2.stk sD := hD3
    have f1 : s2.stk sD = s1.stk sD := ho2 sD sD_ne_zero sD_ne_sTmp sD_ne_sBit
    have f2 : s1.stk sD = gMark :: s.stk sD := hD1
    rw [f0, f1, f2]
  -- ===== 4. cmp =====
  obtain ⟨s4, n4, he4, hn4, hB4, hD4, hDp4, ho4⟩ :=
    Take.cmp_ev main (Take.decProg_decStep main) k xs.length (s.stk sBit) (s.stk sD)
      s3.reg s3.stk hBit3 hD3'
  -- facts for the shift phase
  have hS4 : s4.stk sS = encs (xs.reverse) ++ gMark :: s.stk sS := by
    have f0 : s4.stk sS = s3.stk sS := ho4 sS sS_ne_sBit sS_ne_sD sS_ne_sDp
    have f1 : s3.stk sS = encs (xs.reverse) ++ s2.stk sS := hS3
    have f2 : s2.stk sS = s1.stk sS := ho2 sS sS_ne_zero sS_ne_sTmp sS_ne_sBit
    have f3 : s1.stk sS = gMark :: s.stk sS := hS1
    rw [f0, f1, f2, f3]
  have hT4 : s4.stk sT_x = gMark :: s.stk sT_x := by
    have f0 : s4.stk sT_x = s3.stk sT_x := ho4 sT_x sT_ne_sBit sT_ne_sD sT_ne_sDp
    have f1 : s3.stk sT_x = s2.stk sT_x := ho3 sT_x sT_ne_zero sT_ne_sS sT_ne_sD
    have f2 : s2.stk sT_x = s1.stk sT_x := ho2 sT_x sT_ne_zero sT_ne_sTmp sT_ne_sBit
    have f3 : s1.stk sT_x = gMark :: s.stk sT_x := hT1
    rw [f0, f1, f2, f3]
  -- ===== 5. shift =====
  obtain ⟨s5, n5, he5, hn5, hS5, hT5, hD5, ho5⟩ :=
    Take.shift_ev main xs.reverse (xs.length - min k xs.length) (by simp)
      (s.stk sS) (gMark :: s.stk sT_x) (s.stk sD) s4.reg s4.stk hS4 hT4 hD4
  -- facts for the rebuild phase
  have hlenz : ((xs.reverse).drop (xs.length - min k xs.length)).length = min k xs.length := by
    rw [List.length_drop, List.length_reverse, Nat.sub_sub_self (Nat.min_le_right k xs.length)]
  have h0₅ : s5.stk 0 = Lrest := by
    have f0 : s5.stk 0 = s4.stk 0 := ho5 0 zero_ne_sS zero_ne_sT_x zero_ne_sD
    have f1 : s4.stk 0 = s3.stk 0 := ho4 0 zero_ne_sBit zero_ne_sD zero_ne_sDp
    have f2 : s3.stk 0 = Lrest := h0₃
    rw [f0, f1, f2]
  have hDp5 : s5.stk sDp = List.replicate (min k xs.length) gU ++ gMark :: s.stk sDp := by
    have f0 : s5.stk sDp = s4.stk sDp := ho5 sDp sDp_ne_sS sDp_ne_sT_x sDp_ne_sD
    have f1 : s4.stk sDp = List.replicate (min k xs.length) gU ++ s3.stk sDp := hDp4
    have f2 : s3.stk sDp = s2.stk sDp := ho3 sDp sDp_ne_zero sDp_ne_sS sDp_ne_sD
    have f3 : s2.stk sDp = s1.stk sDp := ho2 sDp sDp_ne_zero sDp_ne_sTmp sDp_ne_sBit
    have f4 : s1.stk sDp = gMark :: s.stk sDp := hDp1
    rw [f0, f1, f2, f3, f4]
  have hS5' : s5.stk sS = encs ((xs.reverse).drop (xs.length - min k xs.length)) ++ gMark :: s.stk sS := by
    rw [hS5]
  -- ===== 6. rebuild =====
  obtain ⟨s6, n6, he6, hn6, h0₆, hS6, hDp6, ho6⟩ :=
    Take.buildN_ev main sDp sS sS_ne_zero sDp_ne_zero sDp_ne_sS sS_ne_sX sS_ne_sY sDp_ne_sX sDp_ne_sY
      ((xs.reverse).drop (xs.length - min k xs.length)) (min k xs.length)
      (by rw [hlenz]) Lrest (s.stk sS) (s.stk sDp) s5.reg s5.stk h0₅ hS5' hDp5
  -- ===== 7. the drains =====
  obtain ⟨s7, n7, he7, hn7, hSS7, ho7⟩ :=
    drain_ev main (b := sS) (G := encs (((xs.reverse).drop (xs.length - min k xs.length)).drop
        (min k xs.length))) (B := s.stk sS) (g := s6.reg) (X := s6.stk)
      (gMark_notMem_encs _) hS6
  have hT7 : s7.stk sT_x = encs (((xs.reverse).take (xs.length - min k xs.length)).reverse) ++
      gMark :: s.stk sT_x := by
    have f0 : s7.stk sT_x = s6.stk sT_x := ho7 sT_x sT_ne_sS
    have f1 : s6.stk sT_x = s5.stk sT_x := ho6 sT_x sT_ne_zero sT_ne_sS sT_ne_sDp
    rw [f0, f1, hT5]
  obtain ⟨s8, n8, he8, hn8, hTT8, ho8⟩ :=
    drain_ev main (b := sT_x) (G := encs (((xs.reverse).take (xs.length - min k xs.length)).reverse))
      (B := s.stk sT_x) (g := s7.reg) (X := s7.stk) (gMark_notMem_encs _) hT7
  have hD8 : s8.stk sD = gMark :: s.stk sD := by
    have f0 : s8.stk sD = s7.stk sD := ho8 sD sD_ne_sT_x
    have f1 : s7.stk sD = s6.stk sD := ho7 sD sD_ne_sS
    have f2 : s6.stk sD = s5.stk sD := ho6 sD sD_ne_zero sD_ne_sS sD_ne_sDp
    rw [f0, f1, f2, hD5]
  obtain ⟨s9, n9, he9, hn9, hDD9, ho9⟩ :=
    drain_ev main (b := sD) (G := []) (B := s.stk sD) (g := s8.reg) (X := s8.stk)
      (by simp) hD8
  have hDp9 : s9.stk sDp = gMark :: s.stk sDp := by
    have f0 : s9.stk sDp = s8.stk sDp := ho9 sDp sDp_ne_sD
    have f1 : s8.stk sDp = s7.stk sDp := ho8 sDp sDp_ne_sT_x
    have f2 : s7.stk sDp = s6.stk sDp := ho7 sDp sDp_ne_sS
    rw [f0, f1, f2, hDp6]
  obtain ⟨s10, n10, he10, hn10, hDp10, ho10⟩ :=
    drain_ev main (b := sDp) (G := []) (B := s.stk sDp) (g := s9.reg) (X := s9.stk)
      (by simp) hDp9
  have hBit10 : s10.stk sBit = bitsG_x ((k - min k xs.length).bits) ++ gMark :: s.stk sBit := by
    have f0 : s10.stk sBit = s9.stk sBit := ho10 sBit sBit_ne_sDp
    have f1 : s9.stk sBit = s8.stk sBit := ho9 sBit sBit_ne_sD
    have f2 : s8.stk sBit = s7.stk sBit := ho8 sBit sBit_ne_sT_x
    have f3 : s7.stk sBit = s6.stk sBit := ho7 sBit sBit_ne_sS
    have f4 : s6.stk sBit = s5.stk sBit := ho6 sBit sBit_ne_zero sBit_ne_sS sBit_ne_sDp
    have f5 : s5.stk sBit = s4.stk sBit := ho5 sBit sBit_ne_sS sBit_ne_sT_x sBit_ne_sD
    rw [f0, f1, f2, f3, f4, f5, hB4]
  obtain ⟨s11, n11, he11, hn11, hBit11, ho11⟩ :=
    drain_ev main (b := sBit) (G := bitsG_x ((k - min k xs.length).bits)) (B := s.stk sBit)
      (g := s10.reg) (X := s10.stk) (gMark_notMem_bitsG_x _) hBit10
  -- ===== 8. the identity of the built list =====
  have htake_rev : (((xs.reverse).drop (xs.length - min k xs.length)).take (min k xs.length)).reverse
      = xs.take k := by
    by_cases hk : k ≤ xs.length
    · rw [Nat.min_eq_left hk, List.drop_reverse, Nat.sub_sub_self hk,
        List.take_of_length_le (by simp), List.reverse_reverse]
    · have hle : xs.length ≤ k := (not_le.mp hk).le
      rw [Nat.min_eq_right hle, Nat.sub_self, List.drop_zero, List.take_of_length_le (by simp),
        List.reverse_reverse, List.take_of_length_le hle]
  -- ===== 9. assemble the evaluation =====
  have hev : Ev main splitTakeProg s s11
      (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + n11)))))))))) :=
    Ev.seqs_cons he1 (Ev.seqs_cons he2 (Ev.seqs_cons he3 (Ev.seqs_cons he4
      (Ev.seqs_cons he5 (Ev.seqs_cons he6 (Ev.seqs_cons he7 (Ev.seqs_cons he8
        (Ev.seqs_cons he9 (Ev.seqs_cons he10 he11)))))))))
  obtain ⟨n, heval, hn⟩ := hev
  -- ===== 10. output and frame =====
  refine ⟨ofList (xs.take k) :: rest, s11, n, ⟨rest, rfl, rfl⟩, heval, ?_, ?_, ?_⟩
  · -- cost
    have hi1 : n1 ≤ 11 := hn1
    have hi2 : n2 ≤ 20 * (k.size + 2) := hn2
    have hi3 : n3 ≤ 30 * (xs.length + (xs.map vsz).sum + 1) := hn3
    have hi4 : n4 ≤ 200 * (xs.length + k.size + 1) := hn4
    have hi5 : n5 ≤ 20 * ((((xs.reverse).take (xs.length - min k xs.length)).map vsz).sum +
        (xs.length - min k xs.length) + 1) := hn5
    have hi6 : n6 ≤ 20 * (((((xs.reverse).drop (xs.length - min k xs.length)).take
        (min k xs.length)).map vsz).sum + min k xs.length + 1) := hn6
    have hi7 : n7 ≤ 4 * ((encs (((xs.reverse).drop (xs.length - min k xs.length)).drop
        (min k xs.length))).length + 1) + 2 := hn7
    have hi8 : n8 ≤ 4 * ((encs (((xs.reverse).take (xs.length - min k xs.length)).reverse)).length + 1) + 2 := hn8
    have hi9 : n9 ≤ 6 := by simpa using hn9
    have hi10 : n10 ≤ 6 := by simpa using hn10
    have hi11 : n11 ≤ 4 * ((bitsG_x ((k - min k xs.length).bits)).length + 1) + 2 := hn11
    have hV : vsz (ofList xs) = xs.length + (xs.map vsz).sum + 1 := hF.1 xs
    have hIZ : isz (k : ℤ) = k.size + 2 := by simp [isz, Int.natAbs_natCast]
    have hsum5 : (((xs.reverse).take (xs.length - min k xs.length)).map vsz).sum ≤
        (xs.map vsz).sum :=
      le_trans (hF.2.2.1 (xs.reverse) (xs.length - min k xs.length)) (le_of_eq (hF.2.1 xs))
    have hsum6 : ((((xs.reverse).drop (xs.length - min k xs.length)).take (min k xs.length)).map vsz).sum ≤
        (xs.map vsz).sum :=
      le_trans (le_trans (hF.2.2.1 ((xs.reverse).drop (xs.length - min k xs.length)) (min k xs.length))
        (hF.2.2.2.1 (xs.reverse) (xs.length - min k xs.length))) (le_of_eq (hF.2.1 xs))
    have hsum7 : (encs (((xs.reverse).drop (xs.length - min k xs.length)).drop (min k xs.length))).length ≤
        (xs.map vsz).sum :=
      le_trans (le_trans (le_trans (le_of_eq (hF.2.2.2.2.1 _))
        (hF.2.2.2.1 ((xs.reverse).drop (xs.length - min k xs.length)) (min k xs.length)))
        (hF.2.2.2.1 (xs.reverse) (xs.length - min k xs.length))) (le_of_eq (hF.2.1 xs))
    have hrev : (((((xs.reverse).take (xs.length - min k xs.length)).reverse).map vsz).sum) =
        (((xs.reverse).take (xs.length - min k xs.length)).map vsz).sum := by
      rw [List.map_reverse, List.sum_reverse]
    have hsum8 : (encs (((xs.reverse).take (xs.length - min k xs.length)).reverse)).length ≤
        (xs.map vsz).sum :=
      le_trans (le_trans (le_trans (le_of_eq (hF.2.2.2.2.1 _)) (le_of_eq hrev))
        (hF.2.2.1 (xs.reverse) (xs.length - min k xs.length))) (le_of_eq (hF.2.1 xs))
    have hsum9 : (bitsG_x ((k - min k xs.length).bits)).length ≤ k.size + 2 := by
      rw [bitsG_length_x, Nat.size_eq_bits_len]
      exact Nat.le_trans (Nat.size_le_size (Nat.sub_le k _)) (Nat.le_add_right _ _)
    have hlen1 : xs.length ≤ (xs.map vsz).sum := hF.2.2.2.2.2 xs
    have hj1 : xs.length - min k xs.length ≤ xs.length := Nat.sub_le _ _
    have hm1 : min k xs.length ≤ xs.length := Nat.min_le_right _ _
    show n ≤ 400 * (vsz (ofList xs) + isz (k : ℤ) + 1)
    omega
  · -- stack 0
    have h0₆' : s6.stk 0 = (ofList (xs.take k)).enc ++ Lrest := by
      rw [h0₆, htake_rev]
    have e : s11.stk 0 = s6.stk 0 := by
      have f0 : s11.stk 0 = s10.stk 0 := ho11 0 zero_ne_sBit
      have f1 : s10.stk 0 = s9.stk 0 := ho10 0 zero_ne_sDp
      have f2 : s9.stk 0 = s8.stk 0 := ho9 0 zero_ne_sD
      have f3 : s8.stk 0 = s7.stk 0 := ho8 0 zero_ne_sT_x
      have f4 : s7.stk 0 = s6.stk 0 := ho7 0 zero_ne_sS
      rw [f0, f1, f2, f3, f4]
    rw [e, h0₆', hLrest, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · -- frame
    intro q hq
    by_cases hqS : q = sS
    · subst hqS
      rw [ho11 sS sS_ne_sBit, ho10 sS sS_ne_sDp, ho9 sS sS_ne_sD, ho8 sS sS_ne_sT_x, hSS7]
    by_cases hqT : q = sT_x
    · subst hqT
      rw [ho11 sT_x sT_ne_sBit, ho10 sT_x sT_ne_sDp, ho9 sT_x sT_ne_sD, hTT8]
    by_cases hqD : q = sD
    · subst hqD
      rw [ho11 sD sD_ne_sBit, ho10 sD sD_ne_sDp, hDD9]
    by_cases hqDp : q = sDp
    · subst hqDp
      rw [ho11 sDp sDp_ne_sBit, hDp10]
    by_cases hqB : q = sBit
    · subst hqB
      rw [hBit11]
    by_cases hqTmp : q = sTmp
    · subst hqTmp
      rw [ho11 sTmp sTmp_ne_sBit, ho10 sTmp sTmp_ne_sDp, ho9 sTmp sTmp_ne_sD, ho8 sTmp sTmp_ne_sT_x,
        ho7 sTmp sTmp_ne_sS, ho6 sTmp hq hqS hqDp, ho5 sTmp hqS hqT hqD,
        ho4 sTmp hqB hqD hqDp, ho3 sTmp hq hqS hqD, hTmp2,
        ho1 sTmp hqS hqT hqD hqDp hqB]
    · rw [ho11 q hqB, ho10 q hqDp, ho9 q hqD, ho8 q hqT,
        ho7 q hqS, ho6 q hq hqS hqDp, ho5 q hqS hqT hqD,
        ho4 q hqB hqD hqDp, ho3 q hq hqS hqD,
        ho2 q hq hqTmp hqB, ho1 q hqS hqT hqD hqDp hqB]

theorem drop_aux (main : Cmd) (k : ℕ) (xs : List Val) :
    WordR main splitDropProg
      (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.drop k) :: rest)
      (fun _ => 400 * (vsz (ofList xs) + isz (k : ℤ) + 1)) := by
  have hF : ListFacts := Take.takeListFacts
  intro vs hPre s R hR
  obtain ⟨rest, rfl⟩ := hPre
  set Lbig : List Glyph := (ofList xs).enc ++ encs rest ++ R with hLbig
  set Lrest : List Glyph := encs rest ++ R with hLrest
  have hLsplit : Lbig = (ofList xs).enc ++ Lrest := by rw [hLbig, hLrest, List.append_assoc]
  have h0 : s.stk 0 = (Val.int (k : ℤ)).enc ++ Lbig := by
    rw [hR, Work.Kernel.encs_cons, Work.Kernel.encs_cons, hLbig]; simp only [List.append_assoc]
  -- 1. init
  obtain ⟨s1, n1, he1, hn1, hS1, hT1, hD1, hDp1, hB1, ho1⟩ := init_ev main s.reg s.stk
  have h0₁ : s1.stk 0 = (Val.int (k : ℤ)).enc ++ Lbig := by
    rw [ho1 0 zero_ne_sS zero_ne_sT_x zero_ne_sD zero_ne_sDp zero_ne_sBit]; exact h0
  -- 2. readInt
  obtain ⟨s2, n2, he2, hn2, h0₂, hTmp2, hB2, ho2⟩ :=
    Take.readInt_ev main k Lbig s1.reg s1.stk h0₁
  -- 3. walk
  have h0₂' : s2.stk 0 = (ofList xs).enc ++ Lrest := by rw [h0₂, hLsplit]
  obtain ⟨s3, n3, he3, hn3, h0₃, hS3, hD3, ho3⟩ :=
    Take.walk_ev main xs Lrest s2.reg s2.stk h0₂'
  -- facts for the comparison phase
  have hBit3 : s3.stk sBit = bitsG_x k.bits ++ gMark :: s.stk sBit := by
    have f0 : s3.stk sBit = s2.stk sBit := ho3 sBit sBit_ne_zero sBit_ne_sS sBit_ne_sD
    have f1 : s2.stk sBit = bitsG_x k.bits ++ s1.stk sBit := hB2
    have f2 : s1.stk sBit = gMark :: s.stk sBit := hB1
    rw [f0, f1, f2]
  have hD3' : s3.stk sD = List.replicate xs.length gU ++ gMark :: s.stk sD := by
    have f0 : s3.stk sD = List.replicate xs.length gU ++ s2.stk sD := hD3
    have f1 : s2.stk sD = s1.stk sD := ho2 sD sD_ne_zero sD_ne_sTmp sD_ne_sBit
    have f2 : s1.stk sD = gMark :: s.stk sD := hD1
    rw [f0, f1, f2]
  -- 4. cmp
  obtain ⟨s4, n4, he4, hn4, hB4, hD4, hDp4, ho4⟩ :=
    Take.cmp_ev main (Take.decProg_decStep main) k xs.length (s.stk sBit) (s.stk sD)
      s3.reg s3.stk hBit3 hD3'
  have hS4 : s4.stk sS = encs (xs.reverse) ++ gMark :: s.stk sS := by
    have f0 : s4.stk sS = s3.stk sS := ho4 sS sS_ne_sBit sS_ne_sD sS_ne_sDp
    have f1 : s3.stk sS = encs (xs.reverse) ++ s2.stk sS := hS3
    have f2 : s2.stk sS = s1.stk sS := ho2 sS sS_ne_zero sS_ne_sTmp sS_ne_sBit
    have f3 : s1.stk sS = gMark :: s.stk sS := hS1
    rw [f0, f1, f2, f3]
  have hT4 : s4.stk sT_x = gMark :: s.stk sT_x := by
    have f0 : s4.stk sT_x = s3.stk sT_x := ho4 sT_x sT_ne_sBit sT_ne_sD sT_ne_sDp
    have f1 : s3.stk sT_x = s2.stk sT_x := ho3 sT_x sT_ne_zero sT_ne_sS sT_ne_sD
    have f2 : s2.stk sT_x = s1.stk sT_x := ho2 sT_x sT_ne_zero sT_ne_sTmp sT_ne_sBit
    have f3 : s1.stk sT_x = gMark :: s.stk sT_x := hT1
    rw [f0, f1, f2, f3]
  have h0₄ : s4.stk 0 = Lrest := by
    have f0 : s4.stk 0 = s3.stk 0 := ho4 0 zero_ne_sBit zero_ne_sD zero_ne_sDp
    rw [f0, h0₃]
  have hDp4' : s4.stk sDp = List.replicate (min k xs.length) gU ++ gMark :: s.stk sDp := by
    have f0 : s4.stk sDp = List.replicate (min k xs.length) gU ++ s3.stk sDp := hDp4
    have f1 : s3.stk sDp = s2.stk sDp := ho3 sDp sDp_ne_zero sDp_ne_sS sDp_ne_sD
    have f2 : s2.stk sDp = s1.stk sDp := ho2 sDp sDp_ne_zero sDp_ne_sTmp sDp_ne_sBit
    have f3 : s1.stk sDp = gMark :: s.stk sDp := hDp1
    rw [f0, f1, f2, f3]
  -- 5. rebuild the tail from `sS`, driven by the units remaining on `sD`
  obtain ⟨s5, n5, he5, hn5, h0₅, hS5, hD5, ho5⟩ :=
    Take.buildN_ev main sD sS sS_ne_zero sD_ne_zero sD_ne_sS sS_ne_sX sS_ne_sY sD_ne_sX sD_ne_sY
      (xs.reverse) (xs.length - min k xs.length)
      (by simp) Lrest (s.stk sS) (s.stk sD) s4.reg s4.stk h0₄ hS4 hD4
  -- 6. the drains
  obtain ⟨s6, n6, he6, hn6, hSS6, ho6⟩ :=
    drain_ev main (b := sS) (G := encs ((xs.reverse).drop (xs.length - min k xs.length)))
      (B := s.stk sS) (g := s5.reg) (X := s5.stk) (gMark_notMem_encs _) hS5
  have hT6 : s6.stk sT_x = gMark :: s.stk sT_x := by
    have f0 : s6.stk sT_x = s5.stk sT_x := ho6 sT_x sT_ne_sS
    have f1 : s5.stk sT_x = s4.stk sT_x := ho5 sT_x sT_ne_zero sT_ne_sS sT_ne_sD
    rw [f0, f1, hT4]
  obtain ⟨s7, n7, he7, hn7, hTT7, ho7⟩ :=
    drain_ev main (b := sT_x) (G := []) (B := s.stk sT_x) (g := s6.reg) (X := s6.stk)
      (by simp) hT6
  have hD7 : s7.stk sD = gMark :: s.stk sD := by
    have f0 : s7.stk sD = s6.stk sD := ho7 sD sD_ne_sT_x
    have f1 : s6.stk sD = s5.stk sD := ho6 sD sD_ne_sS
    rw [f0, f1, hD5]
  obtain ⟨s8, n8, he8, hn8, hDD8, ho8⟩ :=
    drain_ev main (b := sD) (G := []) (B := s.stk sD) (g := s7.reg) (X := s7.stk)
      (by simp) hD7
  have hDp8 : s8.stk sDp = List.replicate (min k xs.length) gU ++ gMark :: s.stk sDp := by
    have f0 : s8.stk sDp = s7.stk sDp := ho8 sDp sDp_ne_sD
    have f1 : s7.stk sDp = s6.stk sDp := ho7 sDp sDp_ne_sT_x
    have f2 : s6.stk sDp = s5.stk sDp := ho6 sDp sDp_ne_sS
    have f3 : s5.stk sDp = s4.stk sDp := ho5 sDp sDp_ne_zero sDp_ne_sS sDp_ne_sD
    rw [f0, f1, f2, f3, hDp4']
  obtain ⟨s9, n9, he9, hn9, hDp9, ho9⟩ :=
    drain_ev main (b := sDp) (G := List.replicate (min k xs.length) gU) (B := s.stk sDp)
      (g := s8.reg) (X := s8.stk) (gMark_notMem_replicate_gU _) hDp8
  have hBit9 : s9.stk sBit = bitsG_x ((k - min k xs.length).bits) ++ gMark :: s.stk sBit := by
    have f0 : s9.stk sBit = s8.stk sBit := ho9 sBit sBit_ne_sDp
    have f1 : s8.stk sBit = s7.stk sBit := ho8 sBit sBit_ne_sD
    have f2 : s7.stk sBit = s6.stk sBit := ho7 sBit sBit_ne_sT_x
    have f3 : s6.stk sBit = s5.stk sBit := ho6 sBit sBit_ne_sS
    have f4 : s5.stk sBit = s4.stk sBit := ho5 sBit sBit_ne_zero sBit_ne_sS sBit_ne_sD
    rw [f0, f1, f2, f3, f4, hB4]
  obtain ⟨s10, n10, he10, hn10, hBit10, ho10⟩ :=
    drain_ev main (b := sBit) (G := bitsG_x ((k - min k xs.length).bits)) (B := s.stk sBit)
      (g := s9.reg) (X := s9.stk) (gMark_notMem_bitsG_x _) hBit9
  -- 7. the identity of the built list
  have hdrop_rev : (((xs.reverse).take (xs.length - min k xs.length)).reverse) = xs.drop k := by
    by_cases hk : k ≤ xs.length
    · rw [Nat.min_eq_left hk, List.take_reverse, Nat.sub_sub_self hk, List.reverse_reverse]
    · have hle : xs.length ≤ k := (not_le.mp hk).le
      rw [Nat.min_eq_right hle, Nat.sub_self, List.take_zero, List.reverse_nil]
      exact (List.drop_eq_nil_of_le hle).symm
  -- 8. assemble the evaluation
  have hev : Ev main splitDropProg s s10
      (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + n10))))))))) :=
    Ev.seqs_cons he1 (Ev.seqs_cons he2 (Ev.seqs_cons he3 (Ev.seqs_cons he4
      (Ev.seqs_cons he5 (Ev.seqs_cons he6 (Ev.seqs_cons he7 (Ev.seqs_cons he8
        (Ev.seqs_cons he9 he10))))))))
  obtain ⟨n, heval, hn⟩ := hev
  refine ⟨ofList (xs.drop k) :: rest, s10, n, ⟨rest, rfl, rfl⟩, heval, ?_, ?_, ?_⟩
  · -- cost
    have hi1 : n1 ≤ 11 := hn1
    have hi2 : n2 ≤ 20 * (k.size + 2) := hn2
    have hi3 : n3 ≤ 30 * (xs.length + (xs.map vsz).sum + 1) := hn3
    have hi4 : n4 ≤ 200 * (xs.length + k.size + 1) := hn4
    have hi5 : n5 ≤ 20 * ((((xs.reverse).take (xs.length - min k xs.length)).map vsz).sum +
        (xs.length - min k xs.length) + 1) := hn5
    have hi6 : n6 ≤ 4 * ((encs ((xs.reverse).drop (xs.length - min k xs.length))).length + 1) + 2 := hn6
    have hi7 : n7 ≤ 6 := by simpa using hn7
    have hi8 : n8 ≤ 6 := by simpa using hn8
    have hi9 : n9 ≤ 4 * (min k xs.length + 1) + 2 := by simpa using hn9
    have hi10 : n10 ≤ 4 * ((bitsG_x ((k - min k xs.length).bits)).length + 1) + 2 := hn10
    have hV : vsz (ofList xs) = xs.length + (xs.map vsz).sum + 1 := hF.1 xs
    have hIZ : isz (k : ℤ) = k.size + 2 := by simp [isz, Int.natAbs_natCast]
    have hsum5 : (((xs.reverse).take (xs.length - min k xs.length)).map vsz).sum ≤
        (xs.map vsz).sum :=
      le_trans (hF.2.2.1 (xs.reverse) (xs.length - min k xs.length)) (le_of_eq (hF.2.1 xs))
    have hsum6 : (encs ((xs.reverse).drop (xs.length - min k xs.length))).length ≤
        (xs.map vsz).sum :=
      le_trans (le_trans (le_of_eq (hF.2.2.2.2.1 _))
        (hF.2.2.2.1 (xs.reverse) (xs.length - min k xs.length))) (le_of_eq (hF.2.1 xs))
    have hsum10 : (bitsG_x ((k - min k xs.length).bits)).length ≤ k.size + 2 := by
      rw [bitsG_length_x, Nat.size_eq_bits_len]
      exact Nat.le_trans (Nat.size_le_size (Nat.sub_le k _)) (Nat.le_add_right _ _)
    have hlen1 : xs.length ≤ (xs.map vsz).sum := hF.2.2.2.2.2 xs
    have hj1 : xs.length - min k xs.length ≤ xs.length := Nat.sub_le _ _
    have hm1 : min k xs.length ≤ xs.length := Nat.min_le_right _ _
    show n ≤ 400 * (vsz (ofList xs) + isz (k : ℤ) + 1)
    omega
  · -- stack 0
    have h0₅' : s5.stk 0 = (ofList (xs.drop k)).enc ++ Lrest := by
      rw [h0₅, hdrop_rev]
    have e : s10.stk 0 = s5.stk 0 := by
      have f0 : s10.stk 0 = s9.stk 0 := ho10 0 zero_ne_sBit
      have f1 : s9.stk 0 = s8.stk 0 := ho9 0 zero_ne_sDp
      have f2 : s8.stk 0 = s7.stk 0 := ho8 0 zero_ne_sD
      have f3 : s7.stk 0 = s6.stk 0 := ho7 0 zero_ne_sT_x
      have f4 : s6.stk 0 = s5.stk 0 := ho6 0 zero_ne_sS
      rw [f0, f1, f2, f3, f4]
    rw [e, h0₅', hLrest, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · -- frame
    intro q hq
    by_cases hqS : q = sS
    · subst hqS
      have f0 : s10.stk sS = s9.stk sS := ho10 sS sS_ne_sBit
      have f1 : s9.stk sS = s8.stk sS := ho9 sS sS_ne_sDp
      have f2 : s8.stk sS = s7.stk sS := ho8 sS sS_ne_sD
      have f3 : s7.stk sS = s6.stk sS := ho7 sS sS_ne_sT_x
      rw [f0, f1, f2, f3, hSS6]
    by_cases hqT : q = sT_x
    · subst hqT
      have f0 : s10.stk sT_x = s9.stk sT_x := ho10 sT_x sT_ne_sBit
      have f1 : s9.stk sT_x = s8.stk sT_x := ho9 sT_x sT_ne_sDp
      have f2 : s8.stk sT_x = s7.stk sT_x := ho8 sT_x sT_ne_sD
      rw [f0, f1, f2, hTT7]
    by_cases hqD : q = sD
    · subst hqD
      have f0 : s10.stk sD = s9.stk sD := ho10 sD sD_ne_sBit
      have f1 : s9.stk sD = s8.stk sD := ho9 sD sD_ne_sDp
      rw [f0, f1, hDD8]
    by_cases hqDp : q = sDp
    · subst hqDp
      have f0 : s10.stk sDp = s9.stk sDp := ho10 sDp sDp_ne_sBit
      rw [f0, hDp9]
    by_cases hqB : q = sBit
    · subst hqB
      rw [hBit10]
    by_cases hqTmp : q = sTmp
    · subst hqTmp
      have f0 : s10.stk sTmp = s9.stk sTmp := ho10 sTmp sTmp_ne_sBit
      have f1 : s9.stk sTmp = s8.stk sTmp := ho9 sTmp sTmp_ne_sDp
      have f2 : s8.stk sTmp = s7.stk sTmp := ho8 sTmp sTmp_ne_sD
      have f3 : s7.stk sTmp = s6.stk sTmp := ho7 sTmp sTmp_ne_sT_x
      have f4 : s6.stk sTmp = s5.stk sTmp := ho6 sTmp sTmp_ne_sS
      have f5 : s5.stk sTmp = s4.stk sTmp := ho5 sTmp hq hqS hqD
      have f6 : s4.stk sTmp = s3.stk sTmp := ho4 sTmp hqB hqD hqDp
      have f7 : s3.stk sTmp = s2.stk sTmp := ho3 sTmp hq hqS hqD
      have f8 : s2.stk sTmp = s1.stk sTmp := hTmp2
      have f9 : s1.stk sTmp = s.stk sTmp := ho1 sTmp hqS hqT hqD hqDp hqB
      rw [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]
    · have f0 : s10.stk q = s9.stk q := ho10 q hqB
      have f1 : s9.stk q = s8.stk q := ho9 q hqDp
      have f2 : s8.stk q = s7.stk q := ho8 q hqD
      have f3 : s7.stk q = s6.stk q := ho7 q hqT
      have f4 : s6.stk q = s5.stk q := ho6 q hqS
      have f5 : s5.stk q = s4.stk q := ho5 q hq hqS hqD
      have f6 : s4.stk q = s3.stk q := ho4 q hqB hqD hqDp
      have f7 : s3.stk q = s2.stk q := ho3 q hq hqS hqD
      have f8 : s2.stk q = s1.stk q := ho2 q hq hqTmp hqB
      have f9 : s1.stk q = s.stk q := ho1 q hqS hqT hqD hqDp hqB
      rw [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9]


/-- **`LayoutLib.take` and `LayoutLib.drop`**: split `ofList xs` after `k` elements.  Route suggested by
the reviewers: compute `xs.length` first (`O(vsz)`), compare with `int k` (`O(isz k + isz len)`), and only
if `k < xs.length` build a unary counter of `k` markers (`O(k) ≤ O(vsz)`), then split with `O(1)` per
element. -/
theorem takeDropWord : (∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
    (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.take k) :: rest)
    (fun _ => K * (vsz (ofList xs) + isz k + 1)))
  ∧ (∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ) (xs : List Val), WordR main p
    (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
    (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.drop k) :: rest)
    (fun _ => K * (vsz (ofList xs) + isz k + 1))) := by
  refine ⟨⟨splitTakeProg, 400, fun main k xs => take_aux main k xs⟩,
    ⟨splitDropProg, 400, fun main k xs => drop_aux main k xs⟩⟩

end Work.Layout
