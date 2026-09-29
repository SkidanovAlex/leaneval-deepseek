import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.SizeShared
import Submission.Work.IntLib.SizeCount
import Submission.Work.IntLib.SizeEmit
import Submission.Work.IntLib.SizeScaffold

/-!
# The `size`, `clog 2` and `pow2` integer words

Assembly of the three `HvdH.IntLib` fields `size`, `clog2`, `pow2` from the low-level pieces:

* `sizeCountPiece` (`SizeCount.lean`), `sizeEmit`, `sizeEmitZeros` (`SizeEmit.lean`),
* `sizeHalve`, `sizeBinUnary` (halving a unary counter to bits; binary to unary),
* `decValue` (subtracting one from a positive integer value).
-/

set_option autoImplicit false

namespace Work.IntLib
namespace Size

open HvdH

/-! ## `size` -/

theorem sizeWord_size : ∃ (p : Cmd) (K : ℕ), ∀ main : Cmd, UnOp main p (fun _ => True)
    (fun a => (a.natAbs.size : ℤ)) (fun a => K * isz a) := by
  obtain ⟨pCount, Kc, hCount⟩ := sizeCountPiece
  obtain ⟨pHalve, Kh, hHalve⟩ := sizeHalve
  obtain ⟨pEmit, Ke, hEmit⟩ := sizeEmit
  refine ⟨.seq (.pop 0 rSign) (.seq pCount (.seq pHalve pEmit)), Kc + Kh + Ke + 1, ?_⟩
  intro main vs hpre s R hR
  obtain ⟨a, rest, rfl, _⟩ := hpre
  have hR' : s.stk 0 = (if a < 0 then Glyph.neg else Glyph.pos) ::
      ((Computability.encodeNat a.natAbs).map Glyph.bit ++ [Glyph.iend]) ++
        (encs rest ++ R) := by
    rw [hR]
    simp only [HvdH.encs, List.map_cons, List.flatten_cons]
    rw [enc_int]
    simp [List.append_assoc]
  let s1 : State := (s.updStk 0 (s.stk 0).tail).updReg rSign ((s.stk 0).headD .eos)
  have e1 : Eval main (.pop 0 rSign) s s1 1 := by
    have hh := Eval.pop (main := main) 0 rSign s
    simpa [s1, State.updStk, State.updReg] using hh
  have hs1 : s1.stk 0 = (Computability.encodeNat a.natAbs).map Glyph.bit ++ [Glyph.iend] ++
      (encs rest ++ R) := by
    simp only [s1, State.updReg_stk, State.updStk_apply, if_pos rfl, List.tail_cons]
    rw [hR']
    simp
  have hs1_oth : ∀ k : Stk, k ≠ 0 → s1.stk k = s.stk k := by
    intro k hk
    simp only [s1, State.updReg_stk, State.updStk_apply]
    rw [if_neg hk]
  obtain ⟨s2, c2, he2, hc2, hs2_0, hs2_1, hs2_oth⟩ :=
    hCount main _ (encs rest ++ R) (s1.stk 1) s1 hs1 rfl
  obtain ⟨s3, c3, he3, hc3, hs3_1, hs3_2, hs3_3, hs3_oth⟩ :=
    hHalve main ((Computability.encodeNat a.natAbs).length) (s1.stk 1) (s2.stk 2) (s2.stk 3)
      s2 hs2_1 rfl rfl
  have hIsB : IsBits ((((Computability.encodeNat a.natAbs).length).bits).reverse).reverse := by
    rw [List.reverse_reverse]
    exact isBits_bits _
  obtain ⟨s4, c4, he4, hc4, hs4_0, hs4_1, hs4_3, hs4_oth⟩ :=
    hEmit main ((((Computability.encodeNat a.natAbs).length).bits).reverse) (encs rest ++ R)
      (s1.stk 1) (s2.stk 3) s3 hIsB
      (by rw [hs3_oth 0 (by decide) (by decide) (by decide), hs2_0]) hs3_1 hs3_3
  have hofBits : Work.IntLib.ofBits (((Computability.encodeNat a.natAbs).length).bits)
      = (Computability.encodeNat a.natAbs).length := ofBits_bits _
  refine ⟨.int (((Computability.encodeNat a.natAbs).length : ℕ) : ℤ) :: rest, s4,
    1 + (c2 + (c3 + c4)), ⟨a, rest, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [encodeNat_length]
  · exact Eval.seq e1 (Eval.seq he2 (Eval.seq he3 he4))
  · have hc2' : c2 ≤ Kc * (a.natAbs.size + 1) := by
      have h := hc2; rwa [encodeNat_length] at h
    have hc3' : c3 ≤ Kh * (a.natAbs.size + 1) := by
      have h := hc3; rwa [encodeNat_length] at h
    have hc4' : c4 ≤ Ke * (a.natAbs.size + 1) := by
      have h := hc4
      rw [List.length_reverse, Nat.size_eq_bits_len, encodeNat_length] at h
      have hsz : (a.natAbs.size).size ≤ a.natAbs.size := by
        rw [Nat.size_le]; exact Nat.lt_two_pow_self
      exact le_trans h (Nat.mul_le_mul_left _ (by omega))
    have hsum : (c2 + c3) + c4 ≤ (Kc + Kh + Ke) * (a.natAbs.size + 1) := by
      have h := Nat.add_le_add (Nat.add_le_add hc2' hc3') hc4'
      calc (c2 + c3) + c4
          ≤ (Kc * (a.natAbs.size + 1) + Kh * (a.natAbs.size + 1))
              + Ke * (a.natAbs.size + 1) := h
        _ = (Kc + Kh + Ke) * (a.natAbs.size + 1) := by ring
    show 1 + (c2 + (c3 + c4)) ≤ (Kc + Kh + Ke + 1) * isz a
    rw [isz_eq]
    have hgoal : (Kc + Kh + Ke + 1) * (a.natAbs.size + 2)
        = (Kc + Kh + Ke) * (a.natAbs.size + 1)
          + ((Kc + Kh + Ke) + (a.natAbs.size + 2)) := by ring
    rw [hgoal]
    omega
  · rw [hs4_0, List.reverse_reverse, hofBits]
    simp [HvdH.encs, List.append_assoc]
  · intro k hk0
    by_cases h1 : k = 1
    · subst h1
      rw [hs4_1]
      exact hs1_oth 1 (by decide)
    by_cases h2 : k = 2
    · subst h2
      rw [hs4_oth 2 (by decide) (by decide) (by decide), hs3_2,
        hs2_oth 2 (by decide) (by decide)]
      exact hs1_oth 2 (by decide)
    by_cases h3 : k = 3
    · subst h3
      rw [hs4_3, hs2_oth 3 (by decide) (by decide)]
      exact hs1_oth 3 (by decide)
    · rw [hs4_oth k hk0 h1 h3, hs3_oth k h1 h2 h3, hs2_oth k hk0 h1]
      exact hs1_oth k hk0




/-! ## `clog 2` -/

theorem sizeWord_clog : ∃ (p : Cmd) (K : ℕ), ∀ main : Cmd, UnOp main p (fun a => 0 ≤ a)
    (fun a => (Nat.clog 2 a.toNat : ℤ)) (fun a => K * isz a) := by
  obtain ⟨pSize, KS, hSize⟩ := sizeWord_size
  obtain ⟨pDec, KD, hDec⟩ := decValue
  refine ⟨.seq (.pop 0 rSign)
      (.seq (.peek 0 rFlag)
        (.ite rFlag Glyph.iend
          (.seq (.pop 0 rFlag) (.seq (.set rIend Glyph.iend) (.seq (.push 0 rIend)
            (.seq (.set rPos Glyph.pos) (.push 0 rPos)))))
          (.seq (.push 0 rSign) (.seq pDec pSize)))), KD + KD + KS + 8, ?_⟩
  intro main vs hpre s R hR
  obtain ⟨a, rest, rfl, ha⟩ := hpre
  have hR' : s.stk 0 = Glyph.pos ::
      ((Computability.encodeNat a.natAbs).map Glyph.bit ++ [Glyph.iend]) ++ (encs rest ++ R) := by
    rw [hR]
    simp only [HvdH.encs, List.map_cons, List.flatten_cons]
    rw [enc_int_pos ha]
    simp [List.append_assoc]
  have hsg : (s.stk 0).headD .eos = Glyph.pos := by rw [hR']; simp
  let s1 : State := (s.updStk 0 (s.stk 0).tail).updReg rSign ((s.stk 0).headD .eos)
  have e1 : Eval main (.pop 0 rSign) s s1 1 := by
    have hh := Eval.pop (main := main) 0 rSign s
    simpa [s1, State.updStk, State.updReg] using hh
  have hs1reg : s1.reg rSign = Glyph.pos := by
    simp only [s1]
    exact hsg
  have hs1 : s1.stk 0 = (Computability.encodeNat a.natAbs).map Glyph.bit ++ [Glyph.iend] ++
      (encs rest ++ R) := by
    simp [s1, State.updStk, State.updReg, hR']
  have hs1_oth : ∀ k : Stk, k ≠ 0 → s1.stk k = s.stk k := by
    intro k hk
    simp [s1, State.updStk, State.updReg, hk]
  let s2 : State := s1.updReg rFlag ((s1.stk 0).headD .eos)
  have e2 : Eval main (.peek 0 rFlag) s1 s2 1 := by
    have hh := Eval.peek (main := main) 0 rFlag s1
    simpa [s2, State.updReg] using hh
  have hs2 : s2.stk 0 = s1.stk 0 := by simp [s2, State.updReg]
  have hs2_oth : ∀ k : Stk, k ≠ 0 → s2.stk k = s1.stk k := by
    intro k hk; simp [s2, State.updReg]
  have hs2reg : s2.reg rFlag = (s1.stk 0).headD .eos := by simp [s2, State.updReg]
  have hs2regSign : s2.reg rSign = Glyph.pos := by
    simp only [s2, State.updReg_apply, if_neg rSign_ne_rFlag]
    exact hs1reg
  have hstk0 : s.stk 0 = encs (HvdH.Val.int a :: rest) ++ R := by
    simpa [HvdH.encs, List.map_cons, List.flatten_cons] using hR
  by_cases hz : a = 0
  · -- `a = 0`: stack 0 is `iend :: below0`
    subst hz
    have hb0 : Computability.encodeNat ((0 : ℤ).natAbs) = [] := by
      rw [encodeNat_eq_nil_iff]; simp
    have hhead : (s1.stk 0).headD .eos = Glyph.iend := by
      rw [hs1, hb0]; simp
    let t1 : State := (s2.updStk 0 (s2.stk 0).tail).updReg rFlag ((s2.stk 0).headD .eos)
    have f1 : Eval main (.pop 0 rFlag) s2 t1 1 := by
      have hh := Eval.pop (main := main) 0 rFlag s2
      simpa [t1, State.updStk, State.updReg] using hh
    have htail : (s2.stk 0).tail = encs rest ++ R := by
      rw [hs2, hs1, hb0]; simp
    have ht1 : t1.stk 0 = encs rest ++ R := by
      simp [t1, State.updStk, State.updReg, htail]
    have ht1_oth : ∀ k : Stk, k ≠ 0 → t1.stk k = s2.stk k := by
      intro k hk
      simp [t1, State.updStk, State.updReg, hk]
    let t2 : State := t1.updReg rIend Glyph.iend
    have f2 : Eval main (.set rIend Glyph.iend) t1 t2 1 := Eval.set_eq
    let t3 : State := t2.updStk 0 (Glyph.iend :: t2.stk 0)
    have f3 : Eval main (.push 0 rIend) t2 t3 1 := by
      refine Eval.push_eq (main := main) ?_
      simp [t2, State.updReg]
    let t4 : State := t3.updReg rPos Glyph.pos
    have f4 : Eval main (.set rPos Glyph.pos) t3 t4 1 := Eval.set_eq
    let t5 : State := t4.updStk 0 (Glyph.pos :: t4.stk 0)
    have f5 : Eval main (.push 0 rPos) t4 t5 1 := by
      refine Eval.push_eq (main := main) ?_
      simp [t4, State.updReg]
    have ht5 : t5.stk 0 = Glyph.pos :: Glyph.iend :: (encs rest ++ R) := by
      simp [t5, t4, t3, t2, State.updStk, State.updReg, ht1]
    have h0enc : (HvdH.Val.int 0).enc = [Glyph.pos, Glyph.iend] := by
      rw [enc_int_pos (le_refl (0 : ℤ)), hb0]
      simp
    refine ⟨.int 0 :: rest, t5, 1 + (1 + ((1 + (1 + (1 + (1 + 1)))) + 1)), ⟨0, rest, rfl, ?_⟩,
      ?_, ?_, ?_, ?_⟩
    · simp
    · refine Eval.seq e1 (Eval.seq e2 (Eval.iteT ?_
        (Eval.seq f1 (Eval.seq f2 (Eval.seq f3 (Eval.seq f4 f5))))))
      rw [hs2reg, hhead]
    · show 1 + (1 + ((1 + (1 + (1 + (1 + 1)))) + 1)) ≤ (KD + KD + KS + 8) * isz (0 : ℤ)
      rw [isz_eq]
      simp only [Int.natAbs_zero, Nat.size_zero, Nat.add_zero]
      omega
    · rw [ht5]
      conv_rhs => rw [show encs (HvdH.Val.int 0 :: rest)
          = (HvdH.Val.int 0).enc ++ encs rest from rfl, h0enc]
      simp
    · intro k hk0
      rw [show t5.stk k = t4.stk k from by simp [t5, State.updStk, State.updReg, hk0],
          show t4.stk k = t3.stk k from by simp [t4, State.updReg],
          show t3.stk k = t2.stk k from by simp [t3, State.updStk, State.updReg, hk0],
          show t2.stk k = t1.stk k from by simp [t2, State.updReg],
          ht1_oth k hk0, hs2_oth k hk0]
      exact hs1_oth k hk0
  · -- `a ≠ 0`, `0 ≤ a`: the head is `bit b`
    have han : a.natAbs ≠ 0 := fun h => hz (Int.natAbs_eq_zero.mp h)
    obtain ⟨b, bs, hb⟩ : ∃ b bs, Computability.encodeNat a.natAbs = b :: bs := by
      cases h : Computability.encodeNat a.natAbs with
      | nil => exact absurd ((encodeNat_eq_nil_iff _).mp h) han
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hhead : (s1.stk 0).headD .eos = Glyph.bit b := by rw [hs1, hb]; simp
    have hne : (s1.stk 0).headD .eos ≠ Glyph.iend := by rw [hhead]; exact bit_ne_iend b
    have ha1 : (1 : ℤ) ≤ a := by
      rcases lt_or_eq_of_le ha with h | h
      · omega
      · exact absurd h.symm hz
    have hdec : a = (((a.toNat - 1 : ℕ)) : ℤ) + 1 := by
      have hcast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
      have h1 : 1 ≤ a.toNat := by omega
      omega
    have hpreD : HvdH.Val.int a :: rest = HvdH.Val.int (↑(a.toNat - 1) + 1) :: rest := by
      simp only [List.cons.injEq, HvdH.Val.int.injEq, and_true]
      exact hdec
    -- restore the sign so that the decrement word sees the complete encoding
    let u1 : State := s2.updStk 0 (Glyph.pos :: s2.stk 0)
    have f1 : Eval main (.push 0 rSign) s2 u1 1 := by
      refine Eval.push_eq (main := main) ?_
      simp [u1, State.updReg, State.updStk, hs2regSign]
    have hu1 : u1.stk 0 = encs (HvdH.Val.int a :: rest) ++ R := by
      have h1 : u1.stk 0 = Glyph.pos :: ((Computability.encodeNat a.natAbs).map Glyph.bit
          ++ [Glyph.iend] ++ (encs rest ++ R)) := by
        simp [u1, State.updStk, State.updReg, hs2, hs1]
      rw [h1]
      conv_rhs => rw [show encs (HvdH.Val.int a :: rest)
          = (HvdH.Val.int a).enc ++ encs rest from rfl, enc_int_pos ha]
      simp [List.append_assoc]
    have hu1_oth : ∀ k : Stk, k ≠ 0 → u1.stk k = s2.stk k := by
      intro k hk
      simp [u1, State.updStk, State.updReg, hk]
    obtain ⟨outD, s3, cD, hDecPost, heD, hcD, hs3_0, hs3_oth⟩ :=
      hDec main (HvdH.Val.int a :: rest) ⟨a.toNat - 1, rest, hpreD⟩ u1 R hu1
    obtain ⟨nD, restD, hn1, houtD⟩ := hDecPost
    have hvalD : a = ((nD : ℕ) : ℤ) + 1 := HvdH.Val.int.inj (by
      have := congrArg (fun l : List HvdH.Val => l.headD HvdH.Val.nil) hn1
      simpa using this)
    have hrestD : restD = rest := (by
      have h := congrArg (fun l : List HvdH.Val => l.tail) hn1
      simpa using h : rest = restD).symm
    have hnD : nD = a.toNat - 1 := by
      have h3 : ((nD : ℕ) : ℤ) = ((a.toNat - 1 : ℕ) : ℤ) := by
        have h := hvalD.symm.trans hdec
        omega
      have h1 : 1 ≤ a.toNat := by
        have hcast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
        omega
      omega
    obtain ⟨outS, s4, cS, hSizePost, heS, hcS, hs4_0, hs4_oth⟩ :=
      hSize main outD ⟨nD, restD, houtD, trivial⟩ s3 R hs3_0
    obtain ⟨zs, restS, hzvis, houtS⟩ := hSizePost
    have hzs : zs = ((nD : ℕ) : ℤ) := (HvdH.Val.int.inj (by
      have h := congrArg (fun l : List HvdH.Val => l.headD HvdH.Val.nil)
        (houtD.symm.trans hzvis)
      simpa using h)).symm
    have hrestS : restS = rest := by
      have h1 : restD = restS := by
        have h := congrArg (fun l : List HvdH.Val => l.tail) (houtD.symm.trans hzvis)
        simpa using h
      rw [← h1, hrestD]
    have hclog : (Nat.clog 2 a.toNat : ℤ) = ((nD : ℤ).natAbs.size : ℤ) := by
      have h1 : (a - 1).natAbs = a.toNat - 1 := by
        have hcast : a - 1 = ((a.toNat - 1 : ℕ) : ℤ) := by omega
        rw [hcast, Int.natAbs_natCast]
      rw [clog_two_int ha1, h1, Int.natAbs_natCast, hnD]
    have houtS' : outS = HvdH.Val.int (↑(Nat.clog 2 a.toNat)) :: rest := by
      rw [houtS, hrestS, hzs]
      dsimp only
      rw [hclog]
    refine ⟨outS, s4, 1 + (1 + ((1 + (cD + cS)) + 1)), ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨a, rest, rfl, houtS'⟩
    · refine Eval.seq e1 (Eval.seq e2 (Eval.iteF ?_ (Eval.seq f1 (Eval.seq heD heS))))
      rw [hs2reg]; exact hne
    · have hcD' : cD ≤ KD * (isz a + 1) := by
        have h := hcD
        simpa [HvdH.vsz, vsz_int] using h
      have hIsz : isz ((nD : ℕ) : ℤ) ≤ isz a := by
        rw [isz_eq, isz_eq, Int.natAbs_natCast, hnD, natAbs_of_nonneg' ha]
        have hmono := Nat.size_le_size (show a.toNat - 1 ≤ a.toNat by omega)
        omega
      have hcS' : cS ≤ KS * isz a := by
        have h := hcS
        rw [houtD] at h
        calc cS ≤ KS * isz ((nD : ℕ) : ℤ) := h
          _ ≤ KS * isz a := Nat.mul_le_mul_left _ hIsz
      show 1 + (1 + ((1 + (cD + cS)) + 1)) ≤ (KD + KD + KS + 8) * isz a
      have h2 : 2 ≤ isz a := isz_nonneg a
      nlinarith [hcD', hcS', h2, Nat.zero_le KD, Nat.zero_le KS]
    · exact hs4_0
    · intro k hk0
      rw [hs4_oth k hk0, hs3_oth k hk0, hu1_oth k hk0, hs2_oth k hk0]
      exact hs1_oth k hk0

/-! ## `pow2` -/

theorem sizeWord_pow2 : ∃ (p : Cmd) (K : ℕ), ∀ main : Cmd, UnOp main p (fun k => 0 ≤ k)
    (fun k => 2 ^ k.toNat) (fun k => K * (k.toNat + isz k)) := by
  obtain ⟨pBU, KB, hBU⟩ := sizeBinUnary
  obtain ⟨pEZ, KE, hEZ⟩ := sizeEmitZeros
  refine ⟨.seq pBU pEZ, KB + KE + KB + 12, ?_⟩
  intro main vs hpre s R hR
  obtain ⟨k, rest, rfl, hk⟩ := hpre
  have hnatAbs : k.natAbs = k.toNat := natAbs_of_nonneg' hk
  have hR' : s.stk 0 = Glyph.pos ::
      ((Computability.encodeNat k.natAbs).map Glyph.bit ++ [Glyph.iend]) ++ (encs rest ++ R) := by
    rw [hR]
    simp only [HvdH.encs, List.map_cons, List.flatten_cons]
    rw [enc_int_pos hk]
    simp [List.append_assoc]
  obtain ⟨s2, cB, heB, hcB, hs2_0, hs2_1, hs2_oth⟩ :=
    hBU main k.toNat Glyph.pos (encs rest ++ R) (s.stk 1) s
      (by rw [hR', hnatAbs]; simp [List.append_assoc]) rfl
  obtain ⟨s3, cE, heE, hcE, hs3_0, hs3_1, hs3_oth⟩ :=
    hEZ main k.toNat (encs rest ++ R) (s.stk 1) s2 hs2_0 hs2_1
  have henc : (HvdH.Val.int (((2 ^ k.toNat : ℕ) : ℤ))).enc = Glyph.pos ::
      List.replicate k.toNat (Glyph.bit false) ++ [Glyph.bit true, Glyph.iend] := by
    rw [enc_int_pos (by positivity : (0 : ℤ) ≤ ((2 ^ k.toNat : ℕ) : ℤ))]
    simp only [Int.natAbs_natCast]
    rw [encodeNat_eq_bits, bits_two_pow]
    simp [List.map_append]
  refine ⟨.int ((2 ^ k.toNat : ℕ) : ℤ) :: rest, s3, cB + cE, ⟨k, rest, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [List.cons.injEq, HvdH.Val.int.injEq, and_true]
    push_cast
    rfl
  · exact Eval.seq heB heE
  · have hcB' : cB ≤ KB * (k.toNat + (k.toNat).size + 1) := hcB
    have hcE' : cE ≤ KE * (k.toNat + 1) := hcE
    show cB + cE ≤ (KB + KE + KB + 12) * (k.toNat + isz k)
    rw [isz_eq, hnatAbs]
    nlinarith [hcB', hcE', Nat.zero_le KB, Nat.zero_le KE]
  · rw [hs3_0]
    simp only [HvdH.encs, List.map_cons, List.flatten_cons]
    rw [henc]
    simp [List.append_assoc]
  · intro j hj0
    by_cases hj1 : j = 1
    · subst hj1
      rw [hs3_1]
    · rw [hs3_oth j hj0 hj1, hs2_oth j hj0 hj1]

end Size

theorem sizeWord : (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.UnOp main p (fun _ => True) (fun a => (a.natAbs.size : ℤ)) (fun a => K * HvdH.isz a)) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.UnOp main p (fun a => 0 ≤ a) (fun a => (Nat.clog 2 a.toNat : ℤ)) (fun a => K * HvdH.isz a)) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.UnOp main p (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat) (fun k => K * (k.toNat + HvdH.isz k))) := by
  exact ⟨Size.sizeWord_size, Size.sizeWord_clog, Size.sizeWord_pow2⟩

end Work.IntLib
