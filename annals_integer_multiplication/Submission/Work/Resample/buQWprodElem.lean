import Mathlib
import Submission.Work.Resample.buQWstepKit
import Submission.Work.Resample.buQWmulWord

/-!
# `Work.Resample.buQWprodElem`: the exact product of a tabulated weight by a fixed-point value

For a weight `c : ℤ` and a fixed-point pair `w : ℤ × ℤ`, the word multiplies `w` by `c` exactly
(one `self` call on the magnitudes with the sign fixed afterwards), turning the window
`[int c, cfxVal w]` into `[cfxVal (c * w.1, c * w.2)]` at cost `Kc * (Cm (Kc*p) + p + 1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

theorem buQWprodElem (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p : ℕ) (c : ℤ) (w : ℤ × ℤ),
      Monotone Cm → HvdH.MulBelow main N Cm → 100 ≤ p → Kc * p < N →
      HvdH.isz c ≤ p + 3 → w.1.natAbs.size ≤ p + 3 → w.2.natAbs.size ≤ p + 3 →
      Work.Resample.Pipe main q [HvdH.Val.int c, HvdH.cfxVal w]
        [HvdH.cfxVal (c * w.1, c * w.2)] (Kc * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨mulP, kmul, hmul⟩ := buQWmulWord KL IL
  obtain ⟨dupP, kdup, hdup⟩ := KL.dup
  obtain ⟨rollP, kroll, hroll⟩ := KL.roll
  obtain ⟨unconsP, kunc, hunc⟩ := KL.unconsV
  obtain ⟨consP, kcons, hcons⟩ := KL.consV
  obtain ⟨swapP, kswap, hswap⟩ := KL.swap
  let KS : ℕ := kmul + kdup + kroll + kunc + kcons + kswap + 100
  let KC : ℕ := 1000000 * KS
  have hKS100 : 100 ≤ KS := by simp only [KS]; omega
  have hKSm : kmul ≤ KS ∧ kdup ≤ KS ∧ kroll ≤ KS ∧ kunc ≤ KS ∧ kcons ≤ KS ∧ kswap ≤ KS := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [KS] <;> omega
  obtain ⟨hkmul_le, hkdup_le, hkroll_le, hkunc_le, hkcons_le, hkswap_le⟩ := hKSm
  have hchain : 11000 * KS + 8 * kmul ≤ KC := by simp only [KC]; nlinarith
  refine ⟨.seq swapP (.seq unconsP (.seq (rollP 2) (.seq dupP (.seq (rollP 2) (.seq (rollP 1)
    (.seq mulP (.seq (rollP 1) (.seq (rollP 2) (.seq (rollP 1) (.seq mulP
    (.seq swapP consP))))))))))), KC, ?_⟩
  intro main N Cm p c w hmono hmb hp hKN hc hw1 hw2
  have hCN : c.natAbs < 2 ^ (p + 1) := buQW_natAbs_lt_of_isz_le (k := p + 1) hc
  have h1N : w.1.natAbs < 2 ^ (p + 3) := by simpa [Nat.size_le] using hw1
  have h2N : w.2.natAbs < 2 ^ (p + 3) := by simpa [Nat.size_le] using hw2
  have hisz1 : isz w.1 ≤ p + 5 := by simp only [isz]; omega
  have hisz2 : isz w.2 ≤ p + 5 := by simp only [isz]; omega
  obtain ⟨hm1, hm2⟩ : isz (c * w.1) ≤ 2 * p + 6 ∧ isz (c * w.2) ≤ 2 * p + 6 :=
    ⟨by have := buQW_isz_mul_le hCN h1N; omega,
     by have := buQW_isz_mul_le hCN h2N; omega⟩
  have hKC2 : 2 ≤ KC := by simp only [KC]; nlinarith
  have hPN : p + 3 < N := by
    have h1 : 2 * p ≤ KC * p := Nat.mul_le_mul_right p hKC2
    omega
  have hkm : kmul * (p + 3) ≤ KC * p := by
    have h4 : 4 * kmul ≤ KC := by omega
    calc kmul * (p + 3) ≤ kmul * (4 * p) := Nat.mul_le_mul_left _ (by omega)
      _ = (4 * kmul) * p := by ring
      _ ≤ KC * p := Nat.mul_le_mul_right _ h4
  have hmulP : ∀ (a b : ℤ), a.natAbs.size ≤ p + 3 → b.natAbs.size ≤ p + 3 →
      Pipe main mulP [.int a, .int b] [.int (a * b)]
        (kmul * (Cm (kmul * (p + 3)) + (p + 3) + 1)) := by
    intro a b ha hb
    exact buPipe_int2 (hmul main N Cm (p + 3) a b hmono hmb hPN ha hb)
  -- size bounds of all values occurring
  have hcsize : c.natAbs.size ≤ p + 3 := by simp only [isz] at hc; omega
  have hszc : vsz (.int c) ≤ 2 * p + 12 := by rw [Work.Fx.vsz_int]; omega
  have hsza : vsz (.int w.1) ≤ 2 * p + 12 := by rw [Work.Fx.vsz_int]; omega
  have hszb : vsz (.int w.2) ≤ 2 * p + 12 := by rw [Work.Fx.vsz_int]; omega
  have hszW : vsz (cfxVal w) ≤ 2 * p + 12 := by rw [Work.Fx.vsz_cfxVal]; omega
  have hszm1 : vsz (.int (c * w.1)) ≤ 2 * p + 12 := by rw [Work.Fx.vsz_int]; omega
  have hszm2 : vsz (.int (c * w.2)) ≤ 2 * p + 12 := by rw [Work.Fx.vsz_int]; omega
  -- step 1: swap
  have s1 : Pipe main swapP [.int c, cfxVal w] [cfxVal w, .int c] (KS * (1000 * (p + 1))) := by
    refine Pipe.le (Pipe.swap main hswap (Val.int c) (cfxVal w)) ?_
    rw [Work.Fx.vsz_int, Work.Fx.vsz_cfxVal]
    have hbr : isz c + (isz w.1 + isz w.2 + 1) + 1 ≤ 1000 * (p + 1) := by omega
    exact Nat.mul_le_mul hkswap_le hbr
  -- step 2: unconsV
  have s2 : Pipe main unconsP [cfxVal w, .int c] [.int w.1, .int w.2, .int c]
      (KS * (1000 * (p + 1))) := by
    refine Pipe.le (Pipe.unconsVA main hunc) ?_
    have h1000 : 1 ≤ 1000 * (p + 1) := by omega
    have h2 := Nat.mul_le_mul_left KS h1000
    rw [Nat.mul_one] at h2
    exact le_trans hkunc_le h2
  -- step 3: roll 2
  have s3 : Pipe main (rollP 2) [.int w.1, .int w.2, .int c] [.int c, .int w.1, .int w.2]
      (KS * (1000 * (p + 1))) := by
    have hk : 2 < ([.int w.1, .int w.2, .int c] : List Val).length := by simp
    have hpost : ([.int w.1, .int w.2, .int c] : List Val).getD 2 .nil ::
        ([.int w.1, .int w.2, .int c] : List Val).eraseIdx 2 = [.int c, .int w.1, .int w.2] := by
      simp
    refine Pipe.le (Pipe.rollA main hroll (A := [.int w.1, .int w.2, .int c]) hk hpost) ?_
    have hsz : Work.Fx.szl (([.int w.1, .int w.2, .int c] : List Val).take (2 + 1)) ≤ 10 * p + 60 := by
      refine le_trans (buQW_szl_le_of (A := [.int w.1, .int w.2, .int c]) (2 * p + 12) ?_) (by omega)
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      exacts [hsza, hszb, hszc]
    exact buQW_op_le hkroll_le hsz 2 (by omega)
  -- step 4: dup
  have s4 : Pipe main dupP [.int c, .int w.1, .int w.2] [.int c, .int c, .int w.1, .int w.2]
      (KS * (1000 * (p + 1))) := by
    refine Pipe.le (Pipe.appendTail [Val.int w.1, Val.int w.2] (Pipe.dup main hdup (Val.int c))) ?_
    rw [Work.Fx.vsz_int]
    have hbr : isz c + 1 ≤ 1000 * (p + 1) := by omega
    exact Nat.mul_le_mul hkdup_le hbr
  -- step 5: roll 2
  have s5 : Pipe main (rollP 2) [.int c, .int c, .int w.1, .int w.2]
      [.int w.1, .int c, .int c, .int w.2] (KS * (1000 * (p + 1))) := by
    have hk : 2 < ([.int c, .int c, .int w.1, .int w.2] : List Val).length := by simp
    have hpost : ([.int c, .int c, .int w.1, .int w.2] : List Val).getD 2 .nil ::
        ([.int c, .int c, .int w.1, .int w.2] : List Val).eraseIdx 2 =
        [.int w.1, .int c, .int c, .int w.2] := by simp
    refine Pipe.le (Pipe.rollA main hroll (A := [.int c, .int c, .int w.1, .int w.2]) hk hpost) ?_
    have hsz : Work.Fx.szl (([.int c, .int c, .int w.1, .int w.2] : List Val).take (2 + 1)) ≤ 10 * p + 60 := by
      refine le_trans (buQW_szl_le_of (A := [.int c, .int c, .int w.1, .int w.2]) (2 * p + 12) ?_) (by omega)
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hszc, hszc, hsza, hszb]
    exact buQW_op_le hkroll_le hsz 2 (by omega)
  -- step 6: roll 1
  have s6 : Pipe main (rollP 1) [.int w.1, .int c, .int c, .int w.2]
      [.int c, .int w.1, .int c, .int w.2] (KS * (1000 * (p + 1))) := by
    have hk : 1 < ([.int w.1, .int c, .int c, .int w.2] : List Val).length := by simp
    have hpost : ([.int w.1, .int c, .int c, .int w.2] : List Val).getD 1 .nil ::
        ([.int w.1, .int c, .int c, .int w.2] : List Val).eraseIdx 1 =
        [.int c, .int w.1, .int c, .int w.2] := by simp
    refine Pipe.le (Pipe.rollA main hroll (A := [.int w.1, .int c, .int c, .int w.2]) hk hpost) ?_
    have hsz : Work.Fx.szl (([.int w.1, .int c, .int c, .int w.2] : List Val).take (1 + 1)) ≤ 10 * p + 60 := by
      refine le_trans (buQW_szl_le_of (A := [.int w.1, .int c, .int c, .int w.2]) (2 * p + 12) ?_) (by omega)
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      exacts [hsza, hszc, hszc, hszb]
    exact buQW_op_le hkroll_le hsz 1 (by omega)
  -- step 7: mul
  have s7 : Pipe main mulP [.int c, .int w.1, .int c, .int w.2] [.int (c * w.1), .int c, .int w.2]
      (kmul * (Cm (kmul * (p + 3)) + (p + 3) + 1)) :=
    Pipe.appendTail [Val.int c, Val.int w.2] (hmulP c w.1 hcsize hw1)
  -- step 8: roll 1
  have s8 : Pipe main (rollP 1) [.int (c * w.1), .int c, .int w.2] [.int c, .int (c * w.1), .int w.2]
      (KS * (1000 * (p + 1))) := by
    have hk : 1 < ([.int (c * w.1), .int c, .int w.2] : List Val).length := by simp
    have hpost : ([.int (c * w.1), .int c, .int w.2] : List Val).getD 1 .nil ::
        ([.int (c * w.1), .int c, .int w.2] : List Val).eraseIdx 1 =
        [.int c, .int (c * w.1), .int w.2] := by simp
    refine Pipe.le (Pipe.rollA main hroll (A := [.int (c * w.1), .int c, .int w.2]) hk hpost) ?_
    have hsz : Work.Fx.szl (([.int (c * w.1), .int c, .int w.2] : List Val).take (1 + 1)) ≤ 10 * p + 60 := by
      refine le_trans (buQW_szl_le_of (A := [.int (c * w.1), .int c, .int w.2]) (2 * p + 12) ?_) (by omega)
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      exacts [hszm1, hszc, hszb]
    exact buQW_op_le hkroll_le hsz 1 (by omega)
  -- step 9: roll 2
  have s9 : Pipe main (rollP 2) [.int c, .int (c * w.1), .int w.2]
      [.int w.2, .int c, .int (c * w.1)] (KS * (1000 * (p + 1))) := by
    have hk : 2 < ([.int c, .int (c * w.1), .int w.2] : List Val).length := by simp
    have hpost : ([.int c, .int (c * w.1), .int w.2] : List Val).getD 2 .nil ::
        ([.int c, .int (c * w.1), .int w.2] : List Val).eraseIdx 2 =
        [.int w.2, .int c, .int (c * w.1)] := by simp
    refine Pipe.le (Pipe.rollA main hroll (A := [.int c, .int (c * w.1), .int w.2]) hk hpost) ?_
    have hsz : Work.Fx.szl (([.int c, .int (c * w.1), .int w.2] : List Val).take (2 + 1)) ≤ 10 * p + 60 := by
      refine le_trans (buQW_szl_le_of (A := [.int c, .int (c * w.1), .int w.2]) (2 * p + 12) ?_) (by omega)
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      exacts [hszc, hszm1, hszb]
    exact buQW_op_le hkroll_le hsz 2 (by omega)
  -- step 10: roll 1
  have s10 : Pipe main (rollP 1) [.int w.2, .int c, .int (c * w.1)]
      [.int c, .int w.2, .int (c * w.1)] (KS * (1000 * (p + 1))) := by
    have hk : 1 < ([.int w.2, .int c, .int (c * w.1)] : List Val).length := by simp
    have hpost : ([.int w.2, .int c, .int (c * w.1)] : List Val).getD 1 .nil ::
        ([.int w.2, .int c, .int (c * w.1)] : List Val).eraseIdx 1 =
        [.int c, .int w.2, .int (c * w.1)] := by simp
    refine Pipe.le (Pipe.rollA main hroll (A := [.int w.2, .int c, .int (c * w.1)]) hk hpost) ?_
    have hsz : Work.Fx.szl (([.int w.2, .int c, .int (c * w.1)] : List Val).take (1 + 1)) ≤ 10 * p + 60 := by
      refine le_trans (buQW_szl_le_of (A := [.int w.2, .int c, .int (c * w.1)]) (2 * p + 12) ?_) (by omega)
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      exacts [hszb, hszc, hszm1]
    exact buQW_op_le hkroll_le hsz 1 (by omega)
  -- step 11: mul
  have s11 : Pipe main mulP [.int c, .int w.2, .int (c * w.1)] [.int (c * w.2), .int (c * w.1)]
      (kmul * (Cm (kmul * (p + 3)) + (p + 3) + 1)) :=
    Pipe.appendTail [Val.int (c * w.1)] (hmulP c w.2 hcsize hw2)
  -- step 12: swap
  have s12 : Pipe main swapP [.int (c * w.2), .int (c * w.1)] [.int (c * w.1), .int (c * w.2)]
      (KS * (1000 * (p + 1))) := by
    refine Pipe.le (Pipe.swap main hswap (Val.int (c * w.2)) (Val.int (c * w.1))) ?_
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
    have hbr : isz (c * w.2) + isz (c * w.1) + 1 ≤ 1000 * (p + 1) := by omega
    exact Nat.mul_le_mul hkswap_le hbr
  -- step 13: consV
  have s13 : Pipe main consP [.int (c * w.1), .int (c * w.2)] [cfxVal (c * w.1, c * w.2)]
      (KS * (1000 * (p + 1))) := by
    refine Pipe.le (Pipe.consVA main hcons) ?_
    have h1000 : 1 ≤ 1000 * (p + 1) := by omega
    have h2 := Nat.mul_le_mul_left KS h1000
    rw [Nat.mul_one] at h2
    exact le_trans hkcons_le h2
  have hch := buQW_chain_le (KS := KS) (kmul := kmul) (KC := KC) (p := p) (Cm := Cm) hmono hchain hkm
  have hcomp := Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 (Pipe.comp s11 (Pipe.comp s12 s13)))))))))))
  exact Pipe.le hcomp (by nlinarith [hch, Nat.zero_le p, Nat.zero_le KS])

end Work.Resample
