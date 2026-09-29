import Mathlib
import Submission.Work.Resample.buHornerKit

/-!
# `Work.Resample.buHornerPrePipe`: the pre-pipe of the Horner word

The word `buHornerPrePipe` takes the pair `[int Z, int p]` off the value stack and pushes
`[int (auEn p), int (auNstep p), int (auEn p), int Z, int p]` back on it, at a cost bounded by
`K (p+1)^K` for a constant `K` depending only on the library witnesses `KL` and `IL`.

It is the setup phase of the Horner recursion `auH p Z (auNstep p)` of `Work.Resample.buHornerWord`:
`auEn p = 2^auPrec p` is the numerator `2^auPrec p` of the recursion and `auNstep p = 2·auPrec p`
the number of steps; the second copy of `auEn p` is the running value of `auH p Z 0` (the initial
iterate is `2^auPrec p`).

The program computes `t = 3p + 100` from `p`, `auNstep p = 2t` from one copy of `t`, `auEn p = 2^t`
from another, duplicates the latter, removes the scratch copy of `p`, and is therefore exactly the
sixteen `Pipe` steps chained below; every intermediate value has `isz ≤ buSZ p`, so each step costs
at most `buHSB p KS` (`le_buSB_one`, `le_buSB_two`, `le_buSB_mul`, `le_buSB_roll`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.Resample

open HvdH

/-! ## Size estimates -/

/-- A natural of at most `p + 30` bits fits the uniform size bound `buSZ p`. -/
theorem isz_natCast_le_buSZ_p30 {p n : ℕ} (h : n ≤ 2 ^ (p + 30)) : isz (((n : ℕ) : ℤ)) ≤ buSZ p :=
  isz_le_buSZ_of (A := p + 30) (by simp only [buSZ]; omega) (by rwa [Int.natAbs_natCast])

theorem isz_three_mul_p_le_buSZ (p : ℕ) : isz (3 * (p : ℤ)) ≤ buSZ p := by
  rw [show (3 * (p : ℤ)) = (((3 * p : ℕ) : ℤ)) by push_cast; ring]
  refine isz_natCast_le_buSZ_p30 ?_
  calc 3 * p ≤ 103 * 2 ^ p := by linarith [three_mul_add_le p]
    _ ≤ 2 ^ 30 * 2 ^ p := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (p + 30) := by rw [← pow_add]; ring_nf

theorem isz_W1_le_buSZ (p : ℕ) : isz (100 + 3 * (p : ℤ)) ≤ buSZ p := by
  rw [show (100 + 3 * (p : ℤ)) = (((3 * p + 100 : ℕ) : ℤ)) by push_cast; ring]
  refine isz_natCast_le_buSZ_p30 ?_
  calc 3 * p + 100 ≤ 103 * 2 ^ p := three_mul_add_le p
    _ ≤ 2 ^ 30 * 2 ^ p := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (p + 30) := by rw [← pow_add]; ring_nf

theorem isz_W2_le_buSZ (p : ℕ) : isz (2 * (100 + 3 * (p : ℤ))) ≤ buSZ p := by
  rw [show (2 * (100 + 3 * (p : ℤ))) = (((2 * (3 * p + 100) : ℕ) : ℤ)) by push_cast; ring]
  refine isz_natCast_le_buSZ_p30 ?_
  calc 2 * (3 * p + 100) ≤ 2 * (103 * 2 ^ p) := Nat.mul_le_mul_left 2 (three_mul_add_le p)
    _ = 206 * 2 ^ p := by ring
    _ ≤ 2 ^ 30 * 2 ^ p := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (p + 30) := by rw [← pow_add]; ring_nf

/-! ## Cost absorption -/

/-- The uniform one-step budget is bounded by a plain power of `p + 1`. -/
theorem buSB_le_pow_q (p KS : ℕ) : buHSB p KS ≤ (KS * 1000000 ^ 2) * (p + 1) ^ 4 := by
  have hexp : (p + 1) ^ 2 = p * p + 2 * p + 1 := by ring
  have h : buSZ p + 8 ≤ 1000000 * (p + 1) ^ 2 := by
    rw [hexp]; simp only [buSZ]; nlinarith [Nat.zero_le p]
  calc buHSB p KS = KS * (buSZ p + 8) ^ 2 := rfl
    _ ≤ KS * (1000000 * (p + 1) ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
    _ = (KS * 1000000 ^ 2) * (p + 1) ^ 4 := by ring

/-! ## The word -/

theorem buHornerPrePipe (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p → ∀ (Z : ℤ),
      Z.natAbs ≤ 2 ^ (11 * p + 210) →
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.auEn p),
                 HvdH.Val.int (((Work.Resample.auNstep p : ℕ)) : ℤ),
                 HvdH.Val.int (Work.Resample.auEn p), HvdH.Val.int Z,
                 HvdH.Val.int (p : ℤ)] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pushProg, Kpush, hPush⟩ := KL.pushVal
  obtain ⟨dupProg, Kdup, hDup⟩ := KL.dup
  obtain ⟨dropProg, Kdrop, hDrop⟩ := KL.drop
  obtain ⟨pickProg, Kpick, hPick⟩ := KL.pick
  obtain ⟨rollProg, Kroll, hRoll⟩ := KL.roll
  obtain ⟨addProg, Kadd, hAdd⟩ := IL.add
  obtain ⟨mulProg, Kmul, hMul⟩ := IL.mulS
  obtain ⟨pow2Prog, Kpow2, hPow2⟩ := IL.pow2
  set KS : ℕ := Kpush + Kdup + Kdrop + Kpick + Kroll + Kadd + Kmul + Kpow2 + 1 with hKS
  have hKpush : Kpush ≤ KS := by omega
  have hKdup : Kdup ≤ KS := by omega
  have hKdrop : Kdrop ≤ KS := by omega
  have hKpick : Kpick ≤ KS := by omega
  have hKroll : Kroll ≤ KS := by omega
  have hKadd : Kadd ≤ KS := by omega
  have hKmul : Kmul ≤ KS := by omega
  have hKpow2 : Kpow2 ≤ KS := by omega
  let prog : HvdH.Cmd := (.seq (pickProg 1) (.seq (dupProg) (.seq (pushProg (.int 3)) (.seq (mulProg) (.seq (pushProg (.int 100)) (.seq (addProg) (.seq (dupProg) (.seq (pushProg (.int 2)) (.seq (mulProg) (.seq (rollProg 1) (.seq (pow2Prog) (.seq (dupProg) (.seq (rollProg 2) (.seq (rollProg 1) (.seq (rollProg 3) (dropProg))))))))))))))))
  refine ⟨prog, 4 * (16 * (KS * 1000000 ^ 2)) + 5, ?_⟩
  intro main p hp Z hZ rest
  have hZsz : isz Z ≤ buSZ p := isz_Z_le_buSZ hZ
  have hpsz : isz (p : ℤ) ≤ buSZ p := isz_p_le_buSZ_HK p
  have h2sz : isz (2 : ℤ) ≤ buSZ p := isz_const_le_buSZ p 2 (by norm_num)
  have h3sz : isz (3 : ℤ) ≤ buSZ p := isz_const_le_buSZ p 3 (by norm_num)
  have h100sz : isz (100 : ℤ) ≤ buSZ p := isz_const_le_buSZ p 100 (by norm_num)
  have h3psz : isz (3 * (p : ℤ)) ≤ buSZ p := isz_three_mul_p_le_buSZ p
  have hW1sz : isz (100 + 3 * (p : ℤ)) ≤ buSZ p := isz_W1_le_buSZ p
  have hW2sz : isz (2 * (100 + 3 * (p : ℤ))) ≤ buSZ p := isz_W2_le_buSZ p
  have ht1 : (100 + 3 * (p : ℤ)).toNat ≤ buSZ p := by
    rw [show (100 + 3 * (p : ℤ)).toNat = 3 * p + 100 by omega]; simp only [buSZ]; omega
  have hW1nn : (0 : ℤ) ≤ 100 + 3 * (p : ℤ) := by positivity
  have hEn_eq : (2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat = auEn p := by
    rw [show (100 + 3 * (p : ℤ)).toNat = 3 * p + 100 by omega]; rfl
  have hNs_eq : 2 * (100 + 3 * (p : ℤ)) = ((auNstep p : ℕ) : ℤ) := by
    rw [show (2 : ℤ) * (100 + 3 * (p : ℤ)) = (((2 * (3 * p + 100)) : ℕ) : ℤ) by push_cast; ring]
    rfl
  have hEnsz : isz ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat) ≤ buSZ p := by
    rw [hEn_eq]; exact isz_auEn_le_buSZ p
  have hAsZ : vsz (HvdH.Val.int Z) ≤ buSZ p := vsz_int_le_buSZ hZsz
  have hAsp : vsz (HvdH.Val.int (p : ℤ)) ≤ buSZ p := vsz_int_le_buSZ hpsz
  have hAsW1 : vsz (HvdH.Val.int (100 + 3 * (p : ℤ))) ≤ buSZ p := vsz_int_le_buSZ hW1sz
  have hAsW2 : vsz (HvdH.Val.int (2 * (100 + 3 * (p : ℤ)))) ≤ buSZ p := vsz_int_le_buSZ hW2sz
  have hAsE : vsz (HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat)) ≤ buSZ p :=
    vsz_int_le_buSZ hEnsz
  have hA1 : ∀ v ∈ ([HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] : List HvdH.Val), vsz v ≤ buSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hAsZ
    · exact hAsp
  have s1 : Pipe main (pickProg 1) [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 1) (by simp))
      (le_buSB_roll hKpick (A := [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 1) (by omega) (by simp) hA1)
  have s2 : Pipe main dupProg [HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (p : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.dup main hDup (HvdH.Val.int (p : ℤ)))) (le_buSB_one hKdup hAsp)
  have s3 : Pipe main (pushProg (.int 3))
      [HvdH.Val.int (p : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int 3, HvdH.Val.int (p : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (buHSB p KS) :=
    Pipe.le (Pipe.pushOnAny (T := [HvdH.Val.int (p : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)]) (hPush main (.int 3))) (le_buSB_one hKpush (vsz_int_le_buSZ h3sz))
  have s4 : Pipe main mulProg
      [HvdH.Val.int 3, HvdH.Val.int (p : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.binOp (hMul main) (a := 3) (b := (p : ℤ)) trivial)) (le_buSB_mul hKmul h3sz hpsz)
  have s5 : Pipe main (pushProg (.int 100))
      [HvdH.Val.int (3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int 100, HvdH.Val.int (3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.pushOnAny (T := [HvdH.Val.int (3 * (p : ℤ)), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (hPush main (.int 100)))
      (le_buSB_one hKpush (vsz_int_le_buSZ h100sz))
  have s6 : Pipe main addProg
      [HvdH.Val.int 100, HvdH.Val.int (3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.binOp (hAdd main) (a := 100) (b := 3 * (p : ℤ)) trivial)) (le_buSB_two hKadd h100sz h3psz)
  have s7 : Pipe main dupProg
      [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.dup main hDup (HvdH.Val.int (100 + 3 * (p : ℤ))))) (le_buSB_one hKdup hAsW1)
  have s8 : Pipe main (pushProg (.int 2))
      [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int 2, HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (100 + 3 * (p : ℤ)),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.pushOnAny (T := [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (100 + 3 * (p : ℤ)),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (hPush main (.int 2)))
      (le_buSB_one hKpush (vsz_int_le_buSZ h2sz))
  have s9 : Pipe main mulProg
      [HvdH.Val.int 2, HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (100 + 3 * (p : ℤ)),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ),
      HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.binOp (hMul main) (a := 2) (b := 100 + 3 * (p : ℤ)) trivial))
      (le_buSB_mul hKmul h2sz hW1sz)
  have hA10 : ∀ v ∈ ([HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (100 + 3 * (p : ℤ)),
      HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] : List HvdH.Val), vsz v ≤ buSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hAsW2
    · exact hAsW1
    · exact hAsp
    · exact hAsZ
    · exact hAsp
  have s10 : Pipe main (rollProg 1)
      [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)]) (k := 1) (by simp))
      (le_buSB_roll hKroll (A := [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)]) (k := 1) (by omega) (by simp) hA10)
  have s11 : Pipe main pow2Prog
      [HvdH.Val.int (100 + 3 * (p : ℤ)), HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ),
      HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.unOp (hPow2 main) (a := 100 + 3 * (p : ℤ)) hW1nn)) (le_buSB_two hKpow2 ht1 hW1sz)
  have s12 : Pipe main dupProg
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ),
      HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.dup main hDup (HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat))))
      (le_buSB_one hKdup hAsE)
  have hA13 : ∀ v ∈ ([HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
      HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
      HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] : List HvdH.Val), vsz v ≤ buSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hAsE
    · exact hAsE
    · exact hAsW2
    · exact hAsp
    · exact hAsZ
    · exact hAsp
  have s13 : Pipe main (rollProg 2)
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))), HvdH.Val.int (p : ℤ), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 2) (by simp))
      (le_buSB_roll hKroll (A := [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 2) (by omega) (by simp) hA13)
  have hA14 : ∀ v ∈ ([HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
      HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
      HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
      HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] : List HvdH.Val), vsz v ≤ buSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hAsW2
    · exact hAsE
    · exact hAsE
    · exact hAsp
    · exact hAsZ
    · exact hAsp
  have s14 : Pipe main (rollProg 1)
      [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 1) (by simp))
      (le_buSB_roll hKroll (A := [HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 1) (by omega) (by simp) hA14)
  have hA15 : ∀ v ∈ ([HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
      HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
      HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
      HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] : List HvdH.Val), vsz v ≤ buSZ p := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hAsE
    · exact hAsW2
    · exact hAsE
    · exact hAsp
    · exact hAsZ
    · exact hAsp
  have s15 : Pipe main (rollProg 3)
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int (p : ℤ),
        HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int (p : ℤ), HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 3) (by simp))
      (le_buSB_roll hKroll (A := [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (p : ℤ), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]) (k := 3) (by omega) (by simp) hA15)
  have s16 : Pipe main dropProg
      [HvdH.Val.int (p : ℤ), HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)] (buHSB p KS) :=
    Pipe.le (Pipe.appendTail [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
      HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
      HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (Pipe.drop main hDrop (HvdH.Val.int (p : ℤ)))) (le_buSB_one hKdrop hAsp)
  have hchain : Pipe main prog [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
      (16 * buHSB p KS) := by
    have h := Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 (Pipe.comp s11 (Pipe.comp s12 (Pipe.comp s13 (Pipe.comp s14 (Pipe.comp s15 (s16)))))))))))))))
    exact Pipe.le h (by omega)
  have hfinal : HvdH.WordR main prog
      (fun vs => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest)
      (fun _ out => out = [HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat),
        HvdH.Val.int (2 * (100 + 3 * (p : ℤ))),
        HvdH.Val.int ((2 : ℤ) ^ (100 + 3 * (p : ℤ)).toNat), HvdH.Val.int Z,
        HvdH.Val.int (p : ℤ)] ++ rest) (fun _ => 16 * buHSB p KS) := hchain rest
  have hcost : 16 * buHSB p KS ≤
      (4 * (16 * (KS * 1000000 ^ 2)) + 5) * (p + 1) ^ (4 * (16 * (KS * 1000000 ^ 2)) + 5) := by
    have h2 : 16 * buHSB p KS ≤ (16 * (KS * 1000000 ^ 2)) * (p + 1) ^ 4 := by
      calc 16 * buHSB p KS ≤ 16 * ((KS * 1000000 ^ 2) * (p + 1) ^ 4) :=
            Nat.mul_le_mul_left 16 (buSB_le_pow_q p KS)
        _ = (16 * (KS * 1000000 ^ 2)) * (p + 1) ^ 4 := by ring
    have h3 : (16 * (KS * 1000000 ^ 2)) * (p + 1) ^ 4 ≤
        (4 * (16 * (KS * 1000000 ^ 2)) + 4 + 1) * (p + 1) ^ (4 * (16 * (KS * 1000000 ^ 2)) + 4) :=
      pow_mul_le (16 * (KS * 1000000 ^ 2)) 4 p (by omega) (by omega)
    have h4 : (4 * (16 * (KS * 1000000 ^ 2)) + 4 + 1) *
          (p + 1) ^ (4 * (16 * (KS * 1000000 ^ 2)) + 4) ≤
        (4 * (16 * (KS * 1000000 ^ 2)) + 5) * (p + 1) ^ (4 * (16 * (KS * 1000000 ^ 2)) + 5) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    exact le_trans h2 (le_trans h3 h4)
  exact KL.conseq main prog _ _ _ _ _ _ hfinal (fun vs h => h)
    (fun vs out hvs hout => ⟨hvs, by rw [hout, hEn_eq, hNs_eq]⟩) (fun vs hvs => hcost)

end Work.Resample
