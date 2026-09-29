import Mathlib
import Submission.Work.Resample.pb2eDefs
import Submission.Work.Resample.pb2eBrFacts
import Submission.Work.Resample.paPABrFacts
import Submission.Work.Resample.paProdWordCost
import Submission.Work.Resample.pb2ProdWordCost
import Submission.Work.Resample.pbRndDefs
import Submission.Work.Resample.pbRAdim

namespace Work.Resample

set_option autoImplicit false
set_option maxHeartbeats 4000000

open HvdH

/-! ## Mirror of `Work.Resample.paEStageCostBd` for the `B̃` half

This is the pure arithmetic/cost estimate for the preamble of one `B̃` axis step (paper Theorem 4.1,
`B̃` half).  It is the exact mirror of the *proved* `Work.Resample.paEStageCostBd` in
`Submission/Work/Resample/paStageE.lean` (lines 68-200 of that file); start by copying that proof.
The 18 phase costs of `pb2ECost` are the costs of the same 18 library words as in the `Ã` half, but
the data flow is swapped: stack 2 keeps the remaining *input* dims `ts.drop j`, stack 3 the
remaining *output* dims `ss.drop j`, stack 6 the outer product `A = (ss.take j).prod`, stack 7 the
stashed output dimension `s_j`, stack 11 the stashed input dimension `t_j` (phases 9 and 10 of the
`Ã` version are interchanged, so the coefficient order is Kc4b then Kc4a).
-/
theorem pb2ECostBd (K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11
    Kc4f Kb : ℕ) :
    ∀ (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (arr : HvdH.Val),
      HvdH.ResParams p α ss ts → j < HvdH.D →
      HvdH.vsz arr ≤ ts.prod * (2 * p + 8) + ts.prod + 1 →
      Work.Resample.pb2ECost K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e
          Kb11 Kc4f Kb Cm p α ss ts j arr ≤
        Work.Resample.pb2EKc K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e
            Kb11 Kc4f Kb * Work.Resample.PB2Br Kb Cm p α ss ts j := by
  intro Cm p α ss ts j arr hRes hjD harr
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hResC : ResParams p α ss ts := ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
  obtain ⟨b_arr, b_s, b_t, b_At, b_A, b_B, b_tsl, b_ssl, hBdrop, hAtake, hA1, hB1, hBX, hX⟩ :=
    pb2EBrFacts (Kb := Kb) (Cm := Cm) (p := p) (α := α) (ss := ss) (ts := ts) (j := j) hResC hjD
  have b_Dp : (D + 1) * (p + 2) ≤ PB2Br Kb Cm p α ss ts j := by unfold PB2Br; omega
  have b_isz1 : 4 ≤ PB2Br Kb Cm p α ss ts j := by unfold PB2Br; omega
  have vst : vsz (Val.int (ts.getD j 0 : ℤ)) = isz ((ts.getD j 0 : ℕ) : ℤ) :=
    Work.ConvR.vsz_int _
  have vss : vsz (Val.int (ss.getD j 0 : ℤ)) = isz ((ss.getD j 0 : ℕ) : ℤ) :=
    Work.ConvR.vsz_int _
  have vct : vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) =
      vsz (Val.int (ts.getD j 0 : ℤ)) + vsz (intList (ts.drop (j + 1))) + 1 :=
    Work.ConvR.vsz_cons _ _
  have vcs : vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) =
      vsz (Val.int (ss.getD j 0 : ℤ)) + vsz (intList (ss.drop (j + 1))) + 1 :=
    Work.ConvR.vsz_cons _ _
  -- ## phase 1: park the array
  have hc1 : K1 * (vsz arr + 1) ≤ K1 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left K1 ?_
    omega
  -- ## phase 2: peel `s_j` off stack 3
  have hc2 : K5a * (vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) +
      vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤ 3 * K5a * PB2Br Kb Cm p α ss ts j := by
    have h3 : vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) +
        vsz (Val.int (ss.getD j 0 : ℤ)) + 1 ≤ 3 * PB2Br Kb Cm p α ss ts j := by
      rw [vcs, vss]
      omega
    calc K5a * (vsz (Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1)))) +
          vsz (Val.int (ss.getD j 0 : ℤ)) + 1)
        ≤ K5a * (3 * PB2Br Kb Cm p α ss ts j) := Nat.mul_le_mul_left K5a h3
      _ = 3 * K5a * PB2Br Kb Cm p α ss ts j := by ring
  -- ## phase 3: stash `s_j` on stack 7
  have hc3 : K7 * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤ K7 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left K7 ?_
    rw [vss]
    omega
  -- ## phase 4: peel `t_j` off stack 2
  have hc4 : K5b * (vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) +
      vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ 3 * K5b * PB2Br Kb Cm p α ss ts j := by
    have h3 : vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) +
        vsz (Val.int (ts.getD j 0 : ℤ)) + 1 ≤ 3 * PB2Br Kb Cm p α ss ts j := by
      rw [vct, vst]
      omega
    calc K5b * (vsz (Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1)))) +
          vsz (Val.int (ts.getD j 0 : ℤ)) + 1)
        ≤ K5b * (3 * PB2Br Kb Cm p α ss ts j) := Nat.mul_le_mul_left K5b h3
      _ = 3 * K5b * PB2Br Kb Cm p α ss ts j := by ring
  -- ## phase 5: stash `t_j` on stack 11
  have hc5 : K11 * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ K11 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left K11 ?_
    rw [vst]
    omega
  -- ## phase 6: push `int 1`
  have hc6 : Kpv * (vsz (Val.int 1) + 1) ≤ Kpv * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kpv ?_
    have h1 : isz (1 : ℤ) ≤ 3 := by
      have h2 : (1 : ℤ).natAbs = 1 := by simp
      have h3 : Nat.size ((1 : ℤ).natAbs) ≤ 1 := by rw [h2]; exact paSizeLeSelf 1
      simp only [isz]; omega
    rw [Work.ConvR.vsz_int]
    omega
  -- ## phase 7: multiply `ts.drop (j+1)` into the accumulator
  have hlen_ts : (ts.drop (j + 1)).length ≤ D := by rw [List.length_drop, htslen]; omega
  have hlt_ts : ∀ t ∈ ts.drop (j + 1), t < 2 ^ p := by
    intro t ht
    obtain ⟨i, hi, hit⟩ := List.mem_iff_getElem.mp ht
    rw [← hit, ← List.getD_eq_getElem (ts.drop (j + 1)) 0 hi]
    rw [pa_getD_drop ts (j + 1) i (by simpa using hi)]
    have hi2 : i < (ts.drop (j + 1)).length := hi
    rw [List.length_drop, htslen] at hi2
    exact (hdim (i + (j + 1)) (by omega)).2.2.1
  have hc7 : K6 * ((ts.drop (j + 1)).length + 1) *
      ((((ts.drop (j + 1)).map (fun x : ℕ => isz (x : ℤ))).sum) +
        ((ts.drop (j + 1)).prod).size + 2) * (((ts.drop (j + 1)).prod).size + 2)
      ≤ 7 * K6 * (D + 1) * PB2Br Kb Cm p α ss ts j :=
    pb2ProdWordCost (Kb := Kb) (Kw := K6) (p := p) (α := α) (j := j) hResC hjD
      (ts.drop (j + 1)) ((ts.drop (j + 1)).prod) hlen_ts hlt_ts hBX
  -- ## phase 8: stash `B_j` on stack 10
  have hc8 : Kn10 * (vsz (Val.int ((ts.drop (j + 1)).prod)) + 1) ≤
      Kn10 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kn10 ?_
    rw [Work.ConvR.vsz_int]
    omega
  -- ## phase 9: copy `t_j` onto the value stack
  have hc9 : Kc4b * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤ Kc4b * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4b ?_
    rw [vst]
    omega
  -- ## phase 10: copy `s_j` onto the value stack
  have hc10 : Kc4a * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤
      Kc4a * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4a ?_
    rw [vss]
    omega
  -- ## phase 11: copy `α` onto the value stack
  have hα4 : α + 2 ≤ p := by
    have h5 : α + 2 ≤ α * α := by
      calc α + 2 ≤ 2 * α := by omega
        _ = α * 2 := by ring
        _ ≤ α * α := Nat.mul_le_mul_left α hα2
    have h6 : α * α < p := by simpa [pow_two] using hαp
    omega
  have hα3 : α + 3 ≤ (D + 1) * (p + 2) := by
    calc α + 3 ≤ 2 * (p + 2) := by omega
      _ ≤ (D + 1) * (p + 2) := Nat.mul_le_mul_right _ (by omega)
  have hc11 : Kc4c * (vsz (Val.int α) + 1) ≤ Kc4c * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4c ?_
    rw [Work.ConvR.vsz_int, pa_isz_nat α]
    have h2 : α.size ≤ α := paSizeLeSelf α
    omega
  -- ## phase 12: copy `p` onto the value stack
  have hp3 : p + 3 ≤ (D + 1) * (p + 2) := by
    calc p + 3 ≤ 2 * (p + 2) := by omega
      _ ≤ (D + 1) * (p + 2) := Nat.mul_le_mul_right _ (by omega)
  have hc12 : Kc4d * (vsz (Val.int p) + 1) ≤ Kc4d * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4d ?_
    rw [Work.ConvR.vsz_int, pa_isz_nat p]
    have h2 : p.size ≤ p := paSizeLeSelf p
    omega
  -- ## phase 13: `prep`
  have hc13 : 1 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) ≤
      1 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left 1 ?_
    unfold PB2Br
    omega
  -- ## phase 14: unpark the array
  have hc14 : Ku1 * (vsz arr + 1) ≤ Ku1 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Ku1 ?_
    omega
  -- ## phase 15: move `B_j` from stack 10 to the value stack
  have hc15 : Kb10 * (vsz (Val.int ((ts.drop (j + 1)).prod)) + 1) ≤
      Kb10 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kb10 ?_
    rw [Work.ConvR.vsz_int]
    omega
  -- ## phase 16: copy `s_j` onto the value stack
  have hc16 : Kc4e * (vsz (Val.int (ss.getD j 0 : ℤ)) + 1) ≤
      Kc4e * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4e ?_
    rw [vss]
    omega
  -- ## phase 17: move `t_j` from stack 11 to the value stack
  have hc17 : Kb11 * (vsz (Val.int (ts.getD j 0 : ℤ)) + 1) ≤
      Kb11 * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kb11 ?_
    rw [vst]
    omega
  -- ## phase 18: copy `A_j = (ss.take j).prod` onto the value stack
  have hc18 : Kc4f * (vsz (Val.int ((ss.take j).prod)) + 1) ≤
      Kc4f * PB2Br Kb Cm p α ss ts j := by
    refine Nat.mul_le_mul_left Kc4f ?_
    rw [Work.ConvR.vsz_int]
    omega
  -- ## assembly
  unfold pb2ECost pb2EKc
  nlinarith [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18]

end Work.Resample
