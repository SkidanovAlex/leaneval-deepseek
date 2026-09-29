import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs
import Submission.Work.Resample.pb2eDefs
import Submission.Work.Resample.pbRndDefs
import Submission.Work.Resample.paPABrFacts
import Submission.Work.Resample.pbRAdim
import Submission.Work.Resample.paProdWordCost

/-!
# Facts about the per-axis budget `Work.Resample.PB2Br` (the `B̃` half)

Mirror of `Submission/Work/Resample/paPABrFacts.lean` for the `B̃` budget `PB2Br`: the budget
dominates the encoding size of the array, the `isz` of the four dimension parameters
`A = ∏_{k<j} s_k`, `s_j`, `t_j`, `B = ∏_{k>j} t_k` and the `vsz` of both suffixes
`intList (ts.drop (j+1))`, `intList (ss.drop (j+1))`, together with the product estimates used by
the fold (`B ≤ (ss.take j).prod * B * (s_j + t_j + 1)`) and the elementary positivity facts.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Every entry of `ss` is `≥ 1` in a `ResParams` setting (in fact `≥ 2`). -/
theorem pb2OneLeSs {p α : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) :
    ∀ x ∈ ss, 1 ≤ x := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hiD : i < HvdH.D := by rw [← hRes.1]; exact hi
  have h := (hRes.2.2.2.2.2 i hiD).1
  rw [← hix, ← List.getD_eq_getElem ss 0 hi]
  omega

/-- The third summand of `PB2Br` is a lower bound for the whole budget. -/
theorem pb2PB2BrThird (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) :
    64 * (((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1))
    ≤ Work.Resample.PB2Br Kb Cm p α ss ts j := by
  unfold Work.Resample.PB2Br
  have h : ∀ a b c d e f g h i : ℕ, c ≤ a + b + c + d + e + f + g + h + i := by
    intro a b c d e f g h i; omega
  exact h _ _ _ _ _ _ _ _ _

/-- In a `ResParams` setting, `X = (ss.take j).prod * (ts.drop (j+1)).prod *
(ss.getD j 0 + ts.getD j 0 + 1)` is at least `6`. -/
theorem pb2Xge6 {p α j : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) (hj : j < HvdH.D) :
    6 ≤ (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by
  have hA : 1 ≤ (ss.take j).prod :=
    paOneLeProd (fun x hx => pb2OneLeSs hRes x ((List.take_sublist j ss).subset hx))
  have hB : 1 ≤ (ts.drop (j + 1)).prod :=
    paOneLeProd (fun x hx => pbRnd_one_le_ts p α ss ts hRes x
      ((List.drop_sublist (j + 1) ts).subset hx))
  have hC : 6 ≤ ss.getD j 0 + ts.getD j 0 + 1 := by
    have h1 := (hRes.2.2.2.2.2 j hj).1
    have h2 := (hRes.2.2.2.2.2 j hj).2.1
    omega
  calc (6 : ℕ) = 1 * 1 * 6 := by norm_num
    _ ≤ (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC

/-- **The budget facts of the `B̃` half.** -/
theorem pb2EBrFacts {Kb : ℕ} {Cm : ℕ → ℕ} {p α : ℕ} {ss ts : List ℕ} {j : ℕ}
    (hRes : HvdH.ResParams p α ss ts) (hj : j < HvdH.D) :
    ts.prod * (2 * p + 8) + ts.prod + 2 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    HvdH.isz (((ss.getD j 0 : ℕ) : ℤ)) + 1 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    HvdH.isz (((ts.getD j 0 : ℕ) : ℤ)) + 1 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    HvdH.isz (((ts.take j).prod : ℕ) : ℤ) + 1 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    HvdH.isz (((ss.take j).prod : ℕ) : ℤ) + 1 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    HvdH.isz (((ts.drop (j + 1)).prod : ℕ) : ℤ) + 1 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    HvdH.vsz (HvdH.intList (ts.drop (j + 1))) + 1 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    HvdH.vsz (HvdH.intList (ss.drop (j + 1))) + 1 ≤ Work.Resample.PB2Br Kb Cm p α ss ts j ∧
    (ts.drop (j + 1)).prod ≤ ts.prod ∧
    (ss.take j).prod ≤ ts.prod ∧
    1 ≤ (ss.take j).prod ∧
    1 ≤ (ts.drop (j + 1)).prod ∧
    (ts.drop (j + 1)).prod ≤ (ss.take j).prod * (ts.drop (j + 1)).prod *
      (ss.getD j 0 + ts.getD j 0 + 1) ∧
    6 ≤ (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by
  have hpar : HvdH.ResParams p α ss ts := hRes
  obtain ⟨hsz_ts, hsz_ss, hT1⟩ := pa_res_facts hpar
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hjs : j < ss.length := by omega
  have hjt : j < ts.length := by omega
  have hsj_mem : ss.getD j 0 ∈ ss := by
    rw [List.getD_eq_getElem ss 0 hjs]; exact List.getElem_mem hjs
  have htj_mem : ts.getD j 0 ∈ ts := by
    rw [List.getD_eq_getElem ts 0 hjt]; exact List.getElem_mem hjt
  -- the two dominating terms of `PB2Br`
  have hbigT : 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2) ≤ PB2Br Kb Cm p α ss ts j := by
    rw [PB2Br]; omega
  have hbigD : 1048576 * ((HvdH.D + 1) * (p + 2)) ≤ PB2Br Kb Cm p α ss ts j := by
    rw [PB2Br]; omega
  have hleD : p + 3 ≤ 1048576 * ((HvdH.D + 1) * (p + 2)) := by
    calc p + 3 ≤ 2 * (p + 2) := by omega
      _ ≤ 2 * ((HvdH.D + 1) * (p + 2)) :=
          Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left (p + 2) (by omega))
      _ ≤ 1048576 * ((HvdH.D + 1) * (p + 2)) := Nat.mul_le_mul_right _ (by norm_num)
  have hleT : ts.prod + 3 ≤ 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2) := by nlinarith
  -- the input suffix `B = ∏_{k>j} t_k` and the output prefix `A = ∏_{k<j} s_k`
  have hBdrop : (ts.drop (j + 1)).prod ≤ ts.prod :=
    pbRnd_prod_drop_le ts (pbRnd_one_le_ts p α ss ts hpar)
  have hAtake : (ss.take j).prod ≤ ts.prod := by
    refine le_trans (pbRnd_take_prod_le p α ss ts hpar (by omega)) ?_
    exact pbRnd_prod_take_le (j := j) ts (pbRnd_one_le_ts p α ss ts hpar)
  have hA1 : 1 ≤ (ss.take j).prod :=
    paOneLeProd (fun x hx => pb2OneLeSs hpar x ((List.take_sublist j ss).subset hx))
  have hB1 : 1 ≤ (ts.drop (j + 1)).prod :=
    paOneLeProd (fun x hx => pbRnd_one_le_ts p α ss ts hpar x
      ((List.drop_sublist (j + 1) ts).subset hx))
  have hX : 6 ≤ (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) :=
    pb2Xge6 hpar hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hBdrop, hAtake, hA1, hB1, ?_, hX⟩
  · exact le_trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 1048576)) hbigT
  · refine le_trans ?_ (le_trans hleD hbigD)
    rw [pa_isz_nat (ss.getD j 0)]
    have := hsz_ss (ss.getD j 0) hsj_mem
    omega
  · refine le_trans ?_ (le_trans hleD hbigD)
    rw [pa_isz_nat (ts.getD j 0)]
    have := hsz_ts (ts.getD j 0) htj_mem
    omega
  · refine le_trans ?_ (le_trans hleT hbigT)
    rw [pa_isz_nat ((ts.take j).prod)]
    have hsz := paSizeLeSelf ((ts.take j).prod)
    have htj_le : (ts.take j).prod ≤ ts.prod :=
      pbRnd_prod_take_le (j := j) ts (pbRnd_one_le_ts p α ss ts hpar)
    omega
  · refine le_trans ?_ (le_trans hleT hbigT)
    rw [pa_isz_nat ((ss.take j).prod)]
    have hsz := paSizeLeSelf ((ss.take j).prod)
    omega
  · refine le_trans ?_ (le_trans hleT hbigT)
    rw [pa_isz_nat ((ts.drop (j + 1)).prod)]
    have hsz := paSizeLeSelf ((ts.drop (j + 1)).prod)
    omega
  · have hv : HvdH.vsz (HvdH.intList (ts.drop (j + 1))) ≤ (HvdH.D + 1) * (p + 3) := by
      have hmem : ∀ m ∈ ts.drop (j + 1), m.size ≤ p :=
        fun m hm => hsz_ts m ((List.drop_sublist (j + 1) ts).subset hm)
      have h0 := pa_vsz_intList_le (ts.drop (j + 1)) p hmem
      have hlen : (ts.drop (j + 1)).length + 1 ≤ HvdH.D + 1 := by
        rw [List.length_drop, htslen]; omega
      exact le_trans h0 (Nat.mul_le_mul_right (p + 3) hlen)
    refine le_trans ?_ hbigD
    calc HvdH.vsz (HvdH.intList (ts.drop (j + 1))) + 1
        ≤ (HvdH.D + 1) * (p + 3) + 1 := Nat.add_le_add_right hv 1
      _ ≤ 2 * ((HvdH.D + 1) * (p + 2)) := by nlinarith
      _ ≤ 1048576 * ((HvdH.D + 1) * (p + 2)) := Nat.mul_le_mul_right _ (by norm_num)
  · have hv : HvdH.vsz (HvdH.intList (ss.drop (j + 1))) ≤ (HvdH.D + 1) * (p + 3) := by
      have hmem : ∀ m ∈ ss.drop (j + 1), m.size ≤ p :=
        fun m hm => hsz_ss m ((List.drop_sublist (j + 1) ss).subset hm)
      have h0 := pa_vsz_intList_le (ss.drop (j + 1)) p hmem
      have hlen : (ss.drop (j + 1)).length + 1 ≤ HvdH.D + 1 := by
        rw [List.length_drop, hsslen]; omega
      exact le_trans h0 (Nat.mul_le_mul_right (p + 3) hlen)
    refine le_trans ?_ hbigD
    calc HvdH.vsz (HvdH.intList (ss.drop (j + 1))) + 1
        ≤ (HvdH.D + 1) * (p + 3) + 1 := Nat.add_le_add_right hv 1
      _ ≤ 2 * ((HvdH.D + 1) * (p + 2)) := by nlinarith
      _ ≤ 1048576 * ((HvdH.D + 1) * (p + 2)) := Nat.mul_le_mul_right _ (by norm_num)
  · have h1 : 1 ≤ (ss.take j).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by
      have h2 : 1 ≤ ss.getD j 0 + ts.getD j 0 + 1 := by omega
      calc 1 = 1 * 1 := (mul_one 1).symm
        _ ≤ (ss.take j).prod * (ss.getD j 0 + ts.getD j 0 + 1) := Nat.mul_le_mul hA1 h2
    calc (ts.drop (j + 1)).prod = 1 * (ts.drop (j + 1)).prod := (one_mul _).symm
      _ ≤ ((ss.take j).prod * (ss.getD j 0 + ts.getD j 0 + 1)) * (ts.drop (j + 1)).prod :=
          Nat.mul_le_mul_right _ h1
      _ = (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) := by ring

end Work.Resample
