import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paBasic

/-!
# Facts about the per-axis budget `Work.Resample.PABr`

`paPABrFacts` collects, in one place, the inequalities that show that the per-axis budget
`Work.Resample.PABr Kb Cm p α ss ts j` of the `Ã` program dominates every quantity that the
program of `Submission.Work.Resample.progTensorA` has to hold at axis `j`:

* the encoding size `ts.prod * (2p+8) + ts.prod + 2` of the array (`PAVec`);
* the sizes `isz` of the four dimension parameters
  `A = ∏_{k<j} ts_k`, `s_j = ss_j`, `t_j = ts_j`, `B = ∏_{k>j} s_k` (the arguments of
  `LayoutLib.applyAlong`), and of both suffixes `intList (ss.drop (j+1))`,
  `intList (ts.drop (j+1))` (the dimension data left on the stacks 2 and 3 between axes);
* the product estimate `B ≤ ts.prod`, i.e. `(∏_{k>j} s_k) ≤ ∏_k t_k`.

All bounds are read off the constituent terms of `PABr` (`1048576 * (ts.prod * (2p+8) + ts.prod + 2)`
for the array and the products, `1048576 * ((D+1) * (p+2))` for the per-dimension data), and the
elementary input is `HvdH.ResParams`: both lists have length `D = 1729`, and each `s_i < t_i < 2^p`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Elementary size facts -/

/-- `isz` of a natural number. -/
theorem pa_isz_nat (n : ℕ) : HvdH.isz (n : ℤ) = n.size + 2 := by simp [HvdH.isz]

/-- The size of a `cons` value. -/
theorem pa_vsz_cons (a b : HvdH.Val) :
    HvdH.vsz (HvdH.Val.cons a b) = HvdH.vsz a + HvdH.vsz b + 1 := by
  simp [HvdH.vsz, HvdH.Val.enc, Nat.add_assoc]

/-- The size of the empty list value. -/
theorem pa_vsz_nil : HvdH.vsz (HvdH.intList ([] : List ℕ)) = 1 := by decide

/-- `vsz (intList l) ≤ (l.length + 1) * (B + 3)` as soon as every entry of `l` has bit-size `≤ B`. -/
theorem pa_vsz_intList_le (l : List ℕ) (B : ℕ) (h : ∀ m ∈ l, m.size ≤ B) :
    HvdH.vsz (HvdH.intList l) ≤ (l.length + 1) * (B + 3) := by
  induction l with
  | nil => rw [pa_vsz_nil]; simp
  | cons a t ih =>
      have ih' := ih (fun m hm => h m (List.mem_cons_of_mem a hm))
      have hrec : HvdH.vsz (HvdH.intList (a :: t))
          = HvdH.vsz (HvdH.Val.int (a : ℤ)) + HvdH.vsz (HvdH.intList t) + 1 := by
        rw [Work.Resample.pa_intList_cons, pa_vsz_cons]
      rw [hrec, Work.Resample.paVszIntNat]
      have ha : a.size ≤ B := h a List.mem_cons_self
      have hkey : (t.length + 1 + 1) * (B + 3) = (t.length + 1) * (B + 3) + (B + 3) := by ring
      rw [List.length_cons, hkey]
      omega

/-- The list facts about `ts` and `ss` that the budget arithmetic uses: every entry of `ts` and of
`ss` has bit-size `≤ p` (because each `t_i < 2^p` and `s_i < t_i`), and `ts.prod ≥ 1`. -/
theorem pa_res_facts {p α : ℕ} {ss ts : List ℕ} (hRes : HvdH.ResParams p α ss ts) :
    (∀ x ∈ ts, x.size ≤ p) ∧ (∀ x ∈ ss, x.size ≤ p) ∧ 1 ≤ ts.prod := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hts : ∀ x ∈ ts, x.size ≤ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by omega
    have h := (hdim i hiD).2.2.1
    rw [List.getD_eq_getElem ts 0 hi] at h
    rwa [Nat.size_le]
  have hss : ∀ x ∈ ss, x.size ≤ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by omega
    have h := (hdim i hiD).2.2.1
    have h2 : ss.getD i 0 < 2 ^ p := lt_trans (hdim i hiD).2.1 h
    rw [List.getD_eq_getElem ss 0 hi] at h2
    rwa [Nat.size_le]
  have hT1 : 1 ≤ ts.prod := by
    refine List.one_le_prod (fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by omega
    have h := le_trans (hdim i hiD).1 (le_of_lt (hdim i hiD).2.1)
    rw [List.getD_eq_getElem ts 0 hi] at h
    omega
  exact ⟨hts, hss, hT1⟩

/-! ## Products of prefixes and suffixes -/

/-- A prefix product is at most the whole product, when the latter is positive. -/
theorem pa_take_prod_le (l : List ℕ) (h : 1 ≤ l.prod) (j : ℕ) : (l.take j).prod ≤ l.prod := by
  have hd : 1 ≤ (l.drop j).prod := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [← List.prod_take_mul_prod_drop l j, h0, mul_zero] at h
    omega
  calc (l.take j).prod = (l.take j).prod * 1 := (mul_one _).symm
    _ ≤ (l.take j).prod * (l.drop j).prod := Nat.mul_le_mul_left _ hd
    _ = l.prod := List.prod_take_mul_prod_drop l j

/-- A suffix product is at most the whole product, when the latter is positive. -/
theorem pa_drop_prod_le_prod (l : List ℕ) (h : 1 ≤ l.prod) (j : ℕ) : (l.drop j).prod ≤ l.prod := by
  have ht : 1 ≤ (l.take j).prod := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [← List.prod_take_mul_prod_drop l j, h0, zero_mul] at h
    omega
  calc (l.drop j).prod = 1 * (l.drop j).prod := (one_mul _).symm
    _ ≤ (l.take j).prod * (l.drop j).prod := Nat.mul_le_mul_right _ ht
    _ = l.prod := List.prod_take_mul_prod_drop l j

/-! ## The budget facts -/

theorem paPABrFacts {Kb : ℕ} {Cm : ℕ → ℕ} {p α : ℕ} {ss ts : List ℕ} {j : ℕ}
    (hRes : HvdH.ResParams p α ss ts) (hj : j < HvdH.D) :
    ts.prod * (2 * p + 8) + ts.prod + 2 ≤ Work.Resample.PABr Kb Cm p α ss ts j ∧
    HvdH.isz (((ss.getD j 0 : ℕ) : ℤ)) + 1 ≤ Work.Resample.PABr Kb Cm p α ss ts j ∧
    HvdH.isz (((ts.getD j 0 : ℕ) : ℤ)) + 1 ≤ Work.Resample.PABr Kb Cm p α ss ts j ∧
    HvdH.isz (((ts.take j).prod : ℕ) : ℤ) + 1 ≤ Work.Resample.PABr Kb Cm p α ss ts j ∧
    HvdH.isz (((ss.drop (j + 1)).prod : ℕ) : ℤ) + 1 ≤ Work.Resample.PABr Kb Cm p α ss ts j ∧
    HvdH.vsz (HvdH.intList (ss.drop (j + 1))) + 1 ≤ Work.Resample.PABr Kb Cm p α ss ts j ∧
    HvdH.vsz (HvdH.intList (ts.drop (j + 1))) + 1 ≤ Work.Resample.PABr Kb Cm p α ss ts j ∧
    (ss.drop (j + 1)).prod ≤ ts.prod := by
  have hpar : HvdH.ResParams p α ss ts := hRes
  obtain ⟨hsz_ts, hsz_ss, hT1⟩ := pa_res_facts hpar
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hjs : j < ss.length := by omega
  have hjt : j < ts.length := by omega
  have hsj_mem : ss.getD j 0 ∈ ss := by
    rw [List.getD_eq_getElem ss 0 hjs]; exact List.getElem_mem hjs
  have htj_mem : ts.getD j 0 ∈ ts := by
    rw [List.getD_eq_getElem ts 0 hjt]; exact List.getElem_mem hjt
  -- the two dominating terms of `PABr`
  have hbigT : 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2) ≤ PABr Kb Cm p α ss ts j := by
    rw [PABr]; omega
  have hbigD : 1048576 * ((HvdH.D + 1) * (p + 2)) ≤ PABr Kb Cm p α ss ts j := by
    rw [PABr]; omega
  have hleD : p + 3 ≤ 1048576 * ((HvdH.D + 1) * (p + 2)) := by
    calc p + 3 ≤ 2 * (p + 2) := by omega
      _ ≤ 2 * ((HvdH.D + 1) * (p + 2)) :=
          Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left (p + 2) (by omega))
      _ ≤ 1048576 * ((HvdH.D + 1) * (p + 2)) := Nat.mul_le_mul_right _ (by norm_num)
  have hleT : ts.prod + 3 ≤ 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2) := by nlinarith
  -- the product estimate for the suffix `B = ∏_{k>j} s_k`
  have hB : (ss.drop (j + 1)).prod ≤ ts.prod :=
    le_trans (pa_drop_prod_le hpar (j + 1)) (pa_drop_prod_le_prod ts hT1 (j + 1))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hB⟩
  · exact le_trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 1048576)) hbigT
  · refine le_trans ?_ (le_trans hleD hbigD)
    rw [pa_isz_nat (ss.getD j 0)]
    have := hsz_ss (ss.getD j 0) hsj_mem
    omega
  · refine le_trans ?_ (le_trans hleD hbigD)
    rw [pa_isz_nat (ts.getD j 0)]
    have := hsz_ts (ts.getD j 0) htj_mem
    omega
  · have hAt : (ts.take j).prod ≤ ts.prod := pa_take_prod_le ts hT1 j
    refine le_trans ?_ (le_trans hleT hbigT)
    rw [pa_isz_nat ((ts.take j).prod)]
    have hsz := paSizeLeSelf ((ts.take j).prod)
    omega
  · refine le_trans ?_ (le_trans hleT hbigT)
    rw [pa_isz_nat ((ss.drop (j + 1)).prod)]
    have hsz := paSizeLeSelf ((ss.drop (j + 1)).prod)
    omega
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

end Work.Resample
