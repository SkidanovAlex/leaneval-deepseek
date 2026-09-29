import Mathlib
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Resample.pbBracketLeTight

/-!
# `Work.Resample.pb2DLayout`: the one-dimensional layout bounds of a `B̃` round

Every round of the one-dimensional resample iteration of Theorem 4.1 works with the frame data
`(ss.take j).prod`, `(ts.drop (j+1)).prod` of the value it carries.  This file reads off from
`HvdH.ResParams p α ss ts` (i.e. `ss.length = ts.length = D` and, for every `i < D`,
`2 ≤ ssᵢ < tsᵢ < 2^p`) the seven bounds used by the layout/complexity arguments:

* `1 ≤ ts.prod`;
* `(ss.take j).prod * (ts.drop (j+1)).prod * (ssⱼ + tsⱼ + 1) ≤ 3 * ts.prod` (the "cost is at most
  a constant times `ts.prod`" inequality, with the constants `ssⱼ + 1 ≤ tsⱼ` and `ss.take` prefix
  products below `ts.prod` absorbed);
* the same quantity fits in `p * D + 2` bits (because it is at most `3 * ts.prod ≤ 3 * 2^(p*D)`);
* the prefix and suffix products are each at most `ts.prod`;
* the individual entries `ssⱼ`, `tsⱼ` fit in `p` bits.

The first two list facts are `Work.Resample.pbTight_take_prod_le` and
`Work.Resample.pbTight_prod_split` from `pbBracketLeTight`; everything else is elementary.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- For a list of naturals all of whose entries are at least `1`, the product of a prefix is at
most the total product. -/
theorem pb2D_take_prod_le {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) (i : ℕ) :
    (l.take i).prod ≤ l.prod := by
  have h1 : 1 ≤ (l.drop i).prod :=
    List.one_le_prod (fun x hx => h x (List.mem_of_mem_drop hx))
  calc (l.take i).prod = (l.take i).prod * 1 := (mul_one _).symm
    _ ≤ (l.take i).prod * (l.drop i).prod := Nat.mul_le_mul_left _ h1
    _ = l.prod := List.prod_take_mul_prod_drop l i

/-- For a list of naturals all of whose entries are at least `1`, the product of a suffix is at
most the total product. -/
theorem pb2D_drop_prod_le {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) (i : ℕ) :
    (l.drop i).prod ≤ l.prod := by
  have h1 : 1 ≤ (l.take i).prod :=
    List.one_le_prod (fun x hx => h x (List.mem_of_mem_take hx))
  calc (l.drop i).prod = 1 * (l.drop i).prod := (one_mul _).symm
    _ ≤ (l.take i).prod * (l.drop i).prod := Nat.mul_le_mul_right _ h1
    _ = l.prod := List.prod_take_mul_prod_drop l i

theorem pb2DLayout {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts) (j : ℕ)
    (hj : j < HvdH.D) :
    1 ≤ ts.prod ∧
    (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) ≤ 3 * ts.prod ∧
    ((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size
      ≤ p * HvdH.D + 2 ∧
    (ss.take j).prod ≤ ts.prod ∧
    (ts.drop (j + 1)).prod ≤ ts.prod ∧
    (ss.getD j 0).size ≤ p ∧
    (ts.getD j 0).size ≤ p := by
  obtain ⟨hsslen, htslen, -, -, -, hpt⟩ := h
  have hjl : j < ts.length := by rw [htslen]; exact hj
  -- every entry of `ts` is at least `1`
  have hts1 : ∀ x ∈ ts, 1 ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by rw [← htslen]; exact hi
    have h1 : 2 ≤ ss.getD i 0 := (hpt i hiD).1
    have h2 : ss.getD i 0 < ts.getD i 0 := (hpt i hiD).2.1
    rw [← List.getD_eq_getElem ts 0 hi]
    omega
  -- every entry of `ts` fits in `p` bits
  have htslt : ∀ x ∈ ts, x < 2 ^ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by rw [← htslen]; exact hi
    rw [← List.getD_eq_getElem ts 0 hi]
    exact (hpt i hiD).2.2.1
  have hprod1 : 1 ≤ ts.prod := List.one_le_prod hts1
  -- the `ss`-prefix product is below the `ts`-prefix product
  have hA : (ss.take j).prod ≤ (ts.take j).prod :=
    pbTight_take_prod_le (by rw [hsslen, htslen])
      (fun i hi => by
        have hiD : i < HvdH.D := by rw [hsslen] at hi; exact hi
        exact le_of_lt (hpt i hiD).2.1)
      (by rw [hsslen]; omega)
  -- splitting `ts.prod` at `j`
  have hsplit := pbTight_prod_split ts hjl
  have hsplt : ss.getD j 0 + ts.getD j 0 + 1 ≤ 2 * ts.getD j 0 := by
    have := (hpt j hj).2.1; omega
  -- the main layout inequality
  have hmain : (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)
      ≤ 3 * ts.prod := by
    calc (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)
        ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * (2 * ts.getD j 0) :=
          Nat.mul_le_mul (Nat.mul_le_mul hA le_rfl) hsplt
      _ = 2 * ((ts.take j).prod * ts.getD j 0 * (ts.drop (j + 1)).prod) := by ring
      _ = 2 * ts.prod := by rw [hsplit]
      _ ≤ 3 * ts.prod := by omega
  -- `ts.prod` is a product of `D` factors each `< 2^p`
  have hT2 : ts.prod ≤ 2 ^ (p * HvdH.D) := by
    have hlen := List.prod_le_pow_length ts (2 ^ p) (fun x hx => le_of_lt (htslt x hx))
    rw [htslen] at hlen
    calc ts.prod ≤ (2 ^ p) ^ HvdH.D := hlen
      _ = 2 ^ (p * HvdH.D) := by rw [← pow_mul]
  -- the size bound: at most `3 * ts.prod < 2^(p*D+2)`
  have hW : ((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size
      ≤ p * HvdH.D + 2 := by
    rw [Nat.size_le]
    calc (ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)
        ≤ 3 * ts.prod := hmain
      _ ≤ 3 * 2 ^ (p * HvdH.D) := Nat.mul_le_mul_left 3 hT2
      _ < 4 * 2 ^ (p * HvdH.D) := by
          have hpos : 0 < 2 ^ (p * HvdH.D) := pow_pos (by norm_num) _
          omega
      _ = 2 ^ (p * HvdH.D + 2) := by rw [pow_add]; ring
  have h4 : (ss.take j).prod ≤ ts.prod := le_trans hA (pb2D_take_prod_le hts1 j)
  have h5 : (ts.drop (j + 1)).prod ≤ ts.prod := pb2D_drop_prod_le hts1 (j + 1)
  have h6 : (ss.getD j 0).size ≤ p := by
    refine Nat.size_le.mpr ?_
    have h1 := (hpt j hj).2.1
    have h2 := (hpt j hj).2.2.1
    omega
  have h7 : (ts.getD j 0).size ≤ p := Nat.size_le.mpr (hpt j hj).2.2.1
  exact ⟨hprod1, hmain, hW, h4, h5, h6, h7⟩

end Work.Resample
