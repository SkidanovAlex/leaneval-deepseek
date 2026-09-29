import Mathlib
import Submission.Work.Resample.pb2CostDefs
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Resample.pbBracketLeTight

namespace Work.Resample

/-- **The `p²` term of the `B̃` budget.**  The extra `Kb (t_j+1) (p+1)²` term carried by the
`B`-slice word at axis `j`, multiplied by `64`, fits into the `ts.prod * p²` group of
`HvdH.resCost`.  The two ingredients are the split bound
`(ss.take j).prod * (ts.drop (j+1)).prod * (t_j + 1) ≤ 4 * ts.prod` (from `ResParams`, exactly as
in `pbBracketLeTight`) and `(p+1)² ≤ 4 p²` (from `p ≥ 100`): `64 · 4 · 4 = 1024`. -/
theorem pb2DXLe {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts)
    (Kb j : ℕ) (hj : j < HvdH.D) :
    64 * Work.Resample.pb2DX Kb p ss ts j ≤ 1024 * Kb * (ts.prod * p ^ 2) := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hpt⟩ := h
  have hjlt : j < ts.length := by rw [htslen]; exact hj
  have hst : ss.getD j 0 < ts.getD j 0 := (hpt j hj).2.1
  have h2s : 2 ≤ ss.getD j 0 := (hpt j hj).1
  -- the `ss`-prefix product is dominated by the `ts`-prefix product
  have hA : (ss.take j).prod ≤ (ts.take j).prod := by
    refine pbTight_take_prod_le (by rw [hsslen, htslen]) (fun i hi => ?_) (by rw [hsslen]; omega)
    have hi' : i < HvdH.D := by rw [hsslen] at hi; exact hi
    exact le_of_lt (hpt i hi').2.1
  -- the split identity for `ts.prod`
  have hT : (ts.take j).prod * ts.getD j 0 * (ts.drop (j + 1)).prod = ts.prod :=
    pbTight_prod_split ts hjlt
  -- the per-axis split bound
  have hAB : (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1) ≤ 4 * ts.prod := by
    have hstep : (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1)
        ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * (2 * ts.getD j 0) :=
      Nat.mul_le_mul (Nat.mul_le_mul hA (le_refl _)) (by omega)
    calc (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1)
        ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * (2 * ts.getD j 0) := hstep
      _ = 2 * ((ts.take j).prod * ts.getD j 0 * (ts.drop (j + 1)).prod) := by ring
      _ = 2 * ts.prod := by rw [hT]
      _ ≤ 4 * ts.prod := by omega
  -- `(p+1)² ≤ 4 p²`
  have hp1 : 1 ≤ p := by omega
  have hpp : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by
    have : p + 1 ≤ 2 * p := by omega
    calc (p + 1) ^ 2 ≤ (2 * p) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * p ^ 2 := by ring
  -- unfold `pb2DX` into the shape the two bounds multiply
  have h1 : 64 * Work.Resample.pb2DX Kb p ss ts j
      = 64 * Kb * ((ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1))
          * (p + 1) ^ 2 := by
    unfold Work.Resample.pb2DX
    ring
  rw [h1]
  calc 64 * Kb * ((ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1)) * (p + 1) ^ 2
      ≤ 64 * Kb * (4 * ts.prod) * (4 * p ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left (64 * Kb) hAB) hpp
    _ = 1024 * Kb * (ts.prod * p ^ 2) := by ring

end Work.Resample
