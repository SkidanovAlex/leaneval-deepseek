import Mathlib
import Submission.Work.Resample.pb2CostDefs
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Resample.paDRestLit
import Submission.Work.Resample.pbBracketLeTight

/-!
# `Work.Resample.pb2DGroupCm`: the `Cm` group of the `B̃` cost arithmetic

This is the exact mirror of `Work.Resample.paDGroupCm`
(`Submission/Work/Resample/paCostD.lean`) for the `B̃` half of Theorem 4.1.  The only difference is
the shape of the array product: the `Ã` half carries
`(ts.take j).prod * (ss.drop (j+1)).prod` (the array flows from shape `ts` to shape `ss`), while the
`B̃` half carries `(ss.take j).prod * (ts.drop (j+1)).prod` (it flows the other way, from `ss` to
`ts`).  So the sum lemma underlying the estimate is not `Work.Resample.paDSumCm` but its mirror
`Work.Resample.pb2DSumCm` below: here the *prefix* is `(ss.take j).prod ≤ (ts.take j).prod` and the
*suffix* is `(ts.drop (j+1)).prod`, so the split `(ts.take j).prod * t_j * (ts.drop (j+1)).prod =
ts.prod` can be used directly.
-/

namespace Work.Resample

open HvdH

set_option autoImplicit false

/-! ## The mirror of `paDSumCm` -/

/-- The `Cm`-carrying factors of the per-axis budgets of the `B̃` half, summed over the `D` axes:
`Σ_{j<D} (ss.take j).prod * (ts.drop (j+1)).prod * (t_j + 1) ≤ 2 * D * ts.prod`.
(`ssᵢ < tᵢ` gives `(ss.take j).prod ≤ (ts.take j).prod` and
`(ts.take j).prod * t_j * (ts.drop (j+1)).prod = ts.prod`.) -/
theorem pb2DSumCm {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts) :
    (∑ j ∈ Finset.range HvdH.D,
        (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1))
      ≤ 2 * HvdH.D * ts.prod := by
  obtain ⟨hsslen, htslen, -, -, -, hpt⟩ := h
  have hterm : ∀ j ∈ Finset.range HvdH.D,
      (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1) ≤ 2 * ts.prod := by
    intro j hj
    have hjD : j < HvdH.D := Finset.mem_range.mp hj
    have hjl : j < ts.length := by rw [htslen]; exact hjD
    have ht0 : 1 ≤ ts.getD j 0 := by have := (hpt j hjD).2.1; omega
    have hA : (ss.take j).prod ≤ (ts.take j).prod :=
      pbTight_take_prod_le (by rw [hsslen, htslen])
        (fun i hi => le_of_lt (hpt i (by rw [hsslen] at hi; exact hi)).2.1)
        (by rw [hsslen]; omega)
    have hT : (ts.take j).prod * ts.getD j 0 * (ts.drop (j + 1)).prod = ts.prod :=
      pbTight_prod_split ts hjl
    have e1 : (ss.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 ≤ ts.prod := by
      calc (ss.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0
          ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA)
        _ = ts.prod := by rw [← hT]; ring
    have e2 : (ss.take j).prod * (ts.drop (j + 1)).prod ≤ ts.prod := by
      calc (ss.take j).prod * (ts.drop (j + 1)).prod
          ≤ (ts.take j).prod * (ts.drop (j + 1)).prod := Nat.mul_le_mul_right _ hA
        _ ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 := by
            calc (ts.take j).prod * (ts.drop (j + 1)).prod
                = (ts.take j).prod * (ts.drop (j + 1)).prod * 1 := (Nat.mul_one _).symm
              _ ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 :=
                  Nat.mul_le_mul_left _ ht0
        _ = ts.prod := by rw [← hT]; ring
    calc (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1)
        = (ss.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0
          + (ss.take j).prod * (ts.drop (j + 1)).prod := by ring
      _ ≤ ts.prod + ts.prod := Nat.add_le_add e1 e2
      _ = 2 * ts.prod := by ring
  calc (∑ j ∈ Finset.range HvdH.D,
        (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1))
      ≤ ∑ _j ∈ Finset.range HvdH.D, 2 * ts.prod := Finset.sum_le_sum hterm
    _ = HvdH.D * (2 * ts.prod) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ = 2 * HvdH.D * ts.prod := by ring

/-! ## The group estimate -/

theorem pb2DGroupCm {Kb Kc2 p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts)
    (Cm : ℕ → ℕ) (hmon : Monotone Cm) {K : ℕ} (hKbK : Kb ≤ K)
    (hKcm : 1024 * Kc2 * HvdH.D * Kb ≤ K) :
    Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, Work.Resample.pb2DCm Kb Cm p α ss ts j))
      ≤ K * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K * p) + p) := by
  -- the sum of the `Cm`-carrying terms, in factored form
  have hS : (∑ j ∈ Finset.range HvdH.D, pb2DCm Kb Cm p α ss ts j)
      ≤ Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) * (2 * HvdH.D * ts.prod) := by
    have h1 : (∑ j ∈ Finset.range HvdH.D, pb2DCm Kb Cm p α ss ts j)
        = (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
          * (∑ j ∈ Finset.range HvdH.D,
              (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by unfold pb2DCm; ring)
    rw [h1]
    calc (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
          * (∑ j ∈ Finset.range HvdH.D,
              (ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + 1))
        ≤ (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
          * (2 * HvdH.D * ts.prod) := Nat.mul_le_mul_left _ (pb2DSumCm h)
      _ = Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
          * (2 * HvdH.D * ts.prod) := by ring
  -- the coefficient comparison
  have hmonK : Cm (Kb * p) ≤ Cm (K * p) := hmon (Nat.mul_le_mul_right p hKbK)
  have hα2 : 2 ≤ α := h.2.2.2.1
  have hp1 : 1 ≤ p := by have := h.2.2.1; omega
  have hα2' : α + 1 ≤ 2 * α := by omega
  have hpp' : Cm (Kb * p) + p + 1 ≤ 2 * (Cm (K * p) + p) := by omega
  have h512 : 512 * Kc2 * HvdH.D * Kb ≤ K := by
    have h1 : 512 * Kc2 * HvdH.D * Kb = 512 * (Kc2 * HvdH.D * Kb) := by ring
    have h2 : 1024 * Kc2 * HvdH.D * Kb = 1024 * (Kc2 * HvdH.D * Kb) := by ring
    have h3 : 512 * (Kc2 * HvdH.D * Kb) ≤ 1024 * (Kc2 * HvdH.D * Kb) :=
      Nat.mul_le_mul_right _ (by norm_num : (512 : ℕ) ≤ 1024)
    have h4 : 1024 * (Kc2 * HvdH.D * Kb) ≤ K := by rw [← h2]; exact hKcm
    rw [h1]
    omega
  have hcoef : 128 * Kc2 * HvdH.D * Kb * ((α + 1) * (Cm (Kb * p) + p + 1))
      ≤ K * (α * (Cm (K * p) + p)) := by
    have hstep : 128 * Kc2 * HvdH.D * Kb * ((α + 1) * (Cm (Kb * p) + p + 1))
        ≤ 128 * Kc2 * HvdH.D * Kb * ((2 * α) * (2 * (Cm (K * p) + p))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hα2' hpp')
    have heq : 128 * Kc2 * HvdH.D * Kb * ((2 * α) * (2 * (Cm (K * p) + p)))
        = (512 * Kc2 * HvdH.D * Kb) * (α * (Cm (K * p) + p)) := by ring
    rw [heq] at hstep
    exact le_trans hstep (Nat.mul_le_mul_right _ h512)
  -- assembly
  calc Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, pb2DCm Kb Cm p α ss ts j))
      ≤ Kc2 * (64 * (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
          * (2 * HvdH.D * ts.prod))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS)
    _ = (ts.prod * (Nat.sqrt p + 1))
          * (128 * Kc2 * HvdH.D * Kb * ((α + 1) * (Cm (Kb * p) + p + 1))) := by ring
    _ ≤ (ts.prod * (Nat.sqrt p + 1)) * (K * (α * (Cm (K * p) + p))) :=
        Nat.mul_le_mul_left _ hcoef
    _ = K * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K * p) + p) := by ring

end Work.Resample
