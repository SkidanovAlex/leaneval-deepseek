/-
# `Submission.Work.FIArea7CF.regionLowSplitWeightSum` — clash-free copy of `Submission.Work.FIArea7.regionLowSplitWeightSum`

Imports redirected to the `FIArea7CF` copies; renamed: norm_uniCoeff_le→crs_norm_uniCoeff_le.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.charRegionSplitAux
import Submission.Work.FIArea7CF.regionLowSplitTermPointwise
import Submission.Work.FIArea7.sum_inv_Icc_le_two_log

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-- **The weighted index sum of region I in the split of `charRegionLow6`.** Region I is the set of
pairs `(b,e) ∈ [1, uniB Pa] × [1, X]` with `4be(2K+L₀+2) ≤ N^{δ₁}`; the weight
`(1/b)·(15√N/√(4be) + 2√(4be))` sums to at most `20·X·log(uniB Pa + 2)·(√N + N^{δ₁/2})`.
(Used with `1/√(4be) ≤ 1/2` and, in region I, `4be·4 ≤ N^{δ₁}`, i.e. `√(4be) ≤ N^{δ₁/2}`.) -/
theorem regionLowSplitWeightSum (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ)
    (hX : 1 ≤ X) (hK : 1 ≤ K) :
    ∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
        (1 / (p.1 : ℝ)) * (15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
          + 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ)))
      ≤ 20 * (X : ℝ) * Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)
          * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
  -- ## The size of the two summands
  --
  -- Region I forces `4be(2K+L₀+2) ≤ N^{δ₁}` with `2K+L₀+2 ≥ 4`, hence `4be ≤ N^{δ₁}` and
  -- `√(4be) ≤ N^{δ₁/2}`; and `b,e ≥ 1` gives `4be ≥ 4`, so `√(4be) ≥ 2`.  Thus each term of the
  -- sum is at most `(1/b)·A` with `A := 15√N/2 + 2N^{δ₁/2}`.
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hNnn : (0 : ℝ) ≤ Pa.N := hNpos.le
  have hrnn : (0 : ℝ) ≤ Pa.N ^ (δ₁ / 2) := Real.rpow_nonneg hNnn _
  have hsNnn : (0 : ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := by
    have h1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  set A : ℝ := 15 * Real.sqrt Pa.N / 2 + 2 * Pa.N ^ (δ₁ / 2) with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hpt : ∀ p ∈ charRegionLowFinset Pa X K L₀ δ₁,
      (1 / (p.1 : ℝ)) * (15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
          + 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))) ≤ (1 / (p.1 : ℝ)) * A := by
    intro p hp
    rw [hAdef]
    exact regionLowSplitTermPointwise Pa X K L₀ δ₁ hK hp
  -- ## Extending the sum from region I to the whole box `[1, uniB Pa] × [1,X]`
  have hsub : charRegionLowFinset Pa X K L₀ δ₁
      ⊆ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X) := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := mem_charRegionLowFinset.mp hp
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  -- ## The elementary sum `∑_{(b,e)} 1/b`
  have hcomb : ∑ p ∈ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X), (1 / (p.1 : ℝ))
      ≤ 2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2) := by
    have hinner : ∀ b : ℕ, (∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)))
        = (X : ℝ) * (1 / (b : ℝ)) := by
      intro b
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hprod : ∑ p ∈ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X), (1 / (p.1 : ℝ))
        = ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)) := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
    rw [hprod]
    calc ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ))
        = ∑ b ∈ Finset.Icc 1 (uniB Pa), (X : ℝ) * (1 / (b : ℝ)) :=
          Finset.sum_congr rfl (fun b _ => hinner b)
      _ = (X : ℝ) * ∑ b ∈ Finset.Icc 1 (uniB Pa), (1 / (b : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (X : ℝ) * (2 * Real.log ((uniB Pa : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le_two_log (uniB Pa)) hXnn
      _ = 2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2) := by ring
  have hstep3 : ∑ p ∈ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X), (1 / (p.1 : ℝ)) * A
      ≤ A * (2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)) := by
    calc ∑ p ∈ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X), (1 / (p.1 : ℝ)) * A
        = (∑ p ∈ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X), (1 / (p.1 : ℝ))) * A :=
          (Finset.sum_mul ..).symm
      _ ≤ (2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)) * A :=
          mul_le_mul_of_nonneg_right hcomb hAnn
      _ = A * (2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)) := by ring
  -- ## The final arithmetic: `2A = 15√N + 4N^{δ₁/2} ≤ 20(√N + N^{δ₁/2})`
  have hlast : A * (2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2))
      ≤ 20 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)
          * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
    have hLnn : (0 : ℝ) ≤ Real.log ((uniB Pa : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ (uniB Pa : ℝ) := Nat.cast_nonneg _
      linarith
    have h2A : 2 * A ≤ 20 * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
      rw [hAdef]; linarith [hsNnn, hrnn]
    have hXLnn : (0 : ℝ) ≤ (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2) := mul_nonneg hXnn hLnn
    calc A * (2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2))
        = (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2) * (2 * A) := by ring
      _ ≤ (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)
            * (20 * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2))) :=
          mul_le_mul_of_nonneg_left h2A hXLnn
      _ = 20 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)
            * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by ring
  calc ∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁,
        (1 / (p.1 : ℝ)) * (15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
          + 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ)))
      ≤ ∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁, (1 / (p.1 : ℝ)) * A := Finset.sum_le_sum hpt
    _ ≤ ∑ p ∈ (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X), (1 / (p.1 : ℝ)) * A :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg (by positivity) hAnn)
    _ ≤ A * (2 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)) := hstep3
    _ ≤ 20 * (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2)
          * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := hlast

end

end Work.FIArea7
