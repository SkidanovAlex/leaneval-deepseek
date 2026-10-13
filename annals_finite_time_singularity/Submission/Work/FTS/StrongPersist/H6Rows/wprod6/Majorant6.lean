/-
# `WProd6/Majorant6` — the pointwise sum of the slots of the `𝒲^{6,∞}`-priced product rule

The level-six shift of `Work.FTS.OpenPkg.prod_majorant_winf`.  Given the two slot bounds
(the seven pure `D_z`-slots `i ≤ 6` priced by `HkIntegrand α 6 g`, and the at most 49 mixed
slots `1 ≤ I, I + J ≤ 6` priced by `GmajW6 α g`), the `ℋ⁶`-integrand of the product is
dominated pointwise by `(7 Cz + 49 Cm) |f|²_{𝒲^{6,∞}} GmajW6 α g`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.WProd6

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The pointwise majorant of the `𝒲^{6,∞}`-priced product rule.**

Summing the seven pure `D_z`-slots (`hzslot`) and the at most 49 mixed slots (`hmslot`) of
`HkIntegrand α 6 (f·g)`, using `HkIntegrand α 6 g ≤ GmajW6 α g`. -/
theorem prod_majorant_winf6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : WlInfMem α 6 f)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : HkMem α 6 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ Cz * (WlInf α 6 f) ^ 2 * HkIntegrand α 6 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (mixed J I (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ (7 * Cz + 49 * Cm) * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ GmajW6 α g z θ := GmajW6_nonneg hα g hθ
  have hbase : 0 ≤ (7 * Cz + 49 * Cm) * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : HkIntegrand α 6 g z θ ≤ GmajW6 α g z θ :=
        HkIntegrand_le_GmajW6 hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (6 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          ≤ 7 * (Cz * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1),
              (DzIter i (fun z θ => f z θ * g z θ) z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (6 + 1), (Cz * (WlInf α 6 f) ^ 2
                * GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi6 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 7 * (Cz * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
            (if 1 ≤ i ∧ i + j ≤ 6 then
              (mixed j i (fun z θ => f z θ * g z θ) z θ
                * Wt α z θ) ^ 2 else 0))
          ≤ 49 * (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
                (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 6
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 49 * (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [HkIntegrand]
      calc (∑ i ∈ Finset.range (6 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
          ≤ 7 * (Cz * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ)
            + 49 * (Cm * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (7 * Cz + 49 * Cm) * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ := by
            ring
    · have hsin : Real.sin (2 * θ) = 0 := sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [HkIntegrand6_eq_zero_of_sin_two_eq_zero (α := α) (F := fun z θ => f z θ * g z θ)
        (by rw [gam]; linarith) hsin]
      exact hbase

end Work.FTS.StrongPersist.H6Rows.WProd6
