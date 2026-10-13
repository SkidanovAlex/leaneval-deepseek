import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.H5.WProd5.Gmaj5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.WProd5

open Work.Spaces

set_option linter.unusedVariables false

/-- **The pointwise majorant of the `𝒲^{5,∞}`-priced product rule.**

The literal `6 ↦ 5` shift (`7 ↦ 6` pure slots, `49 ↦ 36` mixed slots) of the *proved*
`Work.FTS.StrongPersist.H6Rows.WProd6.prod_majorant_winf6`
(`Submission/Work/FTS/StrongPersist/H6Rows/wprod6/Majorant6.lean`), which is itself the level-six
shift of the *proved* `Work.FTS.OpenPkg.prod_majorant_winf`
(`Submission/Work/FTS/OpenPkg/wprod_field_winf.lean`).  Summing the six pure `D_z`-slots
(`hzslot`) and the at most 36 mixed slots (`hmslot`) of `HkIntegrand α 5 (f·g)`, using
`HkIntegrand α 5 g ≤ GmajW5 α g` (from `WProd5.Gmaj5`). -/
theorem prod_majorant_winf5 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 5 f)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 5 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.FTS.StrongEps.H5.WProd5.GmajW5 α g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ
        ≤ (6 * Cz + 36 * Cm) * (Work.Spaces.WlInf α 5 f) ^ 2
            * Work.FTS.StrongEps.H5.WProd5.GmajW5 α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ GmajW5 α g z θ := GmajW5_nonneg hα g hθ
  have hbase : 0 ≤ (6 * Cz + 36 * Cm) * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : HkIntegrand α 5 g z θ ≤ GmajW5 α g z θ :=
        HkIntegrand_le_GmajW5 hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (5 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          ≤ 6 * (Cz * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
        calc (∑ i ∈ Finset.range (5 + 1),
              (DzIter i (fun z θ => f z θ * g z θ) z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (5 + 1), (Cz * (WlInf α 5 f) ^ 2
                * GmajW5 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi5 : i ≤ 5 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi5 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 6 * (Cz * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
            (if 1 ≤ i ∧ i + j ≤ 5 then
              (mixed j i (fun z θ => f z θ * g z θ) z θ
                * Wt α z θ) ^ 2 else 0))
          ≤ 36 * (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
        calc (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
              (if 1 ≤ i ∧ i + j ≤ 5 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (5 + 1), ∑ _j ∈ Finset.range (5 + 1),
                (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 5
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 36 * (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [HkIntegrand]
      calc (∑ i ∈ Finset.range (5 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
              (if 1 ≤ i ∧ i + j ≤ 5 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
          ≤ 6 * (Cz * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ)
            + 36 * (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (6 * Cz + 36 * Cm) * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ := by
            ring
    · have hsin : Real.sin (2 * θ) = 0 := sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [HkIntegrand5_eq_zero_of_sin_two_eq_zero (α := α) (F := fun z θ => f z θ * g z θ)
        (by rw [gam]; linarith) hsin]
      exact hbase

end Work.FTS.StrongEps.H5.WProd5
