/-
Copyright: work module for the Eltindi finite-time singularity project.

# The pointwise majorant for the interior product rule

Summing the two families of summands of `HkIntegrand α 4 (f·g)`:

* the pure `D_z`-summands, bounded by `10^7 |f|_𝒲² HkIntegrand α 4 g`
  (`z_term_le_smoothQuad`), and
* the mixed summands, bounded by `10^12 |f|_𝒲² GmajQ α g` (`m_term_le_smoothQuad`),

one obtains `HkIntegrand α 4 (f·g) ≤ 10^14 |f|_𝒲² GmajQ α g` on `Iz × Iθ`.

The two summand bounds are taken as hypotheses here: they are the two pointwise estimates
proved in `Submission/Work/H2/WPQ/z_term_le_smoothQuad.lean` and
`Submission/Work/H2/WPQ/m_term_le_smoothQuad.lean`.  At the boundary of the quadrant the
statement is trivial: at `z = 0` and at `θ = 0, π/2` the whole integrand `HkIntegrand` vanishes
(the weights carry positive powers of `z` resp. `sin 2θ`), while the right-hand side is
nonnegative.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.H2.WPQ.Interior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces

/-- **The pointwise majorant for the product rule, in the interior class.** -/
theorem HkIntegrand_mul_le_Q {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hfm : Work.Spaces.WlInfMem α 4 f) (hgm : Work.Spaces.HkMem α 4 g)
    (hz_term : ∀ i ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 7 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ)
    (hm_term : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo 0 (π / 2),
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2
        ≤ 10 ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := WlInf_nonneg' hfm
  have hW2 : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  intro z hz θ hθ
  have hGnn : 0 ≤ GmajQ α g z θ := GmajQ_nonneg hα g hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`: the integrand vanishes
    subst hz0
    rw [Work.Spaces.HkIntegrand_zero_z]
    exact mul_nonneg (mul_nonneg (by norm_num) hW2) hGnn
  · by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
    · -- interior: sum the two families of summands
      rw [Work.Spaces.HkIntegrand]
      have hsum1 : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 5 * (10 ^ 7 * (Work.Spaces.WlInf α 4 f) ^ 2
              * Work.Spaces.HkIntegrand α 4 g z θ) := by
        calc (∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (4 + 1), (10 ^ 7 * (Work.Spaces.WlInf α 4 f) ^ 2
                * Work.Spaces.HkIntegrand α 4 g z θ) :=
              Finset.sum_le_sum fun i hi =>
                hz_term i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z hz θ hθi
          _ = 5 * (10 ^ 7 * (Work.Spaces.WlInf α 4 f) ^ 2
                * Work.Spaces.HkIntegrand α 4 g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 25 * (10 ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ) := by
        calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
                (10 ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 4
              · rw [if_pos hc]
                exact hm_term i j hc.1 hc.2 z hzpos θ hθi
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (by norm_num) hW2) hGnn
          _ = 25 * (10 ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      have hle : Work.Spaces.HkIntegrand α 4 g z θ ≤ GmajQ α g z θ := by
        rw [GmajQ]
        exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ1.le)
          (sum_Aang_nonneg α g z)) (theta_factor_nonneg hθ))
      have hcomb : 5 * (10 ^ 7 * (Work.Spaces.WlInf α 4 f) ^ 2
            * Work.Spaces.HkIntegrand α 4 g z θ)
          + 25 * (10 ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ)
          ≤ 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ := by
        have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
          Work.Spaces.HkIntegrand_nonneg α 4 g z θ
        nlinarith [hle, hW2, hHknn, hGnn]
      linarith [hsum1, hsum2, hcomb]
    · -- boundary angle: the integrand vanishes
      have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [HkIntegrand_eq_zero_of_sin_two_eq_zero (F := fun z θ => f z θ * g z θ)
        (by rw [Work.Spaces.gam]; linarith) hsin]
      exact mul_nonneg (mul_nonneg (by norm_num) hW2) hGnn

end Work.FTS.H2.WPQ
