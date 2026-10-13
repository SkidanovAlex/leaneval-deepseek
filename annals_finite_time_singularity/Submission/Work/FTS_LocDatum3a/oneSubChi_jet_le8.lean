import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData6.oneSubChi_jet_le6
import Submission.Work.FTS_LocDatum3a.OneSubChi_deriv_bound8

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `D_z`-jets of the localising factor `1 - χ(z/L)`, up to order `8`

This is the order-`8` instance of the chain
`Work.FTS.LocData.ZFBase.DzIter_oneSubChi_bound_uniform` (order `4`),
`Work.FTS.LocDataExt.oneSubChi_jet_le5` (order `5`) and
`Work.FTS.LocData6.oneSubChi_jet_le6` (order `6`), and the proof is the same one:
the Stirling expansion `D_z^c = ∑_k S(c,k) z^k ∂_z^k` reduces the jet `D_z^c` of the
dilated factor `1 - χ(z/L)` to the weighted derivatives `(z/L)^k ∂^k(1-χ)(z/L)`, whose
uniform bound in `L ≥ 1` is `OneSubChi_deriv_bound8`; the total coefficient mass is the
Bell number `bell c ≤ 5000` for `c ≤ 8`. -/

/-- The Bell number of row `c` is below `5000`, for `c ≤ 8`.  (`bell 8 = 4140`; the rows
`0..8` are `1, 1, 2, 5, 15, 52, 203, 877, 4140`.) -/
theorem bell_le_5000_of_le_eight {c : ℕ} (hc : c ≤ 8) : (Work.Spaces.bell c : ℝ) ≤ 5000 := by
  have h : Work.Spaces.bell c ≤ 5000 := by interval_cases c <;> decide
  exact_mod_cast h

theorem oneSubChi_jet_le8 :
    ∃ Cu : ℝ, 1 ≤ Cu ∧ ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 8 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound8
  -- `M ≥ 1`, by evaluating the bound at `k = 0`, `x = 2`
  have hM1 : 1 ≤ M := by
    have h := hMb 0 (by norm_num) (2 : ℝ)
    have h2 : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (2 : ℝ) = 1 := by
      rw [iteratedDeriv_zero, Work.Stability.chi_eq_zero (by norm_num)]
      norm_num
    simpa [h2] using h
  refine ⟨5000 * M, by linarith, fun L hL c hc z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- smoothness of the two cut-off factors
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have hsmL : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) :=
    hsmg.comp (contDiff_id.div_const L)
  -- 1. the `θ`-independent function is a `z`-only multiplier
  have h1 : Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ
      = Work.Coercivity.CommutZ.DzIterZ c
          (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z := by
    have h := congrFun (congrFun (Work.Coercivity.CommutZ.DzIter_mulZ c
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))) z) θ
    have hfun : Work.Coercivity.CommutZ.mulZ (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))
        = (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) := rfl
    rw [hfun] at h
    simpa only [Work.Coercivity.CommutZ.mulZ_apply] using h
  rw [h1]
  -- 2. the Stirling expansion
  have h2 : Work.Coercivity.CommutZ.DzIterZ c
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
      = ∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
          (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) := by
    simpa only [] using congrFun (Work.FTS.LocData.DzIterZ_eq_sum_scoef
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) hsmL c) z
  rw [h2]
  -- 3. each summand is bounded by `M`, uniformly in `L`
  have hb : ∀ k ≤ c, |z ^ k * iteratedDeriv k
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z| ≤ M := by
    intro k hk
    have hk8 : k ≤ 8 := le_trans hk hc
    have hrew : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
        = (L⁻¹) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) :=
      Work.FTS.LocData.IteratedDeriv_comp_div
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) hsmg hLne k z
    have hzL : z ^ k * ((L⁻¹) ^ k *
          iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L))
        = (z / L) ^ k * iteratedDeriv k
            (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) := by
      have hdiv : z / L = z * L⁻¹ := by rw [div_eq_mul_inv]
      rw [hdiv, mul_pow]
      ring
    rw [hrew, hzL]
    exact hMb k hk8 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 5000 := bell_le_5000_of_le_eight hc
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 5000 * M := mul_le_mul_of_nonneg_right hbell hM0

end Work.FTS_LocDatum3a
