import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weighted derivatives of `1 - χ`, up to order `6`

The order-`5` chapter (`Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5`) proves
`|x ^ k · ∂^k (1 - χ)(x)| ≤ M` for `k ≤ 5` by a crude argument: for `k = 0` the bound is `1`,
and for `k ≥ 1` the function `x ↦ x ^ k · ∂^k (1 - χ)(x)` is continuous (χ is `C^∞`) and
vanishes off `|x| ≤ 2`, hence bounded on the compact `[-2,2]`.  Nothing in that argument uses
the order `5`, so we get order `6` by adding the single case `k = 6` to the order-`5` bound. -/

/-- **The weighted derivatives of `1 - χ` are bounded up to order `6`.**  There is a constant
`M` dominating `|x ^ k · ∂^k (1 - χ)(x)|` for all `k ≤ 6` and all `x : ℝ`. -/
theorem OneSubChi_deriv_bound6 :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 6, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  obtain ⟨M5, hM5nn, hM5⟩ := Work.FTS.LocDataExt.OneSubChi_deriv_bound5
  have hsm : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  -- the new case `k = 6`
  have hkey6 : ∃ M6 : ℝ, 0 ≤ M6 ∧ ∀ x : ℝ,
      |x ^ 6 * iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ M6 := by
    have hcont : Continuous (fun x : ℝ =>
        x ^ 6 * iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x) :=
      (continuous_id.pow 6).mul (hsm.continuous_iteratedDeriv 6 (by simp))
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun x : ℝ =>
        x ^ 6 * iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x)
      hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : |x| ≤ 2
    · have hxmem : x ∈ Set.Icc (-2 : ℝ) 2 := by
        rw [Set.mem_Icc, ← abs_le]; exact hx
      have hbound := hC x hxmem
      rw [Real.norm_eq_abs] at hbound
      exact le_trans hbound (le_max_left _ _)
    · -- `|x| > 2`: `χ ≡ 0` on a neighbourhood of `x`, so its derivatives vanish there
      have hx2 : 2 < |x| := not_le.mp hx
      have hvan : iteratedDeriv 6 Work.Stability.chi x = 0 := by
        have hev : Work.Stability.chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| :=
            (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx2)
          filter_upwards [hmem] with y hy
          exact Work.Stability.chi_eq_zero (le_of_lt hy)
        rw [hev.iteratedDeriv_eq 6, Work.Spaces.iteratedDeriv_zero_fun 6 x]
      have hg6 : iteratedDeriv 6 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
          = - iteratedDeriv 6 Work.Stability.chi x := by
        rw [iteratedDeriv_const_sub (by norm_num : 0 < 6) (1 : ℝ)]
        simp
      rw [hg6, hvan]
      simp
  obtain ⟨M6, hM6nn, hM6⟩ := hkey6
  refine ⟨M5 + M6, by linarith, fun k hk x => ?_⟩
  by_cases h : k ≤ 5
  · exact le_trans (hM5 k h x) (by linarith)
  · have hk6 : k = 6 := by omega
    subst hk6
    exact le_trans (hM6 x) (by linarith)

/-- The Bell number of row `6` is `203`, well below `300`. -/
theorem bell_six_le : (Work.Spaces.bell 6 : ℝ) ≤ 300 := by
  have h : Work.Spaces.bell 6 ≤ 300 := by decide
  exact_mod_cast h

/-- **The `D_z`-jets of the cut-off factor `1 - χ(z/L)` are bounded uniformly in the scale
`L ≥ 1`, up to order `6`.**  This extends the delivered
`Work.FTS.LocDataExt.oneSubChi_jet_le5` (orders `≤ 5`, `z ∈ Iz = Ici 0`) by one order: the same
Stirling expansion `DzIterZ_eq_sum_scoef` + dilation `IteratedDeriv_comp_div` +
`abs_sum_scoef_mul_le`, with the extra input `|x^k · ∂^k(1-χ)(x)| ≤ M` for `k ≤ 6`
(`OneSubChi_deriv_bound6`) and `bell 6 = 203 ≤ 300` in place of `bell_le c hc`, `c ≤ 5`. -/
theorem oneSubChi_jet_le6 :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ C := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound6
  have hM1 : 1 ≤ M := by
    have h := hMb 0 (by norm_num) (2 : ℝ)
    have h2 : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (2 : ℝ) = 1 := by
      rw [iteratedDeriv_zero, Work.Stability.chi_eq_zero (by norm_num)]
      norm_num
    simpa [h2] using h
  refine ⟨300 * M, by linarith, fun L hL c hc z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- smoothness of the two cut-off factors
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have hsmL : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) :=
    hsmg.comp (contDiff_id.div_const L)
  -- 1. the θ-independent function is a `z`-only multiplier
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
    have hk6 : k ≤ 6 := le_trans hk hc
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
    exact hMb k hk6 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 300 := by
    have h : Work.Spaces.bell c ≤ 300 := by interval_cases c <;> decide
    exact_mod_cast h
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 300 * M := mul_le_mul_of_nonneg_right hbell hM0

end Work.FTS.LocData6
