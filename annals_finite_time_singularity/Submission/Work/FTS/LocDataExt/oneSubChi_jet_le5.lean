import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData.DzIter_oneSubChi_bound
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.scoef
import Submission.Work.Stability.Cutoff
import Submission.Work.Coercivity.CommutZBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option linter.unusedVariables false

/-! ## The weighted derivatives of `1 - χ`, up to order `5`

The proof of `Work.FTS.LocData.OneSubChi_deriv_bound` (orders `≤ 4`) uses nothing about `4`:
for `k ≥ 1` the function `x ↦ x ^ k · ∂^k (1 - χ)(x)` is continuous (χ is `C^∞`) and vanishes
off `|x| ≤ 2`, hence is bounded on the compact set `[-2,2]`; the case `k = 0` is the trivial
bound `|1 - χ x| ≤ 1`.  We re-run that argument with the order bound `5`. -/

/-- **The weighted derivatives of `1 - χ` are bounded up to order `5`.**  There is a constant
`M` dominating `|x ^ k · ∂^k (1 - χ)(x)|` for all `k ≤ 5` and all `x : ℝ`. -/
theorem OneSubChi_deriv_bound5 :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 5, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have key : ∀ k : ℕ, ∃ Mk : ℝ, 0 ≤ Mk ∧
      ∀ x : ℝ, |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ Mk := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · -- `k = 0`: the bound `|1 - χ x| ≤ 1`
      subst h0
      refine ⟨1, zero_le_one, fun x => ?_⟩
      have hxg : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
          = 1 - Work.Stability.chi x :=
        congrFun (iteratedDeriv_zero (f := fun x : ℝ => (1 : ℝ) - Work.Stability.chi x)) x
      rw [hxg]
      simp only [pow_zero, one_mul]
      rw [abs_le]
      constructor
      · linarith [Work.Stability.chi_le_one x]
      · linarith [Work.Stability.chi_nonneg x]
    · -- `k ≥ 1`: continuity on the compact set `[-2,2]` plus vanishing off `(-2,2)`
      have hcont : Continuous (fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x) :=
        (continuous_id.pow k).mul (hsm.continuous_iteratedDeriv k (by simp))
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x)
        hcont.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      by_cases hx : |x| ≤ 2
      · have hxmem : x ∈ Set.Icc (-2 : ℝ) 2 := by
          rw [Set.mem_Icc, ← abs_le]; exact hx
        have hbound := hC x hxmem
        rw [Real.norm_eq_abs] at hbound
        exact le_trans hbound (le_max_left _ _)
      · -- `|x| > 2`: `χ ≡ 0` on a neighbourhood of `x`, so all its derivatives vanish there
        have hx2 : 2 < |x| := not_le.mp hx
        have hvan : iteratedDeriv k Work.Stability.chi x = 0 := by
          have hev : Work.Stability.chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
            have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| :=
              (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx2)
            filter_upwards [hmem] with y hy
            exact Work.Stability.chi_eq_zero (le_of_lt hy)
          rw [hev.iteratedDeriv_eq k, Work.Spaces.iteratedDeriv_zero_fun k x]
        have hgk : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
            = - iteratedDeriv k Work.Stability.chi x := by
          rw [iteratedDeriv_const_sub hpos (1 : ℝ)]
          simp
        rw [hgk, hvan]
        simp
  obtain ⟨M0, _, hM0⟩ := key 0
  obtain ⟨M1, _, hM1⟩ := key 1
  obtain ⟨M2, _, hM2⟩ := key 2
  obtain ⟨M3, _, hM3⟩ := key 3
  obtain ⟨M4, _, hM4⟩ := key 4
  obtain ⟨M5, _, hM5⟩ := key 5
  refine ⟨M0 + M1 + M2 + M3 + M4 + M5, by linarith, fun k hk x => ?_⟩
  interval_cases k
  · exact le_trans (hM0 x) (by linarith)
  · exact le_trans (hM1 x) (by linarith)
  · exact le_trans (hM2 x) (by linarith)
  · exact le_trans (hM3 x) (by linarith)
  · exact le_trans (hM4 x) (by linarith)
  · exact le_trans (hM5 x) (by linarith)

/-- The Bell number of row `5` is well below `100`. -/
theorem bell_five_le : (Work.Spaces.bell 5 : ℝ) ≤ 100 := by
  have h : Work.Spaces.bell 5 ≤ 100 := by decide
  exact_mod_cast h

/-- The `D_z`-jets of the cut-off factor `1 - χ(z/L)` are bounded uniformly in the scale
`L ≥ 1`, up to order `5`.  This extends the delivered
`Work.FTS.LocData.ZFBase.DzIter_oneSubChi_bound_uniform` (orders `≤ 4`, `z ∈ Iz = Ici 0`) by one
order: the same Stirling expansion `DzIterZ_eq_sum_scoef` + dilation `IteratedDeriv_comp_div` +
`abs_sum_scoef_mul_le`, with the extra input `|x^k · ∂^k(1-χ)(x)| ≤ M` for `k ≤ 5` (the proof of
`Work.FTS.LocData.OneSubChi_deriv_bound` works verbatim for `k = 5`; it is stated for `k ≤ 4`)
and `bell 5 = 52 ≤ 100` in place of `bell_le c hc`, `c ≤ 4`. -/
theorem oneSubChi_jet_le5 :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 5 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ C := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound5
  have hM1 : 1 ≤ M := by
    have h := hMb 0 (by norm_num) (2 : ℝ)
    have h2 : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (2 : ℝ) = 1 := by
      rw [iteratedDeriv_zero, Work.Stability.chi_eq_zero (by norm_num)]
      norm_num
    simpa [h2] using h
  refine ⟨100 * M, by linarith, fun L hL c hc z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- smoothness of the two cut-off factors
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
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
    have hk5 : k ≤ 5 := le_trans hk hc
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
    exact hMb k hk5 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 100 := by
    have h : Work.Spaces.bell c ≤ 100 := by interval_cases c <;> decide
    exact_mod_cast h
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right hbell hM0

end Work.FTS.LocDataExt
