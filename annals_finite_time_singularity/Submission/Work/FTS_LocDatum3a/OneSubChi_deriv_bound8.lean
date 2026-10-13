import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.LocData6.oneSubChi_jet_le6
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

/-! ## The weighted derivatives of `1 - χ`, up to order `8`

The order-`5` chapter (`Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5`) and the order-`6`
chapter (`Submission.Work.FTS.LocData6.oneSubChi_jet_le6`) prove
`|x ^ k · ∂^k (1 - χ)(x)| ≤ M` for `k ≤ 5` resp. `k ≤ 6` by a crude argument: for `k = 0` the
bound is `1`, and for `k ≥ 1` the function `x ↦ x ^ k · ∂^k (1 - χ)(x)` is continuous (χ is
`C^∞`) and vanishes off `|x| ≤ 2`, hence is bounded on the compact `[-2,2]`.  Nothing in that
argument uses the order bound, so the same proof yields every order; here we collect the terms
`k ≤ 8`. -/

theorem OneSubChi_deriv_bound8 :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 8, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  -- For every single order `k` the weighted derivative is bounded.
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
  let Mf : ℕ → ℝ := fun k => Classical.choose (key k)
  have hMf_nn : ∀ k : ℕ, 0 ≤ Mf k := fun k => (Classical.choose_spec (key k)).1
  have hMf : ∀ k : ℕ, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ Mf k :=
    fun k x => (Classical.choose_spec (key k)).2 x
  refine ⟨∑ k ∈ Finset.range 9, Mf k, Finset.sum_nonneg (fun k _ => hMf_nn k), fun k hk x => ?_⟩
  have hk9 : k ∈ Finset.range 9 := Finset.mem_range.mpr (by omega)
  exact le_trans (hMf k x) (Finset.single_le_sum (fun i _ => hMf_nn i) hk9)

end Work.FTS_LocDatum3a
