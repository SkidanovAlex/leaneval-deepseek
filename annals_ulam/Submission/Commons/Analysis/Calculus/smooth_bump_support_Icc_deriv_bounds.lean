import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Set
open scoped ContDiff

set_option autoImplicit false

namespace Commons.Analysis.Calculus

/-- All iterated derivatives of a smooth (`C^∞`) compactly supported function `w : ℝ → ℝ`
are globally bounded: `iteratedDeriv j w` is continuous and its topological support is
contained in the compact set `tsupport w`, hence it is bounded. -/
theorem exists_bound_iteratedDeriv_of_hasCompactSupport_smooth {w : ℝ → ℝ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) w) (hcs : HasCompactSupport w) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j w x| ≤ C := by
  intro j
  have hle : (j : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by exact_mod_cast le_top
  have hcont : Continuous (iteratedDeriv j w) := hw.continuous_iteratedDeriv j hle
  have htsub : tsupport (iteratedDeriv j w) ⊆ tsupport w := by
    refine closure_minimal ?_ (isClosed_tsupport w)
    intro x hx
    by_contra hcon
    have hx2 : x ∉ tsupport (iteratedFDeriv ℝ j w) :=
      fun h => hcon (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) j h)
    have h0 : iteratedFDeriv ℝ j w x = 0 := image_eq_zero_of_notMem_tsupport hx2
    exact hx (by rw [iteratedDeriv_eq_iteratedFDeriv, h0]; simp)
  have hcs' : HasCompactSupport (iteratedDeriv j w) :=
    hcs.of_isClosed_subset (isClosed_tsupport _) htsub
  obtain ⟨C, hC⟩ := hcs'.exists_bound_of_continuous hcont
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have h := hC x
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- **Smooth (C^∞) bump supported in `[1,2]`, equal to `1` on `[6/5,9/5]`.**

IMPORTANT — regularity index: the index here is `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` (smoothness).
Do NOT replace it by `⊤ : WithTop ℕ∞`: in this Mathlib version the regularity-index type is
`ℕ∞ω = WithTop ℕ∞`, where `⊤` means `ω`, i.e. **analyticity**, and the statement with `⊤`
instead of `∞` is FALSE (an analytic function on `ℝ` that is zero off `[1,2]` is identically
zero — see the commons lemma
`Commons.Analysis.Calculus.contDiff_top_hasCompactSupport_eq_zero`).

Construction: take `σ : ContDiffBump (0 : ℝ)` with `rIn = 7/10`, `rOut = 4/5`
(i.e. `⟨7/10, 4/5, by norm_num, by norm_num⟩`), and set
`w x = σ (x - 11/10) * σ (19/10 - x)`.
Then `w` has support `(11/10, 19/10) ⊆ [1,2]`, equals `1` on `[6/5,9/5]`, is nonnegative and
`C^∞` (product of composition of `ContDiffBump.contDiff` with affine maps).  For the derivative
bound: each `iteratedDeriv j w` is continuous
(`ContDiff.continuous_iteratedFDeriv`/`continuous_iteratedDeriv`), its topological support is
contained in `tsupport w ⊆ [1,2]` (use `tsupport_iteratedFDeriv_subset`,
`image_eq_zero_of_notMem_tsupport`), hence it is bounded by `IsCompact.exists_bound_of_continuousOn`
applied to `[1,2]` (take `max C 0` if necessary). -/
theorem smooth_bump_support_Icc_deriv_bounds :
    ∃ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w ∧
      (∀ x, 0 ≤ w x) ∧
      (∀ x, w x ≠ 0 → x ∈ Set.Icc 1 2) ∧
      (∀ x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ), w x = 1) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j w x| ≤ C) := by
  let σ : ContDiffBump (0 : ℝ) := ⟨7 / 10, 4 / 5, by norm_num, by norm_num⟩
  let w : ℝ → ℝ := fun x => σ (x - 11 / 10) * σ (19 / 10 - x)
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) w := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (fun x : ℝ => x - (11 / 10 : ℝ)) :=
      contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (fun x : ℝ => (19 / 10 : ℝ) - x) :=
      contDiff_const.sub contDiff_id
    change ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω)
      (fun x : ℝ => σ (x - 11 / 10) * σ (19 / 10 - x))
    exact ((σ.contDiff (n := (⊤ : ℕ∞))).comp h1).mul
      ((σ.contDiff (n := (⊤ : ℕ∞))).comp h2)
  have hsupp : ∀ x, w x ≠ 0 → x ∈ Icc (1 : ℝ) 2 := by
    intro x hx
    change σ (x - 11 / 10) * σ (19 / 10 - x) ≠ 0 at hx
    obtain ⟨hx1, hx2⟩ := mul_ne_zero_iff.mp hx
    have hb1 : x - 11 / 10 ∈ Metric.ball (0 : ℝ) σ.rOut := by
      rw [← σ.support_eq]; exact hx1
    have hb2 : 19 / 10 - x ∈ Metric.ball (0 : ℝ) σ.rOut := by
      rw [← σ.support_eq]; exact hx2
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hb1 hb2
    obtain ⟨h1a, h1b⟩ := abs_lt.mp hb1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp hb2
    refine ⟨?_, ?_⟩ <;> linarith
  have hone : ∀ x ∈ Icc (6 / 5 : ℝ) (9 / 5 : ℝ), w x = 1 := by
    intro x hx
    change σ (x - 11 / 10) * σ (19 / 10 - x) = 1
    have h1 : σ (x - 11 / 10) = 1 := by
      apply σ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : σ (19 / 10 - x) = 1 := by
      apply σ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [h1, h2, mul_one]
  refine ⟨w, hw, ?_, hsupp, hone, ?_⟩
  · intro x
    change 0 ≤ σ (x - 11 / 10) * σ (19 / 10 - x)
    exact mul_nonneg (σ.nonneg' _) (σ.nonneg' _)
  · have hcs : HasCompactSupport w :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport w)
        (closure_minimal (fun x hx => hsupp x hx) isClosed_Icc)
    exact exists_bound_iteratedDeriv_of_hasCompactSupport_smooth hw hcs

end Commons.Analysis.Calculus