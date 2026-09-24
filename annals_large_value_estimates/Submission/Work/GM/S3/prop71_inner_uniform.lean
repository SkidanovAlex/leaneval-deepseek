import Mathlib
import Submission.Work.GM.S3.prop71_defs

namespace Work.GM.S3

open Complex MeasureTheory
open scoped BigOperators

/-- The inner integral of GM Prop 7.1 is bounded by an absolute constant (GM: "In general, the
inner integral has size `≪ 1`").  Here `innerInt N m v = ∫ e(-N(m₁v₁+m₂v₂+m₃)u₃) w₂(u₃,v) du₃`
with `w₂(u₃,v) = u₃²w(u₃)²w(v₁u₃)²w(v₂u₃)²` (see `Work.GM.S3.prop71_defs`).

Proof route: `‖∫ f‖ ≤ ∫ ‖f‖ ≤ ∫_{[1,2]} u₃²·(sup w²)³ du₃ ≤ 4·(sup w²)³` — the weight is supported
in `u₃ ∈ [1,2]` and `w` is bounded (`Submission.LargeValues.bumpW_deriv_bdd 0`). -/
theorem prop71_inner_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ),
      ‖innerInt N m v‖ ≤ K := by
  -- `M` bounds `w` (and hence `w²`) uniformly on `ℝ`.
  obtain ⟨M, hM0, hM⟩ := Submission.LargeValues.bumpW_deriv_bdd 0
  have hbW : ∀ x, Submission.LargeValues.bumpW x ≤ M :=
    fun x => le_trans (le_abs_self _) (hM x)
  have hM2 : ∀ x, ‖w2C x‖ ≤ M ^ 2 := by
    intro x
    rw [norm_w2C]
    exact pow_le_pow_left₀ (Submission.LargeValues.bumpW_nonneg x) (hbW x) 2
  refine ⟨7 * M ^ 6 + 1, by positivity, ?_⟩
  intro N m v
  -- exact norm of the weight `w₂`
  have hnorm_eq : ∀ u : ℝ,
      ‖w2v v u‖ = u ^ 2 * ‖w2C u‖ * ‖w2C (v.1 * u)‖ * ‖w2C (v.2 * u)‖ := by
    intro u
    rw [w2v, norm_mul, norm_mul, norm_mul, norm_pow]
    rw [show ‖((u : ℝ) : ℂ)‖ = |u| from by simp, sq_abs]
  -- pointwise bound `‖w₂(u,v)‖ ≤ u² M⁶`
  have hw2v_bound : ∀ u : ℝ, ‖w2v v u‖ ≤ u ^ 2 * M ^ 6 := by
    intro u
    rw [hnorm_eq u]
    calc u ^ 2 * ‖w2C u‖ * ‖w2C (v.1 * u)‖ * ‖w2C (v.2 * u)‖
        ≤ u ^ 2 * M ^ 2 * M ^ 2 * M ^ 2 := by
          gcongr
          · exact hM2 u
          · exact hM2 (v.1 * u)
          · exact hM2 (v.2 * u)
      _ = u ^ 2 * M ^ 6 := by ring
  -- `w₂(·,v)` vanishes off `[1,2]` because `w` does
  have hzero : ∀ u : ℝ, u ∉ Set.Icc (1 : ℝ) 2 → w2v v u = 0 := by
    intro u hu
    rw [w2v, w2C_eq_zero_of_notMem hu]; ring
  -- the pointwise bound against the indicator of `[1,2]`
  have hle : ∀ u : ℝ,
      ‖w2v v u‖ ≤ (Set.Icc (1 : ℝ) 2).indicator (fun u => u ^ 2 * M ^ 6) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (1 : ℝ) 2
    · rw [Set.indicator_of_mem hu]; exact hw2v_bound u
    · rw [Set.indicator_of_notMem hu, hzero u hu, norm_zero]
  have hw2v_meas : Measurable (fun u : ℝ => w2v v u) := by
    have hb : Measurable Submission.LargeValues.bumpW :=
      Submission.LargeValues.bumpW_contDiff.continuous.measurable
    unfold w2v w2C
    fun_prop
  have hw2v_supp : Function.support (fun u : ℝ => w2v v u) ⊆ Set.Icc (1 : ℝ) 2 := by
    intro u hu
    by_contra h
    exact hu (hzero u h)
  have hw2v_bdd : ∀ u : ℝ, ‖w2v v u‖ ≤ 4 * M ^ 6 := by
    intro u
    by_cases hu : u ∈ Set.Icc (1 : ℝ) 2
    · have hu4 : u ^ 2 ≤ 4 := by nlinarith [hu.1, hu.2, sq_nonneg u]
      have h1 := hw2v_bound u
      have h2 : u ^ 2 * M ^ 6 ≤ 4 * M ^ 6 := mul_le_mul_of_nonneg_right hu4 (pow_nonneg hM0 6)
      linarith
    · rw [hzero u hu, norm_zero]; positivity
  have hw2v_int : Integrable (fun u : ℝ => w2v v u) :=
    integrable_of_measurable_bounded_support isCompact_Icc hw2v_meas hw2v_supp hw2v_bdd
  have hF_int : Integrable
      (fun u : ℝ => (Set.Icc (1 : ℝ) 2).indicator (fun u => u ^ 2 * M ^ 6) u) := by
    have hcont : ContinuousOn (fun u : ℝ => u ^ 2 * M ^ 6) (Set.Icc (1 : ℝ) 2) := by fun_prop
    exact (hcont.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  -- the exponential factor has modulus `1`
  have hexp : ∀ u : ℝ,
      ‖Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u))‖ = 1 := by
    intro u
    rw [show -(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u)
        = ((-(2 * Real.pi * ((N : ℝ) * phas m v) * u) : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hgnorm : ∀ u : ℝ, ‖Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u)) *
      w2v v u‖ = ‖w2v v u‖ := by
    intro u
    rw [norm_mul, hexp u, one_mul]
  calc ‖innerInt N m v‖
      = ‖∫ u : ℝ,
          Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u)) * w2v v u‖ := rfl
    _ ≤ ∫ u : ℝ,
          ‖Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u)) * w2v v u‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, ‖w2v v u‖ := integral_congr_ae (Filter.Eventually.of_forall hgnorm)
    _ ≤ ∫ u : ℝ, (Set.Icc (1 : ℝ) 2).indicator (fun u => u ^ 2 * M ^ 6) u :=
          integral_mono hw2v_int.norm hF_int hle
    _ = M ^ 6 * (7 / 3) := by
          rw [integral_indicator measurableSet_Icc]
          rw [show (fun u : ℝ => u ^ 2 * M ^ 6) = fun u => M ^ 6 * u ^ 2 by funext u; ring]
          rw [integral_const_mul]
          congr 1
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
          rw [integral_pow]
          norm_num
    _ ≤ 7 * M ^ 6 + 1 := by nlinarith [pow_nonneg hM0 6]

end Work.GM.S3
