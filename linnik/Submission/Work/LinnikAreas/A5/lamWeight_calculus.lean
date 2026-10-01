import Mathlib
import Submission.Work.LinnikAreas.A5.lambert_defs

set_option linter.unusedVariables false

namespace Work.LinnikAreas.A5

/-- Elementary algebra underlying the derivative of `lamWeight`: for `t > 0`,
`s * t^(s-1) * c + t^s * (d * (t⁻¹ / l)) = t^(s-1) * (s * c + d / l)`. -/
private lemma mul_rpow_sub_one_alg {t s l c d : ℝ} (ht0 : 0 < t) :
    s * t ^ (s - 1) * c + t ^ s * (d * (t⁻¹ / l)) = t ^ (s - 1) * (s * c + d / l) := by
  have hp : t ^ s * t⁻¹ = t ^ (s - 1) := by
    rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0]
    ring_nf
  have hfac : t ^ s * (d * (t⁻¹ / l)) = t ^ (s - 1) * (d / l) := by
    rw [← hp]; ring
  rw [hfac]; ring

theorem lamWeight_calculus {x₀ q lam M M' : ℝ} (hx₀ : 0 < x₀) (hq : 1 < q)
    (hσ : 0 ≤ 1 - lam / Real.log q) (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M') {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 x₀)) (hM : ∀ t : ℝ, ‖f t‖ ≤ M)
    (hM' : ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖deriv f t‖ ≤ M') :
    (∀ t ∈ Set.Ioo (1:ℝ) (q ^ x₀),
        HasDerivAt (lamWeight q lam f)
          (t ^ (-(1 - lam / Real.log q) - 1) *
            (-(1 - lam / Real.log q) * f (Real.log t / Real.log q)
              + deriv f (Real.log t / Real.log q) / Real.log q)) t) ∧
    (∀ t ∈ Set.Ioo (1:ℝ) (q ^ x₀),
        ‖deriv (lamWeight q lam f) t‖
          ≤ t ^ (-(1 - lam / Real.log q) - 1) *
              ((1 - lam / Real.log q) * M + M' / Real.log q)) := by
  have hq0 : 0 < q := lt_trans one_pos hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  -- the argument of `f` stays in the interval where `f` is differentiable
  have harg : ∀ t ∈ Set.Ioo (1:ℝ) (q ^ x₀),
      Real.log t / Real.log q ∈ Set.Ioo (0:ℝ) x₀ := by
    intro t ht
    have ht1 : (1:ℝ) < t := ht.1
    have ht0 : 0 < t := lt_trans one_pos ht1
    refine ⟨div_pos (Real.log_pos ht1) hlogq, ?_⟩
    have h1 : Real.log t < x₀ * Real.log q := by
      rw [← Real.log_rpow hq0]
      exact Real.log_lt_log ht0 ht.2
    rw [div_lt_iff₀ hlogq]
    linarith
  have key : ∀ t ∈ Set.Ioo (1:ℝ) (q ^ x₀),
      HasDerivAt (lamWeight q lam f)
        (t ^ (-(1 - lam / Real.log q) - 1) *
          (-(1 - lam / Real.log q) * f (Real.log t / Real.log q)
            + deriv f (Real.log t / Real.log q) / Real.log q)) t := by
    intro t ht
    have ht1 : (1:ℝ) < t := ht.1
    have ht0 : 0 < t := lt_trans one_pos ht1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hy : Real.log t / Real.log q ∈ Set.Ioo (0:ℝ) x₀ := harg t ht
    have hfd : HasDerivAt f (deriv f (Real.log t / Real.log q)) (Real.log t / Real.log q) :=
      DifferentiableAt.hasDerivAt
        ((hf.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hy))
    have h1 : HasDerivAt (fun s : ℝ => s ^ (-(1 - lam / Real.log q)))
        ((-(1 - lam / Real.log q)) * t ^ (-(1 - lam / Real.log q) - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl htne)
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
    have h2 : HasDerivAt (fun s : ℝ => Real.log s / Real.log q) (t⁻¹ / Real.log q) t :=
      hlog.div_const _
    have h3 : HasDerivAt (fun s : ℝ => f (Real.log s / Real.log q))
        (deriv f (Real.log t / Real.log q) * (t⁻¹ / Real.log q)) t :=
      hfd.comp t h2
    have hmul := h1.mul h3
    have hfun : ((fun s : ℝ => s ^ (-(1 - lam / Real.log q))) *
        fun s : ℝ => f (Real.log s / Real.log q)) = lamWeight q lam f := by
      funext s; rfl
    rw [hfun] at hmul
    refine hmul.congr_deriv ?_
    rw [mul_rpow_sub_one_alg (s := -(1 - lam / Real.log q)) (l := Real.log q)
      (c := f (Real.log t / Real.log q)) (d := deriv f (Real.log t / Real.log q)) ht0]
  refine ⟨key, ?_⟩
  intro t ht
  have ht1 : (1:ℝ) < t := ht.1
  have ht0 : 0 < t := lt_trans one_pos ht1
  have hy : Real.log t / Real.log q ∈ Set.Ioo (0:ℝ) x₀ := harg t ht
  rw [(key t ht).deriv]
  have htp : 0 < t ^ (-(1 - lam / Real.log q) - 1) := Real.rpow_pos_of_pos ht0 _
  rw [norm_mul, Real.norm_of_nonneg (le_of_lt htp)]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt htp)
  calc ‖-(1 - lam / Real.log q) * f (Real.log t / Real.log q)
          + deriv f (Real.log t / Real.log q) / Real.log q‖
      ≤ ‖-(1 - lam / Real.log q) * f (Real.log t / Real.log q)‖
          + ‖deriv f (Real.log t / Real.log q) / Real.log q‖ := norm_add_le _ _
    _ = (1 - lam / Real.log q) * ‖f (Real.log t / Real.log q)‖
          + ‖deriv f (Real.log t / Real.log q)‖ / Real.log q := by
        rw [norm_mul, norm_neg, Real.norm_of_nonneg hσ, norm_div,
          Real.norm_of_nonneg (le_of_lt hlogq)]
    _ ≤ (1 - lam / Real.log q) * M + M' / Real.log q := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hM _) hσ
        · exact div_le_div_of_nonneg_right (hM' _ ⟨le_of_lt hy.1, le_of_lt hy.2⟩) (le_of_lt hlogq)

end Work.LinnikAreas.A5
