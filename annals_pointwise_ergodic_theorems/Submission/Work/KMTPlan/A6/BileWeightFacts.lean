/-
# Analytic facts about the bilinear weight `t ↦ ‖ψ t‖ ^ 2`

This file collects the elementary analytic properties of the weight
`w_ψ t = ‖ψ t‖ ^ 2` attached to a Schwartz function `ψ : ℝ → ℂ`, which are used in the
bilinear (Krause–Mirek–Tao) pointwise ergodic theory chapter of the A6 area:

* `w_ψ` is differentiable, with derivative
  `deriv w_ψ t = 2 * re (deriv ψ t * conj (ψ t))` (`bileWeight_deriv`), whence
  `‖deriv w_ψ t‖ ≤ 2 * ‖deriv ψ t‖ * ‖ψ t‖`;
* `w_ψ` is integrable on `ℝ` (Schwartz functions are bounded, so `‖ψ‖^2 ≤ C ‖ψ‖` and
  `‖ψ‖` is integrable);
* `deriv w_ψ` is integrable: it is dominated by `2 * C * ‖deriv ψ‖`, and `deriv ψ` is
  again a Schwartz function (`SchwartzMap.derivCLM`), hence has integrable norm;
* for every `R ≥ 1` the samples `n ↦ ‖ψ (n / R)‖ ^ 2` along the lattice `(1/R) ℤ` are
  summable: the samples of `‖ψ‖` itself are summable
  (`Work.KMTAreas.A4.schwartzSamplingSummable`, a Schwartz function decays like
  `|x| ^ (-2)` and the shifted `p`-series with `p = 2` converges), and `‖ψ‖ ^ 2 ≤ C ‖ψ‖`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.schwartzSamplingSummable

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory

/-- Boundedness of a Schwartz function: there is `C > 0` with `‖ψ t‖ ≤ C` for all `t`.
This is the `k = n = 0` case of the Schwartz decay estimate. -/
lemma bileWeight_bdd (ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖(ψ : ℝ → ℂ) t‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := SchwartzMap.decay ψ 0 0
  exact ⟨C, hCpos, fun t => by simpa using hC t⟩

/-- The chain rule for the weight: `t ↦ ∥ψ t∥ ^ 2` has derivative
`2 * re (deriv ψ t * conj (ψ t))` at every point.  This is the inner product chain rule
`HasFDerivAt.norm_sq` for `ψ : ℝ → ℂ` (a real inner product space), together with
`Complex.inner : ⟪w, z⟫_ℝ = (z * conj w).re` read at `w = ψ t`, `z = deriv ψ t`. -/
lemma bileWeight_hasDerivAt (ψ : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖(ψ : ℝ → ℂ) s‖ ^ 2)
      (2 * (deriv (ψ : ℝ → ℂ) t * star ((ψ : ℝ → ℂ) t)).re) t := by
  have h' : HasDerivAt (fun s : ℝ => ‖(ψ : ℝ → ℂ) s‖ ^ 2)
      (2 * ((deriv (ψ : ℝ → ℂ) t).re * ((ψ : ℝ → ℂ) t).re) +
       2 * ((deriv (ψ : ℝ → ℂ) t).im * ((ψ : ℝ → ℂ) t).im)) t := by
    simpa [Complex.inner, innerSL_apply_apply, smul_eq_mul] using
      (SchwartzMap.hasFDerivAt ψ t).norm_sq.hasDerivAt
  convert h' using 1
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The explicit formula for the derivative of the weight. -/
lemma bileWeight_deriv (ψ : SchwartzMap ℝ ℂ) :
    deriv (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2)
      = fun t : ℝ => 2 * (deriv (ψ : ℝ → ℂ) t * star ((ψ : ℝ → ℂ) t)).re := by
  funext t
  exact (bileWeight_hasDerivAt ψ t).deriv

/-- Pointwise bound for the derivative of the weight:
`|deriv (∥ψ ·∥ ^ 2) t| ≤ 2 ‖deriv ψ t‖ ‖ψ t‖`. -/
lemma bileWeight_norm_deriv_le (ψ : SchwartzMap ℝ ℂ) (t : ℝ) :
    ‖deriv (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2) t‖
      ≤ 2 * ‖deriv (ψ : ℝ → ℂ) t‖ * ‖(ψ : ℝ → ℂ) t‖ := by
  rw [bileWeight_deriv]
  simp only
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |(deriv (ψ : ℝ → ℂ) t * star ((ψ : ℝ → ℂ) t)).re|
      ≤ ‖deriv (ψ : ℝ → ℂ) t * star ((ψ : ℝ → ℂ) t)‖ := Complex.abs_re_le_norm _
    _ = ‖deriv (ψ : ℝ → ℂ) t‖ * ‖(ψ : ℝ → ℂ) t‖ := by rw [norm_mul, norm_star]

/-- The weight `t ↦ ∥ψ t∥ ^ 2` is integrable: `‖ψ‖` is integrable (Schwartz) and
`‖ψ t‖ ^ 2 ≤ C ‖ψ t‖` with `C = sup ‖ψ‖`. -/
lemma bileWeight_integrable (ψ : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := bileWeight_bdd ψ
  have hbase : Integrable (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖) := (SchwartzMap.integrable ψ).norm
  refine Integrable.mono' (hbase.const_mul C) ?_ ?_
  · exact (continuous_norm.comp ψ.continuous).pow 2 |>.aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖(ψ : ℝ → ℂ) t‖ ^ 2 = ‖(ψ : ℝ → ℂ) t‖ * ‖(ψ : ℝ → ℂ) t‖ := by ring
      _ ≤ C * ‖(ψ : ℝ → ℂ) t‖ := mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)

/-- The derivative of the weight is integrable.  By `bileWeight_norm_deriv_le` it is
dominated by `2 * C * ‖deriv ψ‖`, where `deriv ψ` is the Schwartz function
`SchwartzMap.derivCLM ℝ ℂ ψ`. -/
lemma bileWeight_integrable_deriv (ψ : SchwartzMap ℝ ℂ) :
    Integrable (deriv (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := bileWeight_bdd ψ
  have hfun : (fun t : ℝ => deriv (ψ : ℝ → ℂ) t) = ⇑(SchwartzMap.derivCLM ℝ ℂ ψ) :=
    funext fun t => (SchwartzMap.derivCLM_apply ℝ ψ t).symm
  have hcont : Continuous (fun t : ℝ => deriv (ψ : ℝ → ℂ) t) := by
    rw [hfun]; exact (SchwartzMap.derivCLM ℝ ℂ ψ).continuous
  have hd : Integrable (fun t : ℝ => deriv (ψ : ℝ → ℂ) t) := by
    rw [hfun]; exact SchwartzMap.integrable _
  have hdn : Integrable (fun t : ℝ => ‖deriv (ψ : ℝ → ℂ) t‖) := hd.norm
  refine Integrable.mono' (hdn.const_mul (2 * C)) ?_ ?_
  · rw [bileWeight_deriv]
    exact (continuous_const.mul (Complex.continuous_re.comp
      (hcont.mul (continuous_star.comp ψ.continuous)))).aestronglyMeasurable
  · filter_upwards with t
    calc ‖deriv (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2) t‖
        ≤ 2 * ‖deriv (ψ : ℝ → ℂ) t‖ * ‖(ψ : ℝ → ℂ) t‖ := bileWeight_norm_deriv_le ψ t
      _ ≤ 2 * ‖deriv (ψ : ℝ → ℂ) t‖ * C :=
          mul_le_mul_of_nonneg_left (hC t) (by positivity)
      _ = 2 * C * ‖deriv (ψ : ℝ → ℂ) t‖ := by ring

/-- The samples `n ↦ ‖ψ (n / R)‖ ^ 2` along the lattice `(1/R) ℤ` are summable for
every positive integer `R`.  `Work.KMTAreas.A4.schwartzSamplingSummable` gives summability
of `n ↦ ‖ψ (n / R)‖`, and `‖ψ‖ ^ 2 ≤ C ‖ψ‖` for the sup bound `C`. -/
lemma bileWeight_summable_div (ψ : SchwartzMap ℝ ℂ) (R : ℕ) (hR : 0 < R) :
    Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := bileWeight_bdd ψ
  have hRne : ((R : ℝ)) ≠ 0 := by exact_mod_cast hR.ne'
  have hlin : Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖) := by
    have h := Work.KMTAreas.A4.schwartzSamplingSummable ψ (a := 0) (c := ((R : ℝ))⁻¹)
      (by simp [hRne])
    simpa [zero_add, inv_mul_eq_div] using h
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hlin.mul_left C)
  calc ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2
      = ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ := by
        ring
    _ ≤ C * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ :=
        mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

theorem BileWeightFacts (ψ : SchwartzMap ℝ ℂ) :
    Differentiable ℝ (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2) ∧
    MeasureTheory.Integrable (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2) ∧
    MeasureTheory.Integrable (deriv (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖ ^ 2)) ∧
    (∀ R : ℕ, 0 < R → Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2)) :=
  ⟨fun t => (bileWeight_hasDerivAt ψ t).differentiableAt,
   bileWeight_integrable ψ,
   bileWeight_integrable_deriv ψ,
   fun R hR => bileWeight_summable_div ψ R hR⟩

end Work.KMTPlan.A6
