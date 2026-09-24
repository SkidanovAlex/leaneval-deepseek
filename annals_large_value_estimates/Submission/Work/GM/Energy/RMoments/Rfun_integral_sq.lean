import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.RMoments.FejerDefs
import Submission.Work.GM.Energy.RMoments.fejerK_transform
import Submission.Work.GM.Energy.RMoments.SqDefs
import Submission.Work.GM.Energy.RMoments.integral_Rfun_sq_eq_subst

/-!
# GM Lemma 8.2: the second moment of `R` over `v ∈ [1,2]` is `≪ |W|`

`Rfun W v = Σ_{t∈W} |v|^{it}`.  We prove `∫_1^2 ‖Rfun W v‖² dv ≤ 8π |W|` for every
`1`-separated `W`.

The proof is the `L²` analogue of the `L⁴` (additive energy) argument.  Substituting `v = e^u`
(`u ∈ [0, log 2]`, `dv = e^u du`) turns `R` into the plain exponential sum
`F(u) = Σ_{t∈W} e^{itu}`.  On `[0, log 2]` the Fejér kernel `fejerK u = (2π)⁻¹ sinc(u/2)²`
dominates `e^u` (indeed `e^u ≤ 2` and `fejerK u ≥ 1/(4π)`), while its Fourier transform is the
triangle function `tri`, supported in `[-1,1]`.  Hence, expanding `‖F(u)‖² = Σ_{t,s} e^{i(t-s)u}`
and integrating termwise,

`∫_1^2 ‖R‖² dv ≤ 8π ∫_0^{log 2} fejerK u ‖F(u)‖² du ≤ 8π Σ_{t,s∈W} tri(t-s) = 8π |W|`,

the last step because `1`-separation forces `tri(t-s) = 0` for `t ≠ s`.
-/

namespace Work.GM.Energy.RMoments

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

open Commons.Analysis.Fourier (tri tri_eq_zero_of_one_le_abs)

/-- On the positive half-line, `R` is the exponential sum: `Rfun W (e^u) = Σ_{t∈W} e^{itu}`. -/
lemma Rfun_exp_eq_sqF_exp (W : Finset ℝ) (u : ℝ) :
    Submission.GM.Rfun W (Real.exp u) = sqF W u := by
  simp only [Submission.GM.Rfun, sqF, Real.abs_exp]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero u) :
      ((Real.exp u : ℝ) : ℂ) ≠ 0), ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  congr 1
  push_cast
  ring

lemma continuous_sqF (W : Finset ℝ) : Continuous (sqF W) := by
  unfold sqF
  exact continuous_finsetSum _ (fun t _ => by fun_prop)

lemma norm_sqF_le_card (W : Finset ℝ) (u : ℝ) : ‖sqF W u‖ ≤ (W.card : ℝ) := by
  calc ‖sqF W u‖ ≤ ∑ t ∈ W, ‖Complex.exp (Complex.I * ((t * u : ℝ) : ℂ))‖ := by
        unfold sqF; exact norm_sum_le _ _
    _ = ∑ t ∈ W, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [show Complex.I * ((t * u : ℝ) : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I by ring]
        exact Complex.norm_exp_ofReal_mul_I _
    _ = (W.card : ℝ) := by simp

/-- The Fejér kernel dominates `e^u` on `[0, log 2]`. -/
lemma exp_le_eight_pi_mul_fejerK {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (Real.log 2)) :
    Real.exp u ≤ 8 * Real.pi * fejerK u := by
  have hupper : Real.exp u ≤ 2 := by
    calc Real.exp u ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hu.2
      _ = 2 := Real.exp_log (by norm_num)
  have hlow : (4 * Real.pi)⁻¹ ≤ fejerK u := fejerK_lower hu
  have h8 : (0 : ℝ) ≤ 8 * Real.pi := by positivity
  have h2 : (8 * Real.pi) * (4 * Real.pi)⁻¹ = 2 := by
    field_simp
    ring
  calc Real.exp u ≤ 2 := hupper
    _ = (8 * Real.pi) * (4 * Real.pi)⁻¹ := h2.symm
    _ ≤ (8 * Real.pi) * fejerK u := mul_le_mul_of_nonneg_left hlow h8

/-- Conjugation inverts the exponent of `e^{itu}`. -/
lemma conj_exp_I_mul (t u : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)))
      = Complex.exp (Complex.I * (((-t) * u : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma exp_mul_exp_conj (t s u : ℝ) :
    Complex.exp (Complex.I * ((t * u : ℝ) : ℂ))
        * Complex.exp (Complex.I * (((-s) * u : ℝ) : ℂ))
      = Complex.exp (Complex.I * (((t - s) * u : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Expansion of the squared modulus of the exponential sum into a double sum. -/
lemma sqF_mul_conj_expand' (W : Finset ℝ) (u : ℝ) :
    sqF W u * (starRingEnd ℂ) (sqF W u)
      = ∑ t ∈ W, ∑ s ∈ W, Complex.exp (Complex.I * (((t - s) * u : ℝ) : ℂ)) := by
  simp only [sqF]
  rw [map_sum (starRingEnd ℂ) _ W]
  simp_rw [conj_exp_I_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro t ht
  apply Finset.sum_congr rfl; intro s hs
  exact exp_mul_exp_conj t s u

/-- The complexified Fejér kernel is continuous. -/
lemma continuous_fejerK_complex : Continuous (fun u : ℝ => ((fejerK u : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp fejerK_continuous

/-- The complexified Fejér kernel is integrable. -/
lemma integrable_fejerK_complex : Integrable (fun u : ℝ => ((fejerK u : ℝ) : ℂ)) :=
  Complex.ofRealCLM.integrable_comp fejerK_integrable

/-- Integrability of `fejerK u · e^{iδu}` against the exponential. -/
lemma integrable_fejerK_mul_exp (δ : ℝ) :
    Integrable (fun u : ℝ => ((fejerK u : ℝ) : ℂ) * Complex.exp (Complex.I * ((δ * u : ℝ) : ℂ))) := by
  have hexp : Continuous (fun u : ℝ => Complex.exp (Complex.I * ((δ * u : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop)))
  refine Integrable.mono' fejerK_integrable
    ((continuous_fejerK_complex.mul hexp).aestronglyMeasurable) ?_
  filter_upwards with u
  rw [norm_mul,
    show ‖((fejerK u : ℝ) : ℂ)‖ = fejerK u from by
      simp [abs_of_nonneg (fejerK_nonneg u)]]
  have h1 : ‖Complex.exp (Complex.I * ((δ * u : ℝ) : ℂ))‖ = 1 := by
    rw [show Complex.I * ((δ * u : ℝ) : ℂ) = ((δ * u : ℝ) : ℂ) * Complex.I by ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, mul_one]

/-- Integrability of `fejerK u · ‖F(u)‖²`. -/
lemma integrable_fejerK_mul_normSq (W : Finset ℝ) :
    Integrable (fun u : ℝ => fejerK u * ‖sqF W u‖ ^ 2) := by
  refine Integrable.mono' (g := fun u : ℝ => fejerK u * (W.card : ℝ) ^ 2)
    (fejerK_integrable.mul_const _) ?_ ?_
  · exact (fejerK_continuous.mul ((continuous_sqF W).norm.pow 2)).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fejerK_nonneg u) (by positivity))]
    have h2 : ‖sqF W u‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sqF_le_card W u) 2
    nlinarith [fejerK_nonneg u]

/-- The complex integrand is the complexification of the real integrand. -/
lemma fejerK_mul_conj_pointwise (W : Finset ℝ) (u : ℝ) :
    ((fejerK u : ℝ) : ℂ) * (sqF W u * (starRingEnd ℂ) (sqF W u))
      = ((fejerK u * ‖sqF W u‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]

/-- The complex integrand is the complexification of the real integrand. -/
lemma fejerK_mul_conj_expand (W : Finset ℝ) (u : ℝ) :
    ((fejerK u : ℝ) : ℂ) * (sqF W u * (starRingEnd ℂ) (sqF W u))
      = ∑ t ∈ W, ∑ s ∈ W,
          ((fejerK u : ℝ) : ℂ) * Complex.exp (Complex.I * (((t - s) * u : ℝ) : ℂ)) := by
  rw [sqF_mul_conj_expand' W u, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t ht
  rw [Finset.mul_sum]

/-- **The smoothed second moment of the exponential sum.** -/
theorem integral_fejerK_mul_normSq (W : Finset ℝ) :
    (∫ u, fejerK u * ‖sqF W u‖ ^ 2) = ∑ t ∈ W, ∑ s ∈ W, tri (t - s) := by
  have hre : (∫ u, ((fejerK u : ℝ) : ℂ) * (sqF W u * (starRingEnd ℂ) (sqF W u))).re
      = ∫ u, fejerK u * ‖sqF W u‖ ^ 2 := by
    have hone : (∫ u, ((fejerK u : ℝ) : ℂ) * (sqF W u * (starRingEnd ℂ) (sqF W u)))
        = ∫ u, ((fejerK u * ‖sqF W u‖ ^ 2 : ℝ) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall (fejerK_mul_conj_pointwise W))
    have htwo : (∫ u : ℝ, ((fejerK u * ‖sqF W u‖ ^ 2 : ℝ) : ℂ))
        = ((∫ u, fejerK u * ‖sqF W u‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
    rw [hone, htwo, Complex.ofReal_re]
  have htr : (∫ u, ((fejerK u : ℝ) : ℂ) * (sqF W u * (starRingEnd ℂ) (sqF W u)))
      = ((∑ t ∈ W, ∑ s ∈ W, tri (t - s) : ℝ) : ℂ) := by
    rw [show (∫ u, ((fejerK u : ℝ) : ℂ) * (sqF W u * (starRingEnd ℂ) (sqF W u)))
        = ∫ u, ∑ t ∈ W, ∑ s ∈ W,
            ((fejerK u : ℝ) : ℂ) * Complex.exp (Complex.I * (((t - s) * u : ℝ) : ℂ))
        from integral_congr_ae (Filter.Eventually.of_forall (fejerK_mul_conj_expand W))]
    rw [MeasureTheory.integral_finsetSum W
      (fun t ht => MeasureTheory.integrable_finsetSum W
        (fun s hs => integrable_fejerK_mul_exp (t - s)))]
    rw [Finset.sum_congr rfl
      (fun t ht => MeasureTheory.integral_finsetSum W
        (fun s hs => integrable_fejerK_mul_exp (t - s)))]
    simp_rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro t ht
    apply Finset.sum_congr rfl; intro s hs
    exact fejerK_transform (t - s)
  rw [← hre, htr, Complex.ofReal_re]

/-- For a `1`-separated `W` the double sum of the triangle kernel is `|W|`. -/
lemma sum_tri_distance (W : Finset ℝ) (hsep : Submission.GM.Separated W 1) :
    ∑ t ∈ W, ∑ s ∈ W, tri (t - s) = (W.card : ℝ) := by
  have hinner : ∀ t ∈ W, (∑ s ∈ W, tri (t - s)) = 1 := by
    intro t ht
    rw [Finset.sum_eq_single t]
    · simp [tri]
    · intro s hs hst
      exact tri_eq_zero_of_one_le_abs (hsep t ht s hs (Ne.symm hst))
    · intro h
      exact absurd ht h
  rw [Finset.sum_congr rfl hinner]
  simp

/-- The second moment of `R` over `v ∈ [1,2]` is `≪ |W|` (used in GM Lemma 11.8).
For the densest `1`-separated configurations (`W = {1,…,n}`) the integral tends to `π·|W|`, so the
absolute constant exists; the proof needs genuine cancellation (Dirichlet-kernel / mean-period
argument), not the triangle inequality `log T`. -/
theorem Rfun_integral_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Finset ℝ) (T : ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (∫ v in (1:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2) ≤ C * (W.card : ℝ) := by
  refine ⟨8 * Real.pi, by positivity, ?_⟩
  intro W T hW hsep
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  -- the substitution `v = e^u`
  have hstep1 : (∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2)
      = ∫ u in (0 : ℝ)..Real.log 2, Real.exp u * ‖sqF W u‖ ^ 2 := by
    rw [← integral_Rfun_sq_eq_subst W]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Rfun_exp_eq_sqF_exp]
  rw [hstep1]
  -- domination by the Fejér kernel
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) (Real.log 2),
      Real.exp u * ‖sqF W u‖ ^ 2 ≤ 8 * Real.pi * (fejerK u * ‖sqF W u‖ ^ 2) := by
    intro u hu
    calc Real.exp u * ‖sqF W u‖ ^ 2
        ≤ (8 * Real.pi * fejerK u) * ‖sqF W u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (exp_le_eight_pi_mul_fejerK hu) (by positivity)
      _ = 8 * Real.pi * (fejerK u * ‖sqF W u‖ ^ 2) := by ring
  have hInt1 : IntervalIntegrable (fun u : ℝ => Real.exp u * ‖sqF W u‖ ^ 2) volume
      0 (Real.log 2) :=
    (((Real.continuous_exp).mul ((continuous_sqF W).norm.pow 2))).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun u : ℝ => 8 * Real.pi * (fejerK u * ‖sqF W u‖ ^ 2))
      volume 0 (Real.log 2) :=
    ((continuous_const.mul (fejerK_continuous.mul ((continuous_sqF W).norm.pow 2)))).intervalIntegrable _ _
  have hstep2 := intervalIntegral.integral_mono_on hlog2 hInt1 hInt2 hpt
  -- pull out the constant and extend the interval to all of `ℝ`
  have hstep3 : (∫ u in (0 : ℝ)..Real.log 2, 8 * Real.pi * (fejerK u * ‖sqF W u‖ ^ 2))
      = 8 * Real.pi * ∫ u in (0 : ℝ)..Real.log 2, fejerK u * ‖sqF W u‖ ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  have hstep4 : (∫ u in (0 : ℝ)..Real.log 2, fejerK u * ‖sqF W u‖ ^ 2)
      ≤ ∫ u, fejerK u * ‖sqF W u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hlog2]
    exact MeasureTheory.setIntegral_le_integral (integrable_fejerK_mul_normSq W)
      (Filter.Eventually.of_forall fun u => mul_nonneg (fejerK_nonneg u) (by positivity))
  -- evaluate the full integral
  have hstep5 : (∫ u, fejerK u * ‖sqF W u‖ ^ 2) = (W.card : ℝ) := by
    rw [integral_fejerK_mul_normSq W, sum_tri_distance W hsep]
  calc (∫ u in (0 : ℝ)..Real.log 2, Real.exp u * ‖sqF W u‖ ^ 2)
      ≤ ∫ u in (0 : ℝ)..Real.log 2, 8 * Real.pi * (fejerK u * ‖sqF W u‖ ^ 2) := hstep2
    _ = 8 * Real.pi * ∫ u in (0 : ℝ)..Real.log 2, fejerK u * ‖sqF W u‖ ^ 2 := hstep3
    _ ≤ 8 * Real.pi * ∫ u, fejerK u * ‖sqF W u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hstep4 (by positivity)
    _ = 8 * Real.pi * (W.card : ℝ) := by rw [hstep5]

end Work.GM.Energy.RMoments
