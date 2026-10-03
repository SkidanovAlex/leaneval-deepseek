import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.weyl_plane
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_weak_dbar
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.mollify_weak
import Submission.Lib.Unif2.Work.Analysis.Complex.Mollify.mollify_contDiff
import Submission.Lib.Unif2.Work.Analysis.Complex.MeanValue.norm_sq_mul_le_integral_ball

/-!
# Weyl's lemma, weak form: a weak `∂̄`-solution is holomorphic

The target of this file (`Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_weak_dbar_zero`) is the
*analytic* input of the divisor chapter: a locally `L²` function `u` on an open `U ⊆ ℂ` whose
`∂̄`-pairings against all compactly supported `C¹` test functions supported in `U` vanish agrees a.e.
near every point of `U` with an analytic function.

The proof is the classical mollification argument:

1. mollify: `u n := fun z => ∫ t, ρ n t • u (z - t)` for a suitable sequence of normalised bump
   functions `ρ n` supported in `closedBall 0 (ε n)`, `ε n → 0`;
2. the weak equation transports to `u n` (`mollify_weak`) and hence, by
   `dbar_eq_zero_of_weak` + the differentiable Weyl lemma, `u n` is *analytic* on the shrunk domain;
3. the family `(u n)` is locally bounded, with a bound uniform in `n`, because `u ∈ L²_loc`
   (Cauchy–Schwarz + Young's inequality `integral_convolution` + the area mean value inequality);
4. Montel (`Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_ball`) gives a
   locally uniformly convergent subsequence, whose limit is analytic;
5. the mollifications converge a.e. to `u`
   (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), so the limit agrees with `u`
   a.e.
-/

open MeasureTheory Set Filter
open scoped Topology Convolution

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **Cauchy–Schwarz in the `λ` form.**  For a nonnegative integrable `ρ` with `∫ρ = 1` and real
`f` with `ρ f` and `ρ f²` integrable, `(∫ ρ f)² ≤ ∫ ρ f²`.  The proof is the classical one-line
trick: apply `∫ ρ (f - A)² ≥ 0` with `A = ∫ ρ f`. -/
theorem sq_integral_mul_le_integral_mul_sq {ρ f : ℂ → ℝ} (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ : Integrable ρ volume) (h1 : Integrable (fun t => ρ t * f t) volume)
    (h2 : Integrable (fun t => ρ t * f t ^ 2) volume) (hρint : ∫ t, ρ t = 1) :
    (∫ t, ρ t * f t) ^ 2 ≤ ∫ t, ρ t * f t ^ 2 := by
  set A : ℝ := ∫ t, ρ t * f t with hA
  have hEq : (fun t : ℂ => ρ t * (f t - A) ^ 2)
      = (fun t : ℂ => ρ t * f t ^ 2) - (fun t : ℂ => (2 * A) * (ρ t * f t))
        + (fun t : ℂ => (A ^ 2) * ρ t) := by
    funext t
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have h2' : Integrable (fun t : ℂ => (2 * A) * (ρ t * f t)) volume := h1.const_mul (2 * A)
  have h3' : Integrable (fun t : ℂ => (A ^ 2) * ρ t) volume := hρ.const_mul (A ^ 2)
  have hi : Integrable (fun t : ℂ => ρ t * (f t - A) ^ 2) volume := by
    rw [hEq]; exact (h2.sub h2').add h3'
  have h4 : ∫ t, ρ t * (f t - A) ^ 2
      = (∫ t, ρ t * f t ^ 2) - (2 * A) * (∫ t, ρ t * f t) + (A ^ 2) * (∫ t, ρ t) := by
    have hstep : ∫ t, ρ t * (f t - A) ^ 2
        = ∫ t, ρ t * f t ^ 2 - (2 * A) * (ρ t * f t) + (A ^ 2) * ρ t :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    rw [hstep]
    have hP : Integrable (fun t : ℂ => ρ t * f t ^ 2 - (2 * A) * (ρ t * f t)) volume := h2.sub h2'
    have hQ : Integrable (fun t : ℂ => (A ^ 2) * ρ t) volume := h3'
    rw [integral_add hP hQ, integral_sub h2 h2', integral_const_mul, integral_const_mul]
  have h5 : 0 ≤ ∫ t, ρ t * (f t - A) ^ 2 :=
    integral_nonneg fun t => mul_nonneg (hρnn t) (sq_nonneg _)
  rw [h4, hA, hρint, mul_one] at h5
  linarith

/-- **Pointwise Cauchy–Schwarz for a mollification.**  For a globally `L¹` and `L²` function `u`
and a nonnegative bounded mollifier `ρ` of total mass one,
`‖∫ t, ρ t • u (z - t)‖ ^ 2 ≤ ∫ t, ρ t * ‖u (z - t)‖ ^ 2`. -/
theorem norm_mollify_sq_le_integral {u : ℂ → ℂ} {ρ : ℂ → ℝ} (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ : Integrable ρ volume) (hρbdd : ∃ c : ℝ, ∀ᵐ t ∂volume, ‖ρ t‖ ≤ c)
    (hρint : ∫ t, ρ t = 1) (hu : Integrable u volume)
    (hu2 : MemLp u 2 volume) (z : ℂ) :
    ‖(∫ t, ρ t • u (z - t))‖ ^ 2 ≤ ∫ t, ρ t * ‖u (z - t)‖ ^ 2 := by
  have hF2 : Integrable (fun w : ℂ => ‖u w‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hu2.aestronglyMeasurable).mp hu2
  have hF1 : Integrable (fun w : ℂ => ‖u w‖) volume := hu.norm
  have hshift2 : Integrable (fun t : ℂ => ‖u (z - t)‖ ^ 2) volume := by
    have h1 : Integrable (fun s : ℂ => ‖u (-s)‖ ^ 2) volume := hF2.comp_neg
    refine (h1.comp_add_left (-z)).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply]
    rw [show -(-z + t) = z - t by ring]
  have hshift1 : Integrable (fun t : ℂ => ‖u (z - t)‖) volume := by
    have h1 : Integrable (fun s : ℂ => ‖u (-s)‖) volume := hF1.comp_neg
    refine (h1.comp_add_left (-z)).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply]
    rw [show -(-z + t) = z - t by ring]
  obtain ⟨c, hc⟩ := hρbdd
  have hi1 : Integrable (fun t : ℂ => ρ t * ‖u (z - t)‖) volume :=
    (hshift1.mul_bdd hρ.1 hc).congr
      (Filter.Eventually.of_forall fun t => by ring)
  have hi2 : Integrable (fun t : ℂ => ρ t * ‖u (z - t)‖ ^ 2) volume :=
    (hshift2.mul_bdd hρ.1 hc).congr
      (Filter.Eventually.of_forall fun t => by ring)
  have hle : ‖(∫ t, ρ t • u (z - t))‖ ≤ ∫ t, ρ t * ‖u (z - t)‖ := by
    have h2 : (∫ t : ℂ, ‖ρ t • u (z - t)‖) = ∫ t, ρ t * ‖u (z - t)‖ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ‖ρ t • u (z - t)‖ = ρ t * ‖u (z - t)‖
      rw [norm_smul, Real.norm_of_nonneg (hρnn t)]
    have h : ‖(∫ t : ℂ, ρ t • u (z - t))‖ ≤ ∫ t : ℂ, ‖ρ t • u (z - t)‖ :=
      norm_integral_le_integral_norm (μ := volume) (fun t : ℂ => ρ t • u (z - t))
    rwa [h2] at h
  calc ‖(∫ t, ρ t • u (z - t))‖ ^ 2
      ≤ (∫ t, ρ t * ‖u (z - t)‖) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) hle
    _ ≤ ∫ t, ρ t * ‖u (z - t)‖ ^ 2 :=
        sq_integral_mul_le_integral_mul_sq hρnn hρ hi1 hi2 hρint

/-- **The `L²` bound for a mollification.**  For a nonnegative bounded continuous `ρ` with compact
support and total mass one, and a globally `L¹` and `L²` function `u`,
`∫ ‖u ⋆ ρ‖² ≤ ∫ ‖u‖²`.  This is Young's inequality in the case `p = 1`, `q = 2`; the proof is the
pointwise Cauchy–Schwarz bound plus `MeasureTheory.integral_convolution`, so **no Fubini and no
translation-invariance lemma is needed**. -/
theorem integral_norm_sq_mollify_le {u : ℂ → ℂ} {ρ : ℂ → ℝ} (hρnn : ∀ t, 0 ≤ ρ t)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρint : ∫ t, ρ t = 1)
    (hu : Integrable u volume) (hu2 : MemLp u 2 volume) :
    ∫ z, ‖(∫ t, ρ t • u (z - t))‖ ^ 2 ≤ ∫ z, ‖u z‖ ^ 2 := by
  have hρ : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hF2 : Integrable (fun w : ℂ => ‖u w‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hu2.aestronglyMeasurable).mp hu2
  obtain ⟨C, hC⟩ := hρs.isCompact.exists_bound_of_continuousOn hρc.continuousOn
  have hρbdd : ∀ t : ℂ, ‖ρ t‖ ≤ max C 0 := by
    intro t
    by_cases ht : t ∈ tsupport ρ
    · exact le_trans (hC t ht) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport ht, norm_zero]
      exact le_max_right _ _
  have hpt : ∀ z : ℂ, ‖(∫ t, ρ t • u (z - t))‖ ^ 2
      ≤ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun w : ℂ => ‖u w‖ ^ 2)) z := by
    intro z
    refine (norm_mollify_sq_le_integral hρnn hρ ⟨max C 0, Eventually.of_forall hρbdd⟩ hρint
      hu hu2 z).trans (le_of_eq ?_)
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ρ t • ‖u (z - t)‖ ^ 2 = ρ t * ‖u (z - t)‖ ^ 2
    rw [smul_eq_mul]
  have hgint : Integrable (fun z : ℂ =>
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun w : ℂ => ‖u w‖ ^ 2)) z) volume :=
    hρ.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hF2
  calc ∫ z, ‖(∫ t, ρ t • u (z - t))‖ ^ 2
      ≤ ∫ z, (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun w : ℂ => ‖u w‖ ^ 2)) z :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) hgint
          (Filter.Eventually.of_forall hpt)
    _ = (∫ t, ρ t) * (∫ w, ‖u w‖ ^ 2) := by
        rw [integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
          (ν := volume) (f := ρ) (g := fun w : ℂ => ‖u w‖ ^ 2) hρ hF2]
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    _ = ∫ w, ‖u w‖ ^ 2 := by rw [hρint, one_mul]

/-- The pointwise Cauchy–Schwarz bound for a mollification, written as a convolution.  This is the
form in which it dominates `‖u ⋆ ρ‖²` by the *integrable* function `ρ ⋆ ‖u‖²`, which is what makes
`‖u ⋆ ρ‖²` globally integrable. -/
theorem norm_mollify_sq_le_convolution {u : ℂ → ℂ} {ρ : ℂ → ℝ} (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ : Integrable ρ volume) (hρbdd : ∃ c : ℝ, ∀ᵐ t ∂volume, ‖ρ t‖ ≤ c)
    (hρint : ∫ t, ρ t = 1) (hu : Integrable u volume) (hu2 : MemLp u 2 volume) (z : ℂ) :
    ‖(∫ t, ρ t • u (z - t))‖ ^ 2
      ≤ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun w : ℂ => ‖u w‖ ^ 2)) z := by
  refine (norm_mollify_sq_le_integral hρnn hρ hρbdd hρint hu hu2 z).trans (le_of_eq ?_)
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ρ t • ‖u (z - t)‖ ^ 2 = ρ t * ‖u (z - t)‖ ^ 2
  rw [smul_eq_mul]

end Work.Analysis.Complex.DbarCauchy
