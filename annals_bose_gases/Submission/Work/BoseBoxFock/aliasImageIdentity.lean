import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.firstMoment_heatForm
import Submission.Work.BoseBoxFock.heatImage_tsum_conds
import Submission.Work.BoseBoxFock.imageHeat_swap
import Submission.Work.BoseBoxFock.imageW_lens_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary helpers for the assembly -/

/-- Pulling a nonzero constant out of a `tsum`.  No summability hypothesis is needed: when the
family is not summable both sides are `0`. -/
lemma tsum_mul_left_of_ne_zero {ι : Type*} {f : ι → ℝ} {c : ℝ} (hc : c ≠ 0) :
    (∑' i, c * f i) = c * ∑' i, f i := by
  by_cases h : Summable f
  · exact h.tsum_mul_left c
  · have hc' : ¬ Summable (fun i => c * f i) := by
      intro hs
      refine h ((hs.mul_left c⁻¹).congr (fun i => ?_))
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [tsum_eq_zero_of_not_summable hc', tsum_eq_zero_of_not_summable h, mul_zero]

/-- `‖latVec m‖ ≥ 1` for `m ≠ 0`. -/
lemma one_le_norm_latVec {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm (funext h)
  have h1 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast h2
  have h2 : ‖(latVec m).ofLp i‖ = |((m i : ℤ) : ℝ)| := by
    have h3 : (latVec m).ofLp i = ((m i : ℤ) : ℝ) := by
      simp [latVec, WithLp.ofLp_toLp]
    rw [h3, Real.norm_eq_abs]
  calc (1 : ℝ) ≤ ‖(latVec m).ofLp i‖ := by rw [h2]; exact h1
    _ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i

/-- At the lattice image `ℓ • latVec m` (`m ≠ 0`) the autocorrelation kernel vanishes: the
touching point of the ball `B(0, ℓ/2)` and its translate. -/
lemma aliasKernel_latVec_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) : aliasKernel g (ℓ • latVec m) = 0 := by
  have hge : ℓ ≤ ‖ℓ • latVec m‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    calc ℓ = ℓ * 1 := (mul_one ℓ).symm
      _ ≤ ℓ * ‖latVec m‖ := mul_le_mul_of_nonneg_left (one_le_norm_latVec hm) hℓ.le
  have h := autocorr_eq_zero_of_le_norm hℓ hg hgsupp hge
  simp only [aliasKernel, h, Complex.zero_re]

/-- The per-`m` spatial integrability hypothesis of `imageHeat_swap`, deduced from the
`tsum`-level estimate of the image weights. -/
lemma integrable_aliasKernel_imgW {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    Integrable (fun u : E3 =>
      aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹) := by
  have hsumm := tsum_lintegral_aliasKernel_imageW_lens hℓ hg hgsupp
  have hterm : (∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) ≠ ⊤ := by
    intro htop
    exact hsumm (top_unique (htop ▸ ENNReal.le_tsum (f := fun m : Fin 3 → ℤ =>
      ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) m))
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  have hcont : Continuous (aliasKernel g) := Complex.continuous_re.comp (autocorr_continuous hg hgc)
  have hpinv : Measurable (fun u : E3 => (‖u - ℓ • latVec m‖ ^ 4)⁻¹) :=
    (((continuous_norm.comp (continuous_id.sub continuous_const)).pow 4).measurable).inv
  have hmeas : AEStronglyMeasurable (fun u : E3 =>
      aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹) volume := by
    refine Measurable.aestronglyMeasurable ?_
    exact (hcont.measurable.mul measurable_const).mul hpinv
  refine ⟨hmeas, ?_⟩
  have hc0 : (0 : ℝ) ≤ 2 / Real.pi ^ (3 / 2 : ℝ) := by positivity
  have hpt : ∀ u : E3,
      ‖aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹‖ₑ
        = ENNReal.ofReal (2 / Real.pi ^ (3 / 2 : ℝ))
          * ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) := by
    intro u
    have hw : (0 : ℝ) ≤ (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by positivity
    have hval : |aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹|
        = (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖aliasKernel g u‖ * imgW ℓ m u) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg hw, imgW_ne_zero hm,
        ← Real.norm_eq_abs]
      ring
    rw [Real.enorm_eq_ofReal_abs, hval, ENNReal.ofReal_mul hc0]
  have hmeas2 : Measurable (fun u : E3 =>
      ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) := by
    simp only [imgW_ne_zero hm]
    exact ENNReal.measurable_ofReal.comp (hcont.norm.measurable.mul hpinv)
  have hmain : (∫⁻ u : E3,
      ‖aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹‖ₑ)
      = ENNReal.ofReal (2 / Real.pi ^ (3 / 2 : ℝ))
        * ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) := by
    rw [lintegral_congr hpt]
    rw [lintegral_const_mul (ENNReal.ofReal (2 / Real.pi ^ (3 / 2 : ℝ))) hmeas2]
  show (∫⁻ u : E3,
      ‖aliasKernel g u * (2 / Real.pi ^ (3 / 2 : ℝ)) * (‖u - ℓ • latVec m‖ ^ 4)⁻¹‖ₑ) < ⊤
  rw [hmain]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hterm)

/-- The arithmetic of the two constants: `(2√π)⁻¹·2π^{-3/2} = π⁻²`. -/
lemma aliasImage_const_arith :
    (2 * Real.sqrt Real.pi)⁻¹ * (2 / Real.pi ^ ((3 : ℝ) / 2)) = (Real.pi)⁻¹ ^ 2 := by
  have hpi : Real.pi ^ ((3 : ℝ) / 2) = Real.pi * Real.sqrt Real.pi := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hpi]
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos_of_pos Real.pi_pos).ne'
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  exact (Real.sq_sqrt Real.pi_pos.le).symm

/-- **The image (Poisson/aliasing) form of the first-moment deficit.**  For `g` smooth with
`tsupport g ⊆ B(0,ℓ/2)` (open ball):

    R1 − S1 = π⁻² Σ_{m ≠ 0} ∫_u 𝒢(u) ‖u − ℓ • latVec m‖⁻⁴ du ,

where `R1 = kinFirst g = (2π)⁻³∫‖p‖‖kinFT g p‖²`, `S1 = Σ_n ℓ⁻³‖kmomInt ℓ n‖‖kinFT g (kmomInt ℓ n)‖²`,
and `𝒢 = aliasKernel g = Re(autocorr g)` with `autocorr g u = ∫_x g x · conj(g (x−u))`.
(For real `g`, `𝒢 = g ⋆ g̃`; `Im(autocorr)` is odd and drops out because the kernel is even.)

Proof route — every ingredient is already in the corpus, `aliasIdentity` has 0 sorries:
1. subordination `√λ = (2√π)⁻¹∫_0^∞ t^{-3/2}(1−e^{−tλ})dt` gives
   `R1 − S1 = (2√π)⁻¹∫_0^∞ t^{-3/2}(latHeat ℓ t g − contHeat g t)dt` **provided** the two masses
   agree, `Σ'_{n}ℓ⁻³‖kinFT g (kmomInt ℓ n)‖² = kinMass g`, which follows from `hgsupp` (the
   `ℓ`-translates of `supp g` are disjoint, so `𝒢` vanishes at every nonzero lattice point);
2. the PROVED `Work.BoseBoxFock.aliasIdentity` rewrites the bracket as
   `Σ'_{m≠0}∫_u aliasKernel g u · heatK t (ℓ • latVec m − u)`;
3. `∫_0^∞ t^{-3/2} heatK t z dt = 2π^{-3/2}‖z‖^{-4}` (with `heatK t z = (4πt)^{-3/2}e^{−‖z‖²/4t}`),
   and `2π^{-3/2}/(2√π) = π^{-2}`.

The remaining work is interchange of the `t`-, `u`- and `m`-integrals (dominated convergence;
the `m`-sum converges since `supp (aliasKernel g) ⊆ closedBall 0 ℓ` and distinct images
`ℓ • latVec m` are at distance `≥ ℓ`), plus the `m ≠ 0` guard (the `m = 0` term is singular at
`u = 0` where `𝒢(0) = ∫‖g‖² ≠ 0`). -/
theorem aliasImageIdentity {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    Work.BoseBoxFock.kinFirst g
      - (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ *
          ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = (Real.pi)⁻¹ ^ 2 * ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.aliasKernel g u *
            (‖u - ℓ • Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := by
  -- Step 1: the heat (subordination) form of the deficit.
  have hsub := firstMoment_heatForm hℓ hg hgsupp
  -- Step 2: pointwise (in `t > 0`) the bracket is the `m`-sum of the heat images.
  have hpoint : Set.EqOn
      (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * (latHeat ℓ t g - contHeat g t))
      (fun t : ℝ => ∑' m : Fin 3 → ℤ, t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t)
      (Set.Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hne : t ^ (-(3 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
    change t ^ (-(3 / 2 : ℝ)) * (latHeat ℓ t g - contHeat g t)
      = ∑' m : Fin 3 → ℤ, t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t
    rw [aliasIdentity hℓ hg hgsupp ht0]
    rw [← tsum_mul_left_of_ne_zero hne]
    refine tsum_congr (fun m => ?_)
    simp only [heatImage]
  -- Step 3: the two hypotheses of `integral_tsum`.
  have hsumm := tsum_lintegral_aliasKernel_imageW_lens hℓ hg hgsupp
  have hconds := heatImage_tsum_conds hℓ hg hgsupp hsumm
  have hswap : (∫ t in Set.Ioi (0 : ℝ), ∑' m : Fin 3 → ℤ,
        t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t)
      = ∑' m : Fin 3 → ℤ, ∫ t in Set.Ioi (0 : ℝ),
          t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t :=
    integral_tsum hconds.1 hconds.2
  -- Step 4: the per-`m` value, `∫_t t^{-3/2} heatImage = (2/π^{3/2})∫_u 𝒢 imgW`.
  have hperm : ∀ m : Fin 3 → ℤ,
      (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t)
        = ∫ u : E3, aliasKernel g u * ((2 / Real.pi ^ (3 / 2 : ℝ)) * imgW ℓ m u) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp
    · have hvanish : aliasKernel g (ℓ • latVec m) = 0 := aliasKernel_latVec_eq_zero hℓ hg hgsupp hm
      have hint := integrable_aliasKernel_imgW hℓ hg hgsupp hm
      rw [show (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t)
          = ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
              (∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u)) from by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        rw [heatImage_ne_zero hm]]
      rw [imageHeat_swap hℓ hm hvanish hint]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      simp only [imgW_ne_zero hm]
      ring
  -- Step 5: pull the constant `2π^{-3/2}` out of the `m`-sum.
  have hsum_swap : (∑' m : Fin 3 → ℤ,
        ∫ u : E3, aliasKernel g u * ((2 / Real.pi ^ (3 / 2 : ℝ)) * imgW ℓ m u))
      = (2 / Real.pi ^ (3 / 2 : ℝ)) *
        ∑' m : Fin 3 → ℤ, ∫ u : E3, aliasKernel g u * imgW ℓ m u := by
    have h1 : ∀ m : Fin 3 → ℤ,
        (∫ u : E3, aliasKernel g u * ((2 / Real.pi ^ (3 / 2 : ℝ)) * imgW ℓ m u))
          = (2 / Real.pi ^ (3 / 2 : ℝ)) *
            (∫ u : E3, aliasKernel g u * imgW ℓ m u) := by
      intro m
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      ring
    rw [tsum_congr h1, tsum_mul_left_of_ne_zero (by positivity)]
  -- Step 6: the `m = 0` guard.
  have hguard : ∀ m : Fin 3 → ℤ, (∫ u : E3, aliasKernel g u * imgW ℓ m u)
      = if m = 0 then 0 else ∫ u : E3, aliasKernel g u * (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp
    · rw [if_neg hm]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      simp only [imgW_ne_zero hm]
  calc
    kinFirst g
        - (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        = (2 * Real.sqrt Real.pi)⁻¹ *
            ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (latHeat ℓ t g - contHeat g t) := hsub
    _ = (2 * Real.sqrt Real.pi)⁻¹ *
            ∫ t in Set.Ioi (0 : ℝ), ∑' m : Fin 3 → ℤ,
              t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t := by
          rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
    _ = (2 * Real.sqrt Real.pi)⁻¹ *
            ∑' m : Fin 3 → ℤ, ∫ t in Set.Ioi (0 : ℝ),
              t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t := by
          rw [hswap]
    _ = (2 * Real.sqrt Real.pi)⁻¹ *
            ∑' m : Fin 3 → ℤ,
              ∫ u : E3, aliasKernel g u * ((2 / Real.pi ^ (3 / 2 : ℝ)) * imgW ℓ m u) := by
          rw [tsum_congr hperm]
    _ = (2 * Real.sqrt Real.pi)⁻¹ * ((2 / Real.pi ^ (3 / 2 : ℝ)) *
            ∑' m : Fin 3 → ℤ, ∫ u : E3, aliasKernel g u * imgW ℓ m u) := by
          rw [hsum_swap]
    _ = (Real.pi)⁻¹ ^ 2 * ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          ∫ u : E3, aliasKernel g u * (‖u - ℓ • latVec m‖ ^ 4)⁻¹) := by
          rw [tsum_congr hguard]
          rw [← mul_assoc, aliasImage_const_arith]

end Work.BoseBoxFock
