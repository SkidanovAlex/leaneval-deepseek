import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.aliasImageDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.heatImage_tsum_conds`

The two `MeasureTheory.integral_tsum`-hypotheses for the image (Poisson) form of the
first-moment deficit `Work.BoseBoxFock.aliasImageIdentity`:

* for every `m`, the function `t ↦ t^{-3/2}·heatImage ℓ g m t` is a.e. strongly measurable
  on `(0, ∞)`;
* the `ℝ≥0∞`-series `∑'_m ∫⁻_{t>0} ‖t^{-3/2}·heatImage ℓ g m t‖ₑ` is finite — and it is,
  because the `t`-integral of each summand is bounded by `2π^{-3/2}·∫_u ‖𝒢(u)‖·imgW ℓ m u`,
  whose `m`-sum is finite by hypothesis (`hsumm`).

The `t`-integral identity used is `Work.BoseBoxFock.SqrtKin.heatK_t_rpow_lintegral`
(`∫_{t>0} t^{-3/2}heatK t z = 2π^{-3/2}‖z‖^{-4}`); the single point `u = ℓ • latVec m` where
the kernel `‖z‖^{-4}` is singular carries no mass because
`aliasKernel g (ℓ • latVec m) = 0` (`autocorr_eq_zero_of_le_norm`: the ball `B(0,ℓ/2)`
and its translate by `ℓ • latVec m` are disjoint since `‖latVec m‖ ≥ 1` for `m ≠ 0`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `g` smooth with `tsupport g ⊆ B(0, ℓ/2)` has compact support. -/
theorem hts_hasCompactSupport {ℓ : ℝ} {g : E3 → ℂ}
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) : HasCompactSupport g := by
  rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩

/-- `‖latVec m‖ ≥ 1` for `m ≠ 0`. -/
theorem hts_one_le_norm_latVec {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hm (funext h)
  have hcoord : (1 : ℝ) ≤ ‖(latVec m).ofLp i‖ := by
    have h1 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
      have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
      exact_mod_cast h2
    have h3 : (latVec m).ofLp i = ((m i : ℤ) : ℝ) := by
      simp [latVec, WithLp.ofLp_toLp]
    rw [h3, Real.norm_eq_abs]
    exact h1
  exact le_trans hcoord (PiLp.norm_apply_le (latVec m) i)

/-- At the lattice image `ℓ • latVec m` (`m ≠ 0`) the autocorrelation kernel vanishes: the
touching point of the ball `B(0, ℓ/2)` and its translate. -/
theorem hts_aliasKernel_latVec_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) : aliasKernel g (ℓ • latVec m) = 0 := by
  have hge : ℓ ≤ ‖ℓ • latVec m‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    calc ℓ = ℓ * 1 := (mul_one ℓ).symm
      _ ≤ ℓ * ‖latVec m‖ := mul_le_mul_of_nonneg_left (hts_one_le_norm_latVec hm) hℓ.le
  have h := autocorr_eq_zero_of_le_norm hℓ hg hgsupp hge
  simp only [aliasKernel, h, Complex.zero_re]

/-- `imgW` as a negative power of the norm. -/
theorem hts_imgW_eq_rpow {ℓ : ℝ} {m : Fin 3 → ℤ} (hm : m ≠ 0) (u : E3) :
    imgW ℓ m u = ‖u - ℓ • latVec m‖ ^ (-(4 : ℝ)) := by
  have hA : (‖u - ℓ • latVec m‖ ^ 4)⁻¹ = (‖u - ℓ • latVec m‖ ^ ((4 : ℕ) : ℝ))⁻¹ :=
    (congrArg Inv.inv (Real.rpow_natCast ‖u - ℓ • latVec m‖ 4)).symm
  have hB : (‖u - ℓ • latVec m‖ ^ ((4 : ℕ) : ℝ))⁻¹ = ‖u - ℓ • latVec m‖ ^ (-(4 : ℝ)) :=
    (Real.rpow_neg (norm_nonneg (u - ℓ • latVec m)) 4).symm
  rw [imgW_ne_zero hm]
  exact hA.trans hB

/-! ## The per-`m` bound on the `t`-integral -/

/-- **The per-`m` `t`-integral bound.**  For every `m`,
`∫⁻_{t>0} ‖t^{-3/2}·heatImage ℓ g m t‖ₑ ≤ 2π^{-3/2}·∫⁻_u ofReal(‖𝒢(u)‖·imgW ℓ m u)`. -/
theorem heatImage_setLIntegral_enorm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    (m : Fin 3 → ℤ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖t ^ (-(3 : ℝ) / 2) * heatImage ℓ g m t‖ₑ)
      ≤ ENNReal.ofReal (2 / Real.pi ^ ((3 : ℝ) / 2))
        * ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) := by
  have hc0 : (0 : ℝ) ≤ 2 / Real.pi ^ ((3 : ℝ) / 2) := by positivity
  by_cases hm : m = 0
  · subst hm
    simp
  have hgc : HasCompactSupport g := hts_hasCompactSupport hgsupp
  have halias : Continuous (aliasKernel g) :=
    Complex.continuous_re.comp (autocorr_continuous hg hgc)
  set z : E3 := ℓ • latVec m with hz
  have hker : aliasKernel g z = 0 := by
    rw [hz]; exact hts_aliasKernel_latVec_eq_zero hℓ hg hgsupp hm
  -- joint measurability, for Tonelli
  have hFmeas : AEMeasurable (Function.uncurry (fun t : ℝ => fun u : E3 =>
      ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (‖aliasKernel g u‖ * heatK t (z - u)))))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    have h1 : Measurable (fun p : ℝ × E3 => p.1 ^ (-(3 : ℝ) / 2)) := by fun_prop
    have h2 : Measurable (fun p : ℝ × E3 => ‖aliasKernel g p.2‖) :=
      (halias.measurable.comp measurable_snd).norm
    have h3 : Measurable (fun p : ℝ × E3 => heatK p.1 (z - p.2)) := by
      unfold heatK; fun_prop
    exact h1.mul (h2.mul h3)
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := volume) hFmeas
  -- the pointwise bound in `t`
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖t ^ (-(3 : ℝ) / 2) * heatImage ℓ g m t‖ₑ
        ≤ ∫⁻ u : E3,
            ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (‖aliasKernel g u‖ * heatK t (z - u))) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hhi : heatImage ℓ g m t
        = ∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u) := by
      simp only [heatImage, if_neg hm]
    have hsplit : t ^ (-(3 : ℝ) / 2) *
          (∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u))
        = ∫ u : E3, t ^ (-(3 : ℝ) / 2) *
            (aliasKernel g u * heatK t (ℓ • latVec m - u)) := by
      simpa only [smul_eq_mul] using
        (integral_const_mul (μ := volume) (t ^ (-(3 : ℝ) / 2))
          (fun u : E3 => aliasKernel g u * heatK t (ℓ • latVec m - u))).symm
    rw [hhi, hsplit]
    calc ‖∫ u : E3, t ^ (-(3 : ℝ) / 2) *
            (aliasKernel g u * heatK t (ℓ • latVec m - u))‖ₑ
        ≤ ∫⁻ u : E3,
            ‖t ^ (-(3 : ℝ) / 2) *
              (aliasKernel g u * heatK t (ℓ • latVec m - u))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ u : E3,
            ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (‖aliasKernel g u‖ * heatK t (z - u))) := by
          refine lintegral_congr (fun u => ?_)
          rw [hz, Real.enorm_eq_ofReal_abs, abs_mul, abs_mul,
            abs_of_nonneg (Real.rpow_nonneg ht0.le _),
            abs_of_nonneg (heatK_nonneg ht0.le _), Real.norm_eq_abs]
  -- the pointwise bound in `u`
  have himgWmeas : Measurable (fun u : E3 => imgW ℓ m u) := by
    have hfun : (fun u : E3 => imgW ℓ m u) = fun u : E3 => (‖u - ℓ • latVec m‖ ^ 4)⁻¹ :=
      funext (fun u => imgW_ne_zero hm u)
    rw [hfun]
    exact ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 4).measurable.inv
  have hmeasC : Measurable (fun u : E3 =>
      ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) :=
    ENNReal.measurable_ofReal.comp ((halias.measurable.norm).mul himgWmeas)
  have hperu : ∀ u : E3, (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (‖aliasKernel g u‖ * heatK t (z - u))))
      ≤ ENNReal.ofReal (2 / Real.pi ^ ((3 : ℝ) / 2)
          * (‖aliasKernel g u‖ * imgW ℓ m u)) := by
    intro u
    by_cases hzu : z - u = 0
    · have huz : u = z := (sub_eq_zero.mp hzu).symm
      have hkeru : ‖aliasKernel g u‖ = 0 := by rw [huz, hker, norm_zero]
      have hz0 : (fun t : ℝ => ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) *
          (‖aliasKernel g u‖ * heatK t (z - u)))) = fun _ => 0 := by
        funext t
        rw [hkeru, zero_mul, mul_zero]
        simp
      rw [hz0]
      simp
    · have hkey := SqrtKin.heatK_t_rpow_lintegral hzu (c := ‖aliasKernel g u‖) (norm_nonneg _)
      have hconv : (∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (‖aliasKernel g u‖ * heatK t (z - u))))
          = ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-(3 : ℝ) / 2)
              * (heatK t (z - u) * ‖aliasKernel g u‖)) := by
        refine lintegral_congr (fun t => ?_)
        rw [mul_comm (‖aliasKernel g u‖) (heatK t (z - u))]
      rw [hconv, hkey]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      have harith : ‖z - u‖ ^ (-(4 : ℝ)) = imgW ℓ m u := by
        rw [hts_imgW_eq_rpow hm, ← hz, norm_sub_rev]
      rw [harith]
      ring
  -- assembling
  calc (∫⁻ t in Set.Ioi (0 : ℝ), ‖t ^ (-(3 : ℝ) / 2) * heatImage ℓ g m t‖ₑ)
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ u : E3,
          ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (‖aliasKernel g u‖ * heatK t (z - u))) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact hpt t ht
    _ = ∫⁻ u : E3, ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (‖aliasKernel g u‖ * heatK t (z - u))) := hswap
    _ ≤ ∫⁻ u : E3, ENNReal.ofReal (2 / Real.pi ^ ((3 : ℝ) / 2)
          * (‖aliasKernel g u‖ * imgW ℓ m u)) := lintegral_mono hperu
    _ = ENNReal.ofReal (2 / Real.pi ^ ((3 : ℝ) / 2))
          * ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) := by
        rw [lintegral_congr (fun u => ENNReal.ofReal_mul hc0)]
        exact lintegral_const_mul _ hmeasC

/-! ## The target -/

theorem heatImage_tsum_conds {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) (hsumm : (∑' m : Fin 3 → ℤ, ∫⁻ u : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (‖Work.BoseBoxFock.aliasKernel g u‖ * Work.BoseBoxFock.imgW ℓ m u)) ≠ ⊤) : (∀ m : Fin 3 → ℤ, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * Work.BoseBoxFock.heatImage ℓ g m t) (MeasureTheory.volume.restrict (Set.Ioi 0))) ∧ (∑' m : Fin 3 → ℤ, ∫⁻ t in Set.Ioi (0 : ℝ), ‖t ^ (-(3 / 2 : ℝ)) * Work.BoseBoxFock.heatImage ℓ g m t‖ₑ) ≠ ⊤ := by
  have hgc : HasCompactSupport g := hts_hasCompactSupport hgsupp
  have halias : Continuous (aliasKernel g) :=
    Complex.continuous_re.comp (autocorr_continuous hg hgc)
  have hexp : (-(3 / 2 : ℝ)) = (-(3 : ℝ) / 2) := by norm_num
  refine ⟨?_, ?_⟩
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [heatImage_zero, mul_zero]
      exact aestronglyMeasurable_const
    · have hjoint : StronglyMeasurable (Function.uncurry (fun t : ℝ => fun u : E3 =>
          aliasKernel g u * heatK t (ℓ • latVec m - u))) := by
        have h1 : Measurable (fun p : ℝ × E3 =>
            aliasKernel g p.2 * heatK p.1 (ℓ • latVec m - p.2)) := by
          refine (halias.measurable.comp measurable_snd).mul ?_
          unfold heatK; fun_prop
        exact h1.stronglyMeasurable
      have hmeas0 : AEStronglyMeasurable
          (fun t : ℝ => ∫ u : E3, aliasKernel g u * heatK t (ℓ • latVec m - u))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        (MeasureTheory.StronglyMeasurable.integral_prod_right (ν := volume)
          (f := fun t (u : E3) => aliasKernel g u * heatK t (ℓ • latVec m - u))
          hjoint).aestronglyMeasurable
      have h1 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(3 / 2 : ℝ)))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        (show Measurable (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) by fun_prop).aestronglyMeasurable
      refine (h1.mul hmeas0).congr (Filter.Eventually.of_forall (fun t => ?_))
      simp only [Pi.mul_apply, heatImage, if_neg hm]
  · have hconv : ∀ m : Fin 3 → ℤ,
        (∫⁻ t in Set.Ioi (0 : ℝ), ‖t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t‖ₑ)
          = ∫⁻ t in Set.Ioi (0 : ℝ), ‖t ^ (-(3 : ℝ) / 2) * heatImage ℓ g m t‖ₑ := by
      intro m
      refine lintegral_congr (fun t => ?_)
      rw [hexp]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.ofReal_ne_top (r := 2 / Real.pi ^ ((3 : ℝ) / 2))) hsumm) ?_
    calc (∑' m : Fin 3 → ℤ, ∫⁻ t in Set.Ioi (0 : ℝ),
            ‖t ^ (-(3 / 2 : ℝ)) * heatImage ℓ g m t‖ₑ)
        = ∑' m : Fin 3 → ℤ, ∫⁻ t in Set.Ioi (0 : ℝ),
            ‖t ^ (-(3 : ℝ) / 2) * heatImage ℓ g m t‖ₑ :=
          tsum_congr (fun m => hconv m)
      _ ≤ ∑' m : Fin 3 → ℤ, ENNReal.ofReal (2 / Real.pi ^ ((3 : ℝ) / 2))
            * ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) :=
          ENNReal.tsum_le_tsum (fun m => heatImage_setLIntegral_enorm_le hℓ hg hgsupp m)
      _ = ENNReal.ofReal (2 / Real.pi ^ ((3 : ℝ) / 2))
            * ∑' m : Fin 3 → ℤ, ∫⁻ u : E3,
                ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) :=
          ENNReal.tsum_mul_left

end Work.BoseBoxFock
