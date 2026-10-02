/-
`L²`-continuity of the mollification of an `L²` function, uniformly over normalised bump kernels.

`Work.MRMT.QC.existsBumpIntegralMollSubLe` states that for `h ∈ L²(ℂ)` and every `ε > 0` there is
`δ > 0` such that every bump function `φ` at `0` with `φ.rOut ≤ δ` satisfies
`ρ_φ ⋆ h - h ∈ L²(ℂ)` and `∫ ‖ρ_φ ⋆ h - h‖² ≤ ε`, where `ρ_φ = φ.normed volume` and `⋆` is the
mollification `Work.MRMT.Weyl.moll`.

The two ingredients are:

* `lintegral_ofReal_norm_sq_moll_sub_le` — the Jensen/Cauchy–Schwarz bound
  `∫⁻ ‖ρ ⋆ f - f‖² ≤ ∫⁻ y, ρ y · ∫⁻ z, ‖f (z - y) - f z‖²` for a normalised nonnegative kernel `ρ`
  with compact support, followed by Tonelli's theorem;
* `exists_delta_lintegral_ofReal_norm_sub_translate_le` — continuity of translation in `L²(ℂ)`,
  in `lintegral` form (from `Work.MRMT.Sobolev.tendsto_eLpNorm_sub_translate`).
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.moll_L1_aux
import Submission.Work.MRMT.QC.lintegral_ofReal_norm_sq_moll_le
import Submission.Work.MRMT.Sobolev.mollification_pairing_tendsto

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

noncomputable section

/-- `ofReal` of the square of a norm is the square of the extended norm. -/
theorem ofReal_norm_sq_eq_enorm_sq (a : ℂ) :
    ENNReal.ofReal (‖a‖ ^ 2) = ‖a‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg a) 2, enorm_eq_ofReal_norm]

/-- The `ℒ²`-seminorm, computed as the square root of the integral of `ofReal ‖·‖²`. -/
theorem eLpNorm_two_eq_lintegral_ofReal (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume) :
    MeasureTheory.eLpNorm f 2 volume = (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2)) ^ (1 / 2 : ℝ) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) hf]
  rw [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [ENNReal.rpow_ofNat]
  exact (ofReal_norm_sq_eq_enorm_sq _).symm

/-- `(A ^ (1/2)) ^ 2 = A` in `ℝ≥0∞`. -/
theorem rpow_half_sq (A : ℝ≥0∞) : (A ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = A := by
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- **Jensen/Cauchy–Schwarz bound for the mollification defect.**  For a normalised nonnegative
kernel `ρ` with compact support and a locally integrable `f`,
`∫⁻ ‖ρ ⋆ f - f‖² ≤ ∫⁻ y, ρ y · ∫⁻ z, ‖f (z - y) - f z‖²`.

The pointwise estimate is Cauchy–Schwarz applied to the weighted average
`ρ ⋆ f z - f z = ∫ y, ρ y • (f (z - y) - f z)`; the two iterated integrals are then swapped by
Tonelli's theorem. -/
theorem lintegral_ofReal_norm_sq_moll_sub_le {f : ℂ → ℂ} {ρ : ℂ → ℝ}
    (hf : LocallyIntegrable f volume) (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ)
    (hρnn : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z - f z‖ ^ 2) ≤
      ∫⁻ y, ENNReal.ofReal (ρ y) * ∫⁻ z, ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2) := by
  have hfam : AEMeasurable f volume := hf.aestronglyMeasurable.aemeasurable
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρcs
  set G : ℂ → ℝ≥0∞ := fun y => ENNReal.ofReal (ρ y) with hGdef
  have hGm : AEMeasurable G volume := hρc.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hGlin : ∫⁻ y, G y = 1 := by
    rw [hGdef]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hρint
      (Filter.Eventually.of_forall hρnn), hρ1]
    simp
  -- Pointwise (in `z`) Cauchy–Schwarz bound.
  have hpt : ∀ z : ℂ, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z - f z‖ ^ 2) ≤
      ∫⁻ y, G y * ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2) := by
    intro z
    have hHm : AEMeasurable (fun y : ℂ => ‖f (z - y) - f z‖ₑ) volume :=
      (((hfam.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_left_of_right_invariant volume z)).sub
        aemeasurable_const).enorm)
    have h1 : ‖Work.MRMT.Weyl.moll ρ f z - f z‖ₑ
        ≤ ∫⁻ y, G y * ‖f (z - y) - f z‖ₑ := by
      rw [Work.MRMT.Weyl.moll_sub_integral hf hρc hρcs hρ1 z]
      refine (enorm_integral_le_lintegral_enorm (μ := volume)
        (fun y : ℂ => ((ρ y : ℝ) : ℂ) * (f (z - y) - f z))).trans_eq ?_
      refine lintegral_congr fun y => ?_
      rw [enorm_mul]
      congr 1
      simp only [hGdef]
      rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← enorm_eq_nnnorm]
      exact Real.enorm_eq_ofReal (hρnn y)
    have hCS := lintegral_mul_sq_le (μ := volume) (G := G)
      (H := fun y : ℂ => ‖f (z - y) - f z‖ₑ) hGm hHm
    rw [ofReal_norm_sq_eq_enorm_sq]
    calc ‖Work.MRMT.Weyl.moll ρ f z - f z‖ₑ ^ 2
        ≤ (∫⁻ y, G y * ‖f (z - y) - f z‖ₑ) ^ 2 := pow_le_pow_left' h1 2
      _ ≤ (∫⁻ y, G y) * ∫⁻ y, G y * ‖f (z - y) - f z‖ₑ ^ 2 := hCS
      _ = ∫⁻ y, G y * ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2) := by
          rw [hGlin, one_mul]
          refine lintegral_congr fun y => ?_
          rw [ofReal_norm_sq_eq_enorm_sq]
  -- Tonelli: swap the two `lintegral`s.
  have hmeas : AEMeasurable (Function.uncurry fun z y : ℂ =>
      G y * ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2)) (volume.prod volume) := by
    have h2 : AEMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2) - f p.1) (volume.prod volume) :=
      (hfam.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)).sub hfam.comp_fst
    have h3 : AEMeasurable (fun p : ℂ × ℂ => ‖f (p.1 - p.2) - f p.1‖ ^ 2)
        (volume.prod volume) := h2.norm.pow aemeasurable_const
    exact (hGm.comp_snd).mul h3.ennreal_ofReal
  calc ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z - f z‖ ^ 2)
      ≤ ∫⁻ z, ∫⁻ y, G y * ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2) := lintegral_mono hpt
    _ = ∫⁻ y, ∫⁻ z, G y * ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2) :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ y, G y * ∫⁻ z, ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2) := by
        refine lintegral_congr fun y => ?_
        rw [hGdef]
        exact lintegral_const_mul' (ENNReal.ofReal (ρ y))
          (fun z => ENNReal.ofReal (‖f (z - y) - f z‖ ^ 2)) ENNReal.ofReal_lt_top.ne

/-- **Continuity of translation in `L²(ℂ)`, `lintegral` form.**  For `h ∈ L²(ℂ)` and `ε > 0` there
is `δ > 0` such that `∫⁻ z, ‖h (z - t) - h z‖² ≤ ε` whenever `‖t‖ < δ`. -/
theorem exists_delta_lintegral_ofReal_norm_sub_translate_le {h : ℂ → ℂ}
    (hh : MeasureTheory.MemLp h 2 MeasureTheory.volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℂ, ‖t‖ < δ →
      ∫⁻ z, ENNReal.ofReal (‖h (z - t) - h z‖ ^ 2) ≤ ENNReal.ofReal ε := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ),
      eLpNorm (fun z => h (z - t) - h z) 2 volume ≤ ENNReal.ofReal (Real.sqrt ε) :=
    (ENNReal.tendsto_nhds_zero.mp (Work.MRMT.Sobolev.tendsto_eLpNorm_sub_translate hh))
      _ (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hε))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ, hδpos, fun t ht => ?_⟩
  have ht' : t ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact ht
  have haesm : AEStronglyMeasurable (fun z : ℂ => h (z - t) - h z) volume :=
    (hh.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_sub_right volume t)).sub hh.aestronglyMeasurable
  have h3 : (∫⁻ z, ENNReal.ofReal (‖h (z - t) - h z‖ ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt ε) := by
    rw [← eLpNorm_two_eq_lintegral_ofReal (fun z : ℂ => h (z - t) - h z) haesm]
    exact hδ ht'
  calc ∫⁻ z, ENNReal.ofReal (‖h (z - t) - h z‖ ^ 2)
      = ((∫⁻ z, ENNReal.ofReal (‖h (z - t) - h z‖ ^ 2)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        (rpow_half_sq _).symm
    _ ≤ (ENNReal.ofReal (Real.sqrt ε)) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg ε) (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_two, Real.sq_sqrt hε.le]

theorem existsBumpIntegralMollSubLe {h : ℂ → ℂ} (hh : MeasureTheory.MemLp h 2 MeasureTheory.volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℂ), φ.rOut ≤ δ →
      MeasureTheory.MemLp
        (fun z => Work.MRMT.Weyl.moll (φ.normed MeasureTheory.volume) h z - h z) 2
        MeasureTheory.volume ∧
      ∫ z, ‖Work.MRMT.Weyl.moll (φ.normed MeasureTheory.volume) h z - h z‖ ^ 2 ≤ ε := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_lintegral_ofReal_norm_sub_translate_le hh hε
  refine ⟨δ, hδpos, fun φ hφ => ?_⟩
  have hli : LocallyIntegrable h volume := hh.locallyIntegrable (by norm_num)
  have hρc : Continuous (φ.normed volume) := φ.continuous_normed
  have hρcs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hρnn : ∀ x : ℂ, 0 ≤ φ.normed volume x := fun x => φ.nonneg_normed x
  have hρ1 : ∫ x, φ.normed volume x = 1 := φ.integral_normed
  -- The `lintegral` bound.
  have hint : ∫⁻ y, ENNReal.ofReal (φ.normed volume y) *
        (∫⁻ z, ENNReal.ofReal (‖h (z - y) - h z‖ ^ 2)) ≤ ENNReal.ofReal ε := by
    have hstep : ∀ y : ℂ, ENNReal.ofReal (φ.normed volume y) *
          (∫⁻ z, ENNReal.ofReal (‖h (z - y) - h z‖ ^ 2))
        ≤ ENNReal.ofReal (φ.normed volume y) * ENNReal.ofReal ε := by
      intro y
      by_cases hy : φ.normed volume y = 0
      · rw [hy]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hyball : y ∈ Metric.ball (0 : ℂ) φ.rOut := by
          rw [← φ.support_normed_eq (μ := volume)]
          exact Function.mem_support.mpr hy
        have hylt : ‖y‖ < φ.rOut := by
          simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hyball
        exact hδ y (lt_of_lt_of_le hylt hφ)
    calc ∫⁻ y, ENNReal.ofReal (φ.normed volume y) *
          (∫⁻ z, ENNReal.ofReal (‖h (z - y) - h z‖ ^ 2))
        ≤ ∫⁻ y, ENNReal.ofReal (φ.normed volume y) * ENNReal.ofReal ε :=
          lintegral_mono hstep
      _ = ENNReal.ofReal ε := by
          rw [lintegral_mul_const' (ENNReal.ofReal ε)
            (fun y => ENNReal.ofReal (φ.normed volume y)) ENNReal.ofReal_lt_top.ne,
            ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
              (Filter.Eventually.of_forall fun y => φ.nonneg_normed y),
            hρ1]
          simp
  have hmain : ∫⁻ z, ENNReal.ofReal
      (‖Work.MRMT.Weyl.moll (φ.normed volume) h z - h z‖ ^ 2) ≤ ENNReal.ofReal ε :=
    (lintegral_ofReal_norm_sq_moll_sub_le hli hρc hρcs hρnn hρ1).trans hint
  -- `L²`-membership.
  have hmollcont : Continuous (Work.MRMT.Weyl.moll (φ.normed volume) h) :=
    hρcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc hli
  have haesm : AEStronglyMeasurable
      (fun z => Work.MRMT.Weyl.moll (φ.normed volume) h z - h z) volume :=
    hmollcont.aestronglyMeasurable.sub hh.aestronglyMeasurable
  have heLp : eLpNorm (fun z => Work.MRMT.Weyl.moll (φ.normed volume) h z - h z) 2 volume
      ≤ ENNReal.ofReal (Real.sqrt ε) := by
    rw [eLpNorm_two_eq_lintegral_ofReal (fun z => Work.MRMT.Weyl.moll (φ.normed volume) h z - h z)
      haesm]
    calc (∫⁻ z, ENNReal.ofReal
            (‖Work.MRMT.Weyl.moll (φ.normed volume) h z - h z‖ ^ 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal ε) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hmain (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt ε) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 1 / 2),
            Real.sqrt_eq_rpow]
  have hmem : MeasureTheory.MemLp
      (fun z => Work.MRMT.Weyl.moll (φ.normed volume) h z - h z) 2 MeasureTheory.volume :=
    MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt heLp ENNReal.ofReal_lt_top)
  refine ⟨hmem, ?_⟩
  have hInt : Integrable
      (fun z => ‖Work.MRMT.Weyl.moll (φ.normed volume) h z - h z‖ ^ 2) volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm haesm).mp hmem
  have hof : ENNReal.ofReal (∫ z, ‖Work.MRMT.Weyl.moll (φ.normed volume) h z - h z‖ ^ 2)
      = ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll (φ.normed volume) h z - h z‖ ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun z => sq_nonneg _)
  rw [← hof] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hmain

end

end Work.MRMT.QC
