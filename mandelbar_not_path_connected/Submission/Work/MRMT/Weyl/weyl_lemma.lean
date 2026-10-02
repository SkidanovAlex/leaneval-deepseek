/-
Weyl's lemma (a.e. form): a locally integrable function whose weak `∂̄`-derivative vanishes
almost everywhere agrees almost everywhere with an entire function.

Route: mollify `f` against a sequence of bump functions with outer radii tending to `0`; each
mollification is entire (`isDbarDeriv_moll` + the continuous Weyl lemma).  The limit is identified
with the *ball average* of `f` of radius `1`, using the mean value property of the entire
mollifications and the `L¹_loc` convergence of mollifications.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll
import Submission.Work.MRMT.Weyl.integral_ball_eq_mul_of_differentiable
import Submission.Work.MRMT.Weyl.weyl_lemma_continuous
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

noncomputable section

open Work.MRMT

/-- The `n`-th bump kernel is smooth with compact support. -/
theorem bump_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) ((bump n).normed volume) :=
  (bump n).contDiff_normed (μ := volume) (n := ⊤)

theorem bump_hasCompactSupport (n : ℕ) : HasCompactSupport ((bump n).normed volume) :=
  (bump n).hasCompactSupport_normed

/-- The outer radius of the `n`-th bump is at most `1`. -/
theorem bump_rOut_le_one (n : ℕ) : (bump n).rOut ≤ 1 := by
  rw [show (bump n).rOut = 1 / ((n : ℝ) + 1) from rfl]
  have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  exact div_le_one_of_le₀ (a := (1 : ℝ)) (b := (n : ℝ) + 1) hx h0.le

/-- **`L¹`-convergence of the bump mollifications on a compact set.**  For `f` locally integrable and
`K` compact, `∫_K ‖moll ((bump n).normed volume) f - f‖ → 0`.

Proof: write `f = g + (f - g)` with `g` bounded continuous and `∫_{K₂} ‖f - g‖ ≤ ε/4` on the
slightly larger compact set `K₂ = cthickening 1 K` (Mathlib's density
`Integrable.exists_boundedContinuous_integral_sub_le`).  Then
* `∫_K ‖moll ρ_n f - moll ρ_n g‖ ≤ ∫_K (ρ_n ⋆ W)` where `W = 1_{K₂} ‖f - g‖` (the kernels have
  support in the unit ball, so `K` is dragged into `K₂`), and
  `∫ (ρ_n ⋆ W) = (∫ ρ_n) (∫ W) = ∫ W ≤ ε/4` by `MeasureTheory.integral_convolution`;
* `∫_K ‖moll ρ_n g - g‖ ≤ ε/4` for `n` large (uniform convergence on `K`,
  `tendstoUniformlyOn_moll`);
* `∫_K ‖g - f‖ ≤ ∫_{K₂} ‖f - g‖ ≤ ε/4`. -/
theorem moll_bump_tendsto_L1 {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) {K : Set ℂ}
    (hK : IsCompact K) :
    Tendsto (fun n : ℕ => ∫ z in K, ‖moll ((bump n).normed volume) f z - f z‖) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  set K₂ : Set ℂ := Metric.cthickening 1 K with hK₂def
  have hK₂c : IsCompact K₂ := hK.cthickening
  have hKK₂ : K ⊆ K₂ := fun z hz => Metric.self_subset_cthickening K hz
  -- a bounded continuous approximation of `f` on `K₂`
  have hFint : Integrable (K₂.indicator f) volume := by
    rw [integrable_indicator_iff hK₂c.measurableSet]
    exact hf.integrableOn_isCompact hK₂c
  obtain ⟨G, hG, hGint⟩ := hFint.exists_boundedContinuous_integral_sub_le hε4
  set g : ℂ → ℂ := ⇑G with hgdef
  have hgcont : Continuous g := G.continuous
  have hgint : Integrable g volume := hGint
  have hfin : ∀ s : Set ℂ, IsCompact s → IntegrableOn (fun z => ‖f z - g z‖) s volume := fun s hs =>
    ((hf.integrableOn_isCompact hs).sub (hgint.locallyIntegrable.integrableOn_isCompact hs)).norm
  have hgin : ∀ s : Set ℂ, IsCompact s → IntegrableOn (fun z => ‖g z - f z‖) s volume := fun s hs =>
    ((hgint.locallyIntegrable.integrableOn_isCompact hs).sub (hf.integrableOn_isCompact hs)).norm
  have hfg2 : ∫ z in K₂, ‖f z - g z‖ ≤ ε / 4 := by
    have h1 : ∫ z in K₂, ‖f z - g z‖ = ∫ z, K₂.indicator (fun z => ‖f z - g z‖) z :=
      (integral_indicator hK₂c.measurableSet).symm
    rw [h1]
    refine le_trans (integral_mono_ae ?_ ?_ (Eventually.of_forall ?_)) hG
    · exact (integrable_indicator_iff hK₂c.measurableSet).2 (hfin K₂ hK₂c)
    · exact (hFint.sub hgint).norm
    · intro z
      by_cases hz : z ∈ K₂
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        exact norm_nonneg _
  -- the weight `W = 1_{K₂} ‖f - g‖`
  set W : ℂ → ℝ := K₂.indicator (fun w => ‖f w - g w‖) with hWdef
  have hWint : Integrable W volume := by
    rw [hWdef]
    exact (integrable_indicator_iff hK₂c.measurableSet).2 (hfin K₂ hK₂c)
  have hWnn : ∀ w, 0 ≤ W w := by
    intro w
    rw [hWdef]
    by_cases hw : w ∈ K₂
    · rw [Set.indicator_of_mem hw]; exact norm_nonneg _
    · rw [Set.indicator_of_notMem hw]
  have hWint' : ∫ w, W w ≤ ε / 4 := by
    rw [hWdef, integral_indicator hK₂c.measurableSet]
    exact hfg2
  -- the support of the kernels stays in the unit ball
  have hsupp : ∀ (n : ℕ) (t : ℂ), ((bump n).normed volume) t ≠ 0 → dist t 0 < 1 := by
    intro n t ht
    have hmem : t ∈ Function.support ((bump n).normed volume) := Function.mem_support.mpr ht
    rw [ContDiffBump.support_normed_eq (f := bump n) (μ := (volume : Measure ℂ)),
      Metric.mem_ball] at hmem
    have := bump_rOut_le_one n
    linarith
  -- the first piece: `moll ρ_n f - moll ρ_n g` is controlled by the convolution with `W`
  have hA : ∀ n : ℕ, ∫ z in K, ‖moll ((bump n).normed volume) f z
      - moll ((bump n).normed volume) g z‖ ≤ ε / 4 := by
    intro n
    have hρncont : Continuous ((bump n).normed volume) :=
      ContDiffBump.continuous_normed (f := bump n) (μ := volume)
    have hρncs : HasCompactSupport ((bump n).normed volume) := bump_hasCompactSupport n
    have hρnint : Integrable ((bump n).normed volume) volume :=
      hρncont.integrable_of_hasCompactSupport hρncs
    have hρn1 : ∫ t, ((bump n).normed volume) t = 1 :=
      ContDiffBump.integral_normed (f := bump n) (μ := volume)
    have hρnnn : ∀ t, 0 ≤ ((bump n).normed volume) t := fun t =>
      ContDiffBump.nonneg_normed (bump n) (μ := volume) t
    have hmollf_cont : Continuous (moll ((bump n).normed volume) f) :=
      (contDiff_moll (N := (⊤ : ℕ∞)) (bump_contDiff n) (bump_hasCompactSupport n) hf).continuous
    have hmollg_cont : Continuous (moll ((bump n).normed volume) g) :=
      (contDiff_moll (N := (⊤ : ℕ∞)) (bump_contDiff n) (bump_hasCompactSupport n)
        hgint.locallyIntegrable).continuous
    have hconv_int : Integrable
        (MeasureTheory.convolution ((bump n).normed volume) W (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        volume :=
      MeasureTheory.Integrable.integrable_convolution
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hρnint hWint
    have hconv_nn : 0 ≤ᵐ[(volume : Measure ℂ)]
        (MeasureTheory.convolution ((bump n).normed volume) W (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
      Eventually.of_forall fun z => by
        rw [MeasureTheory.convolution_def]
        exact integral_nonneg fun t => mul_nonneg (hρnnn t) (hWnn (z - t))
    have hpt : ∀ z ∈ K, ‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖
        ≤ MeasureTheory.convolution ((bump n).normed volume) W (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
      intro z hz
      have h1 : Integrable (fun t => (((bump n).normed volume) t : ℂ) * f (z - t)) volume :=
        (hρncs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρncont hf z).integrable
      have h2 : Integrable (fun t => (((bump n).normed volume) t : ℂ) * g (z - t)) volume :=
        (hρncs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρncont
          hgint.locallyIntegrable z).integrable
      have hlin : moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z
          = ∫ t, (((bump n).normed volume) t : ℂ) * (f (z - t) - g (z - t)) := by
        rw [moll_apply, moll_apply, ← integral_sub h1 h2]
        exact integral_congr_ae (Eventually.of_forall fun t => by ring_nf)
      rw [hlin]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [MeasureTheory.convolution_def]
      refine integral_mono_ae ?_ ?_ (Eventually.of_forall fun t => ?_)
      · exact (((hρncs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
          hρncont (hf.sub hgint.locallyIntegrable) z).integrable).norm)
      · exact ((hρncs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
          hρncont hWint.locallyIntegrable z).integrable)
      · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρnnn t)]
        by_cases ht : ((bump n).normed volume) t = 0
        · rw [ht, zero_mul, zero_mul]
        · have hmem : z - t ∈ K₂ := by
            refine Metric.mem_cthickening_of_dist_le (z - t) z 1 K hz ?_
            have h1 : dist (z - t) z = dist t 0 := by
              simp only [dist_eq_norm, show (z - t) - z = -t by ring,
                show t - (0 : ℂ) = t by ring, norm_neg]
            rw [h1]
            exact (hsupp n t ht).le
          rw [hWdef, Set.indicator_of_mem hmem]
    have step1 : ∫ z in K, ‖moll ((bump n).normed volume) f z
        - moll ((bump n).normed volume) g z‖
        ≤ ∫ z in K, MeasureTheory.convolution ((bump n).normed volume) W
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
      have hptae : ∀ᵐ z ∂(volume.restrict K), ‖moll ((bump n).normed volume) f z
          - moll ((bump n).normed volume) g z‖
          ≤ MeasureTheory.convolution ((bump n).normed volume) W
              (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
        rw [ae_restrict_iff' hK.measurableSet]
        exact Eventually.of_forall hpt
      exact integral_mono_ae ((hmollf_cont.sub hmollg_cont).continuousOn.integrableOn_compact hK).norm
        hconv_int.integrableOn hptae
    have step2 : ∫ z in K, MeasureTheory.convolution ((bump n).normed volume) W
          (ContinuousLinearMap.lsmul ℝ ℝ) volume z
        ≤ ∫ z, MeasureTheory.convolution ((bump n).normed volume) W
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      setIntegral_le_integral hconv_int hconv_nn
    have step3 : ∫ z, MeasureTheory.convolution ((bump n).normed volume) W
          (ContinuousLinearMap.lsmul ℝ ℝ) volume z
        = (ContinuousLinearMap.lsmul ℝ ℝ) (∫ y, ((bump n).normed volume) y) (∫ w, W w) :=
      MeasureTheory.integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hρnint hWint
    calc ∫ z in K, ‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖
        ≤ ∫ z in K, MeasureTheory.convolution ((bump n).normed volume) W
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z := step1
      _ ≤ ∫ z, MeasureTheory.convolution ((bump n).normed volume) W
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z := step2
      _ = (ContinuousLinearMap.lsmul ℝ ℝ) (∫ y, ((bump n).normed volume) y) (∫ w, W w) := step3
      _ = ∫ w, W w := by rw [hρn1]; simp
      _ ≤ ε / 4 := hWint'
  -- the second piece: uniform convergence of the mollifications of the continuous `g`
  have hB : ∃ N : ℕ, ∀ n ≥ N, ∫ z in K, ‖moll ((bump n).normed volume) g z - g z‖ ≤ ε / 4 := by
    have hunif := tendstoUniformlyOn_moll hgcont isOpen_univ hK (Set.subset_univ K)
      bump tendsto_rOut_bump
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    have hKfin : (volume : Measure ℂ) K < ⊤ := hK.measure_lt_top
    obtain ⟨D, hD0, hDK⟩ : ∃ D : ℝ, 0 ≤ D ∧ (volume K).toReal ≤ D :=
      ⟨max (volume K).toReal 0, le_max_right _ _, le_max_left _ _⟩
    have hD1 : (0 : ℝ) < D + 1 := by linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hunif (ε / (4 * (D + 1))) (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    have h1 : ∫ z in K, ‖moll ((bump n).normed volume) g z - g z‖
        ≤ (ε / (4 * (D + 1))) * (volume K).toReal := by
      have h2 := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (f := fun z => ‖moll ((bump n).normed volume) g z - g z‖) hKfin
        (C := ε / (4 * (D + 1))) ?_
      · rwa [Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg _)] at h2
      · intro z hz
        have h3 := hN n hn z hz
        rw [dist_eq_norm, norm_sub_rev] at h3
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact h3.le
    calc ∫ z in K, ‖moll ((bump n).normed volume) g z - g z‖
        ≤ (ε / (4 * (D + 1))) * (volume K).toReal := h1
      _ ≤ (ε / (4 * (D + 1))) * D := mul_le_mul_of_nonneg_left hDK (by positivity)
      _ ≤ ε / 4 := by
          have h4 : (ε / (4 * (D + 1))) * D ≤ (ε / (4 * (D + 1))) * (D + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h5 : (ε / (4 * (D + 1))) * (D + 1) = ε / 4 := by
            field_simp
          linarith [h4, h5.le, h5.ge]
  -- the third piece
  have hC : ∫ z in K, ‖g z - f z‖ ≤ ε / 4 := by
    have h1 : ∫ z in K₂, ‖g z - f z‖ = ∫ z in K₂, ‖f z - g z‖ :=
      integral_congr_ae (Eventually.of_forall fun z => norm_sub_rev _ _)
    calc ∫ z in K, ‖g z - f z‖ ≤ ∫ z in K₂, ‖g z - f z‖ :=
          setIntegral_mono_set (hgin K₂ hK₂c)
            (Eventually.of_forall fun z => norm_nonneg _) (Eventually.of_forall hKK₂)
      _ = ∫ z in K₂, ‖f z - g z‖ := h1
      _ ≤ ε / 4 := hfg2
  obtain ⟨N, hN⟩ := hB
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
  have hm1 : Continuous (moll ((bump n).normed volume) f) :=
    (contDiff_moll (N := (⊤ : ℕ∞)) (bump_contDiff n) (bump_hasCompactSupport n) hf).continuous
  have hm2 : Continuous (moll ((bump n).normed volume) g) :=
    (contDiff_moll (N := (⊤ : ℕ∞)) (bump_contDiff n) (bump_hasCompactSupport n)
      hgint.locallyIntegrable).continuous
  have i1 : IntegrableOn (fun z => ‖moll ((bump n).normed volume) f z
      - moll ((bump n).normed volume) g z‖) K volume :=
    ((hm1.sub hm2).continuousOn.integrableOn_compact hK).norm
  have i2 : IntegrableOn (fun z => ‖moll ((bump n).normed volume) g z - g z‖) K volume :=
    ((hm2.sub hgcont).continuousOn.integrableOn_compact hK).norm
  have i3 : IntegrableOn (fun z => ‖g z - f z‖) K volume :=
    ((hgcont.continuousOn.integrableOn_compact hK).sub (hf.integrableOn_isCompact hK)).norm
  have i4 : IntegrableOn (fun z => ‖moll ((bump n).normed volume) f z - f z‖) K volume :=
    ((hm1.continuousOn.integrableOn_compact hK).sub (hf.integrableOn_isCompact hK)).norm
  have htri : ∫ z in K, ‖moll ((bump n).normed volume) f z - f z‖
      ≤ ∫ z in K, (‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖
          + (‖moll ((bump n).normed volume) g z - g z‖ + ‖g z - f z‖)) := by
    refine integral_mono_ae i4 (i1.add (i2.add i3)) (Eventually.of_forall fun z => ?_)
    calc ‖moll ((bump n).normed volume) f z - f z‖
        = ‖(moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z)
            + ((moll ((bump n).normed volume) g z - g z) + (g z - f z))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (norm_add_le _ _)
  have htri2 : ∫ z in K, (‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖
        + (‖moll ((bump n).normed volume) g z - g z‖ + ‖g z - f z‖))
      = (∫ z in K, ‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖)
        + ((∫ z in K, ‖moll ((bump n).normed volume) g z - g z‖) + ∫ z in K, ‖g z - f z‖) := by
    have h1 : ∫ z in K, (‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖
          + (‖moll ((bump n).normed volume) g z - g z‖ + ‖g z - f z‖))
        = (∫ z in K, ‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖)
          + ∫ z in K, (‖moll ((bump n).normed volume) g z - g z‖ + ‖g z - f z‖) :=
      integral_add i1 (i2.add i3)
    rw [h1, integral_add i2 i3]
  calc ∫ z in K, ‖moll ((bump n).normed volume) f z - f z‖
      ≤ ∫ z in K, (‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖
          + (‖moll ((bump n).normed volume) g z - g z‖ + ‖g z - f z‖)) := htri
    _ = (∫ z in K, ‖moll ((bump n).normed volume) f z - moll ((bump n).normed volume) g z‖)
        + ((∫ z in K, ‖moll ((bump n).normed volume) g z - g z‖) + ∫ z in K, ‖g z - f z‖) := htri2
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by linarith [hA n, hN n hn, hC]
    _ < ε := by linarith

theorem weyl_lemma {f : ℂ → ℂ}
    (hf : MeasureTheory.LocallyIntegrable f (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (h : IsWeaklyConformal f) :
    ∃ F : ℂ → ℂ, AnalyticOn ℂ F Set.univ ∧
      f =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] F := by
  obtain ⟨g, hgd, hg0⟩ := h
  -- the weak `∂̄`-derivative of `f` is zero
  have hd : IsDbarDeriv f (fun _ => 0) := by
    refine ⟨hgd.1, locallyIntegrable_zero, fun ψ => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hgd.2.2 ψ
    refine ⟨h1, by simp, ?_⟩
    have hzero : ∫ z, g z * (ψ : ℂ → ℂ) z = 0 := by
      have hae : (fun z => g z * (ψ : ℂ → ℂ) z) =ᵐ[(volume : Measure ℂ)] (0 : ℂ → ℂ) := by
        filter_upwards [hg0] with z hz
        simp [hz]
      rw [integral_congr_ae hae]
      simp
    rw [h3, hzero]
    simp
  -- the mollifications are entire
  have hρ_cont : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) ((bump n).normed volume) := fun n =>
    (bump n).contDiff_normed (μ := volume) (n := ⊤)
  have hρ_cs : ∀ n : ℕ, HasCompactSupport ((bump n).normed volume) := fun n =>
    (bump n).hasCompactSupport_normed
  have hmoll_cont : ∀ n : ℕ, Continuous (moll ((bump n).normed volume) f) := fun n =>
    (contDiff_moll (N := (⊤ : ℕ∞)) (hρ_cont n) (hρ_cs n) hf).continuous
  have hAn : ∀ n : ℕ, AnalyticOn ℂ (moll ((bump n).normed volume) f) Set.univ := fun n =>
    analyticOn_of_continuous_isDbarDeriv_zero (hmoll_cont n)
      (isDbarDeriv_moll_contDiff hd (hρ_cont n) (hρ_cs n))
  have hint_moll : ∀ (n : ℕ) {s : Set ℂ}, IsCompact s →
      IntegrableOn (moll ((bump n).normed volume) f) s volume := fun n s hs =>
    ContinuousOn.integrableOn_compact hs ((hmoll_cont n).continuousOn.mono (Set.subset_univ s))
  -- the candidate: the ball average of `f` over the unit ball
  let F : ℂ → ℂ := fun z => ((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball z 1, f w
  -- mean value property of the (entire) mollifications at radius `1`
  have hmean : ∀ n z, moll ((bump n).normed volume) f z =
      ((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball z 1, moll ((bump n).normed volume) f w := by
    intro n z
    have hD : Differentiable ℂ (moll ((bump n).normed volume) f) :=
      differentiableOn_univ.mp (hAn n).differentiableOn
    have hmv := integral_ball_eq_mul_of_differentiable hD (c := z) (R := 1) one_pos
    rw [hmv, show (Real.pi * (1 : ℝ) ^ 2) = Real.pi by ring]
    rw [← mul_assoc, inv_mul_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]
  -- pointwise bound for the difference between a mollification and the ball average of `f`
  have hbound : ∀ (n : ℕ) {K : Set ℂ}, IsCompact K → ∀ z ∈ K,
      ‖moll ((bump n).normed volume) f z - F z‖ ≤
        (Real.pi)⁻¹ * ∫ w in Metric.cthickening 1 K,
            ‖moll ((bump n).normed volume) f w - f w‖ := by
    intro n K hK z hz
    have hKc : IsCompact (Metric.cthickening 1 K) := hK.cthickening
    have hi1 : IntegrableOn (moll ((bump n).normed volume) f) (Metric.ball z 1) volume :=
      (hint_moll n (isCompact_closedBall z 1)).mono_set Metric.ball_subset_closedBall
    have hi2 : IntegrableOn f (Metric.ball z 1) volume :=
      (hf.integrableOn_isCompact (isCompact_closedBall z 1)).mono_set Metric.ball_subset_closedBall
    have hsub : ∫ w in Metric.ball z 1,
          (moll ((bump n).normed volume) f w - f w)
        = (∫ w in Metric.ball z 1, moll ((bump n).normed volume) f w)
          - ∫ w in Metric.ball z 1, f w :=
      integral_sub hi1 hi2
    have hnormpi : ‖((Real.pi : ℂ))⁻¹‖ = (Real.pi)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hintbig : IntegrableOn (fun w => ‖moll ((bump n).normed volume) f w - f w‖)
        (Metric.cthickening 1 K) volume :=
      ((hint_moll n hKc).sub (hf.integrableOn_isCompact hKc)).norm
    have hmono : ∫ w in Metric.ball z 1, ‖moll ((bump n).normed volume) f w - f w‖
        ≤ ∫ w in Metric.cthickening 1 K, ‖moll ((bump n).normed volume) f w - f w‖ := by
      refine setIntegral_mono_set hintbig (Eventually.of_forall fun w => norm_nonneg _) ?_
      filter_upwards with w hw
      exact Metric.mem_cthickening_of_dist_le w z 1 K hz (le_of_lt hw)
    have hkey : moll ((bump n).normed volume) f z - F z =
        ((Real.pi : ℂ))⁻¹ * ((∫ w in Metric.ball z 1, moll ((bump n).normed volume) f w)
          - ∫ w in Metric.ball z 1, f w) := by
      rw [hmean n z]; dsimp only [F]; ring
    calc ‖moll ((bump n).normed volume) f z - F z‖
        = ‖((Real.pi : ℂ))⁻¹ * ((∫ w in Metric.ball z 1, moll ((bump n).normed volume) f w)
            - ∫ w in Metric.ball z 1, f w)‖ := by rw [hkey]
      _ = (Real.pi)⁻¹ * ‖(∫ w in Metric.ball z 1, moll ((bump n).normed volume) f w)
            - ∫ w in Metric.ball z 1, f w‖ := by
          rw [norm_mul, hnormpi]
      _ = (Real.pi)⁻¹ * ‖∫ w in Metric.ball z 1,
            (moll ((bump n).normed volume) f w - f w)‖ := by rw [hsub]
      _ ≤ (Real.pi)⁻¹ * ∫ w in Metric.ball z 1,
            ‖moll ((bump n).normed volume) f w - f w‖ := by
          refine mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
            (inv_nonneg.mpr Real.pi_pos.le)
      _ ≤ (Real.pi)⁻¹ * ∫ w in Metric.cthickening 1 K,
            ‖moll ((bump n).normed volume) f w - f w‖ := by
          refine mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr Real.pi_pos.le)
  -- locally uniform convergence of the mollifications to `F`
  have hTLU : TendstoLocallyUniformlyOn
      (fun n : ℕ => moll ((bump n).normed volume) f) F atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n => ∫ w in Metric.cthickening 1 K,
          ‖moll ((bump n).normed volume) f w - f w‖) atTop (nhds 0) :=
      moll_bump_tendsto_L1 hf hK.cthickening
    have hε' : 0 < ε * Real.pi := mul_pos hε Real.pi_pos
    filter_upwards [hlim.eventually (eventually_lt_nhds hε')] with n hn
    intro z hz
    rw [dist_comm, dist_eq_norm]
    refine (hbound n hK z hz).trans_lt ?_
    have h2 : (Real.pi)⁻¹ * (∫ w in Metric.cthickening 1 K,
          ‖moll ((bump n).normed volume) f w - f w‖) < (Real.pi)⁻¹ * (ε * Real.pi) :=
      mul_lt_mul_of_pos_left hn (inv_pos.mpr Real.pi_pos)
    have h3 : (Real.pi)⁻¹ * (ε * Real.pi) = ε := by
      rw [mul_comm ε Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
    linarith
  have hFdiff : DifferentiableOn ℂ F Set.univ :=
    hTLU.differentiableOn (Eventually.of_forall fun n => (hAn n).differentiableOn) isOpen_univ
  have hFana : AnalyticOn ℂ F Set.univ := hFdiff.analyticOn isOpen_univ
  have hFcont : Continuous F := continuousOn_univ.mp hFana.continuousOn
  have hFint : ∀ {K : Set ℂ}, IsCompact K → IntegrableOn F K volume := fun {K} hK =>
    ContinuousOn.integrableOn_compact hK (hFcont.continuousOn.mono (Set.subset_univ K))
  refine ⟨F, hFana, ?_⟩
  -- the `L¹` integral of `‖f - F‖` over any compact set vanishes
  have hFK : ∀ K : Set ℂ, IsCompact K → ∫ z in K, ‖f z - F z‖ = 0 := by
    intro K hK
    have hKc : IsCompact (Metric.cthickening 1 K) := hK.cthickening
    have hfint : IntegrableOn f K volume := hf.integrableOn_isCompact hK
    have hin1 : ∀ n : ℕ, IntegrableOn (fun z => ‖f z - moll ((bump n).normed volume) f z‖) K volume :=
      fun n => (hfint.sub (hint_moll n hK)).norm
    have hin2 : ∀ n : ℕ, IntegrableOn (fun z => ‖moll ((bump n).normed volume) f z - F z‖) K volume :=
      fun n => ((hint_moll n hK).sub (hFint hK)).norm
    have hL : IntegrableOn (fun z => ‖f z - F z‖) K volume := (hfint.sub (hFint hK)).norm
    have hle : ∀ n : ℕ, ∫ z in K, ‖f z - F z‖ ≤
        (∫ z in K, ‖f z - moll ((bump n).normed volume) f z‖)
          + ∫ z in K, ‖moll ((bump n).normed volume) f z - F z‖ := by
      intro n
      rw [← integral_add (hin1 n) (hin2 n)]
      refine integral_mono_ae hL ((hin1 n).add (hin2 n)) (Eventually.of_forall fun z => ?_)
      calc ‖f z - F z‖ = ‖(f z - moll ((bump n).normed volume) f z)
              + (moll ((bump n).normed volume) f z - F z)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have hlim1 : Tendsto (fun n => ∫ z in K, ‖f z - moll ((bump n).normed volume) f z‖)
        atTop (nhds 0) := by
      refine (moll_bump_tendsto_L1 hf hK).congr' ?_
      filter_upwards with n
      exact integral_congr_ae (Eventually.of_forall fun z => norm_sub_rev _ _)
    have hbd : ∀ n : ℕ, ∫ z in K, ‖moll ((bump n).normed volume) f z - F z‖ ≤
        (volume : Measure ℂ).real K * ((Real.pi)⁻¹ *
          ∫ w in Metric.cthickening 1 K, ‖moll ((bump n).normed volume) f w - f w‖) := by
      intro n
      calc ∫ z in K, ‖moll ((bump n).normed volume) f z - F z‖
          ≤ ∫ z in K, ((Real.pi)⁻¹ * ∫ w in Metric.cthickening 1 K,
              ‖moll ((bump n).normed volume) f w - f w‖) := by
            have haele : ∀ᵐ z ∂(volume.restrict K), ‖moll ((bump n).normed volume) f z - F z‖
                ≤ (Real.pi)⁻¹ * ∫ w in Metric.cthickening 1 K,
                    ‖moll ((bump n).normed volume) f w - f w‖ := by
              rw [ae_restrict_iff' hK.measurableSet]
              exact Eventually.of_forall fun z hz => hbound n hK z hz
            exact integral_mono_ae (hin2 n)
              (ContinuousOn.integrableOn_compact hK continuousOn_const) haele
        _ = (volume : Measure ℂ).real K * ((Real.pi)⁻¹ *
              ∫ w in Metric.cthickening 1 K, ‖moll ((bump n).normed volume) f w - f w‖) := by
            rw [setIntegral_const, smul_eq_mul]
    have hlim2 : Tendsto (fun n => ∫ z in K, ‖moll ((bump n).normed volume) f z - F z‖)
        atTop (nhds 0) := by
      refine squeeze_zero (fun n => integral_nonneg fun z => norm_nonneg _) hbd ?_
      have hc : Tendsto (fun n => ∫ w in Metric.cthickening 1 K,
            ‖moll ((bump n).normed volume) f w - f w‖) atTop (nhds 0) :=
        moll_bump_tendsto_L1 hf hKc
      have hmain := ((hc.const_mul (Real.pi)⁻¹).const_mul ((volume : Measure ℂ).real K))
      simpa only [mul_zero] using hmain
    have hsum : Tendsto (fun n => (∫ z in K, ‖f z - moll ((bump n).normed volume) f z‖)
        + ∫ z in K, ‖moll ((bump n).normed volume) f z - F z‖) atTop (nhds 0) := by
      have := hlim1.add hlim2
      simpa using this
    refine le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hsum
      (Eventually.of_forall hle)) ?_
    exact integral_nonneg fun z => norm_nonneg _
  -- hence `f = F` a.e.
  have hN : ∀ N : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ Metric.closedBall (0 : ℂ) (N : ℝ) → f z = F z := by
    intro N
    have hK : IsCompact (Metric.closedBall (0 : ℂ) (N : ℝ)) := isCompact_closedBall 0 (N : ℝ)
    have hint : IntegrableOn (fun z => ‖f z - F z‖) (Metric.closedBall (0 : ℂ) (N : ℝ)) volume :=
      ((hf.integrableOn_isCompact hK).sub (hFint hK)).norm
    have hzero : ∫ z in Metric.closedBall (0 : ℂ) (N : ℝ), ‖f z - F z‖ = 0 := hFK _ hK
    have hae : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) (N : ℝ))),
        ‖f z - F z‖ = 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun z => norm_nonneg _) hint).mp hzero
    rw [ae_restrict_iff' measurableSet_closedBall] at hae
    filter_upwards [hae] with z hz hzK
    exact sub_eq_zero.mp (norm_eq_zero.mp (hz hzK))
  have hall := ae_all_iff.mpr hN
  filter_upwards [hall] with z hz
  exact hz (Nat.ceil ‖z‖) (Metric.mem_closedBall.mpr (by simpa using Nat.le_ceil ‖z‖))

end

end Work.MRMT.Weyl
