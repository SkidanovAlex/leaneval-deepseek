/-
Support material for `Work.MRMT.Sobolev.mollification_pairing_tendsto`: the `L²` convergence of
mollification (pairing against an `L²` function).

Main ingredients:
* `tendsto_lintegral_ofReal_normed_mul` — concentration at `0`: averaging a function which tends
  to `0` at `0` against a normalised bump profile supported in a ball of radius `rOut → 0`;
* `tendsto_eLpNorm_sub_translate` — continuity of translation in `L²(ℂ)`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal Convolution

namespace Work.MRMT.Sobolev

/-! ## Averaging against a normalised bump -/

/-- The (lower Lebesgue) integral of a normalised bump profile is `1`. -/
theorem lintegral_ofReal_normed_eq_one (φ : ContDiffBump (0 : ℂ)) :
    ∫⁻ t, ENNReal.ofReal (φ.normed volume t) ∂(volume : Measure ℂ) = 1 := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
    (ae_of_all _ φ.nonneg_normed)]
  rw [φ.integral_normed]
  simp

/-- Concentration at `0`: if `ω : ℂ → ℝ≥0∞` tends to `0` at `0`, then its average against the
normalised bump profile `(φ i).normed volume` tends to `0` whenever `(φ i).rOut → 0`.  No global
boundedness of `ω` is needed, because each bump vanishes outside a small ball. -/
theorem tendsto_lintegral_ofReal_normed_mul {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℂ)}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0)) {ω : ℂ → ENNReal}
    (hω : Filter.Tendsto ω (𝓝 0) (𝓝 0)) :
    Filter.Tendsto (fun i => ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * ω t) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have h1 : {t : ℂ | ω t ≤ ε} ∈ 𝓝 (0 : ℂ) := (ENNReal.tendsto_nhds_zero.mp hω) ε hε
  rw [Metric.mem_nhds_iff] at h1
  obtain ⟨δ, hδ, hδω⟩ := h1
  filter_upwards [hφ.eventually (eventually_lt_nhds hδ)] with i hi
  calc ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * ω t
      ≤ ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * ε := by
        refine lintegral_mono fun t => ?_
        by_cases ht : (φ i).normed volume t = 0
        · simp [ht]
        · have ht' : t ∈ Metric.ball (0 : ℂ) (φ i).rOut := by
            rw [← (φ i).support_normed_eq (μ := (volume : Measure ℂ))]
            exact Function.mem_support.mpr ht
          have : ω t ≤ ε := hδω (Metric.ball_subset_ball hi.le ht')
          gcongr
    _ = (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t)) * ε :=
        MeasureTheory.lintegral_mul_const ε (φ i).continuous_normed.measurable.ennreal_ofReal
    _ = 1 * ε := by rw [lintegral_ofReal_normed_eq_one]
    _ = ε := by simp

/-! ## Continuity of translation in `L²` -/

/-- **Continuity of translation in `L²(ℂ)`**: for `f ∈ L²`, the `L²` distance between `f` and its
translate by `t` tends to `0` as `t → 0`.  Proof by density of continuous compactly supported
functions in `L²`. -/
theorem tendsto_eLpNorm_sub_translate {f : ℂ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
    Filter.Tendsto (fun t : ℂ => eLpNorm (fun z => f (z - t) - f z) 2 volume) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · filter_upwards with t
    rw [htop]; exact le_top
  have hγ : ε / 3 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩
  have hγtop : ε / 3 ≠ ⊤ := ENNReal.div_ne_top htop (by norm_num)
  obtain ⟨g, hgcs, hgclose, hgcont, hgmem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num) (ε := ε / 3) hγ
  have hgterm : ∀ᶠ t in 𝓝 (0 : ℂ), eLpNorm (fun z => g (z - t) - g z) 2 volume ≤ ε / 3 := by
    obtain ⟨R, hR⟩ := hgcs.isBounded.subset_closedBall (0 : ℂ)
    have hKR : tsupport g ⊆ Metric.closedBall (0 : ℂ) (max R 0) := by
      intro x hx
      have h1 : ‖x‖ ≤ R := by
        have h2 := Metric.mem_closedBall.mp (hR hx)
        rwa [dist_eq_norm, sub_zero] at h2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact h1.trans (le_max_left _ _)
    set S : Set ℂ := Metric.closedBall (0 : ℂ) (max R 0 + 1) with hSdef
    set T : Set ℂ := Metric.closedBall (0 : ℂ) (max R 0 + 2) with hTdef
    have hSc : IsCompact S := isCompact_closedBall _ _
    have hSfin : volume S < ⊤ := hSc.measure_lt_top
    have hTc : IsCompact T := isCompact_closedBall _ _
    set M : ENNReal := (volume S) ^ (1 / 2 : ℝ) with hMdef
    have hMtop : M ≠ ⊤ := by
      rw [hMdef]
      exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSfin.ne).ne
    set η : ℝ := (ε / 3).toReal / (M.toReal + 1) with hηdef
    have hηpos : 0 < η := by
      rw [hηdef]
      exact div_pos (ENNReal.toReal_pos hγ hγtop) (by positivity)
    have hnorm : ‖(η : ℂ)‖ₑ = ENNReal.ofReal η := by
      rw [enorm_eq_nnnorm, Complex.nnnorm_real, Real.nnnorm_of_nonneg hηpos.le]
      exact ENNReal.ofReal_coe_nnreal.symm
    have hunif := hTc.uniformContinuousOn_of_continuous hgcont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at hunif
    obtain ⟨δ, hδ, hδ'⟩ := hunif η hηpos
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (lt_min hδ one_pos)] with t ht
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at ht
    have htδ : ‖t‖ < δ := lt_of_lt_of_le ht (min_le_left _ _)
    have ht1 : ‖t‖ < 1 := lt_of_lt_of_le ht (min_le_right _ _)
    calc eLpNorm (fun z => g (z - t) - g z) 2 volume
        ≤ eLpNorm (S.indicator (fun _ => (η : ℂ))) 2 volume := by
          refine eLpNorm_mono_ae ?_ ?_
          · exact ((hgcont.comp (continuous_id.sub continuous_const)).sub hgcont).aestronglyMeasurable
          · filter_upwards with z
            by_cases hz : z ∈ S
            · have hzT : z ∈ T := by
                rw [hTdef, Metric.mem_closedBall, dist_eq_norm, sub_zero]
                have hz' := Metric.mem_closedBall.mp hz
                rw [dist_eq_norm, sub_zero] at hz'
                linarith
              have hzt : z - t ∈ T := by
                rw [hTdef, Metric.mem_closedBall, dist_eq_norm, sub_zero]
                have hz' := Metric.mem_closedBall.mp hz
                rw [dist_eq_norm, sub_zero] at hz'
                calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le _ _
                  _ ≤ (max R 0 + 1) + 1 := by linarith
                  _ = max R 0 + 2 := by ring
              have hdist : dist (z - t) z < δ := by
                rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
                exact htδ
              have hlt := hδ' (z - t) hzt z hzT hdist
              rw [Set.indicator_of_mem hz, Complex.norm_real, Real.norm_of_nonneg hηpos.le]
              calc ‖g (z - t) - g z‖ = dist (g (z - t)) (g z) := by rw [dist_eq_norm]
                _ ≤ η := hlt.le
            · have hzneg : max R 0 + 1 < ‖z‖ := by
                have hnot : ¬ (dist z 0 ≤ max R 0 + 1) := by
                  intro hcon
                  exact hz (Metric.mem_closedBall.mpr hcon)
                rw [dist_eq_norm, sub_zero] at hnot
                exact not_le.mp hnot
              have hzero : g (z - t) - g z = 0 := by
                have hzK : z ∉ tsupport g := by
                  intro hzK
                  exact hz (Metric.closedBall_subset_closedBall (by linarith) (hKR hzK))
                have hztK : z - t ∉ tsupport g := by
                  intro hztK
                  have h1 : ‖z - t‖ ≤ max R 0 := by
                    have h2 := Metric.mem_closedBall.mp (hKR hztK)
                    rwa [dist_eq_norm, sub_zero] at h2
                  have h2 : ‖z‖ ≤ max R 0 + 1 := by
                    calc ‖z‖ = ‖(z - t) + t‖ := by rw [sub_add_cancel]
                      _ ≤ ‖z - t‖ + ‖t‖ := norm_add_le _ _
                      _ ≤ max R 0 + 1 := by linarith
                  linarith
                rw [image_eq_zero_of_notMem_tsupport hztK, image_eq_zero_of_notMem_tsupport hzK]
                ring
              rw [Set.indicator_of_notMem hz, hzero, norm_zero]
        _ ≤ ‖(η : ℂ)‖ₑ * (volume S) ^ (1 / (2 : ENNReal).toReal) :=
            eLpNorm_indicator_const_le (η : ℂ) 2 hSc.measurableSet.nullMeasurableSet
        _ = ENNReal.ofReal η * M := by
            rw [hMdef, hnorm, show (2 : ENNReal).toReal = 2 by norm_num,
              show (1 : ℝ) / 2 = (1 / 2 : ℝ) by norm_num]
        _ ≤ ε / 3 := by
            have hMle : M ≤ ENNReal.ofReal (M.toReal + 1) := by
              have h1 : (0 : ℝ) ≤ M.toReal := ENNReal.toReal_nonneg
              calc M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hMtop).symm
                _ ≤ ENNReal.ofReal (M.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
            rw [hηdef]
            calc ENNReal.ofReal ((ε / 3).toReal / (M.toReal + 1)) * M
                ≤ ENNReal.ofReal ((ε / 3).toReal / (M.toReal + 1)) *
                    ENNReal.ofReal (M.toReal + 1) := by
                  gcongr
              _ = ENNReal.ofReal (((ε / 3).toReal / (M.toReal + 1)) * (M.toReal + 1)) := by
                  rw [ENNReal.ofReal_mul (by positivity)]
              _ = ENNReal.ofReal ((ε / 3).toReal) := by
                  congr 1
                  field_simp
              _ ≤ ε / 3 := ENNReal.ofReal_toReal_le
  filter_upwards [hgterm] with t ht
  have hcongr : (fun z => f (z - t) - f z)
      = fun z => f (z - t) - g (z - t) + (g (z - t) - g z + (g z - f z)) := by
    funext z; ring
  rw [hcongr]
  have hA : eLpNorm (fun z => f (z - t) - g (z - t)) 2 volume ≤ ε / 3 := by
    have h2 : (fun z => f (z - t) - g (z - t)) = (f - g) ∘ (fun z => z - t) := rfl
    rw [h2, eLpNorm_comp_measurePreserving
      (hf.aestronglyMeasurable.sub hgmem.aestronglyMeasurable)
      (measurePreserving_sub_right volume t)]
    exact hgclose
  have hC : eLpNorm (fun z => g z - f z) 2 volume ≤ ε / 3 := by
    have h2 : (fun z => g z - f z) = -(fun z => f z - g z) := by
      funext z; simp only [Pi.neg_apply]; ring
    rw [h2, eLpNorm_neg]
    exact hgclose
  calc eLpNorm (fun z => f (z - t) - g (z - t) + (g (z - t) - g z + (g z - f z))) 2 volume
      ≤ eLpNorm (fun z => f (z - t) - g (z - t)) 2 volume
        + eLpNorm (fun z => g (z - t) - g z + (g z - f z)) 2 volume := eLpNorm_add_le (by norm_num)
    _ ≤ eLpNorm (fun z => f (z - t) - g (z - t)) 2 volume
        + (eLpNorm (fun z => g (z - t) - g z) 2 volume
          + eLpNorm (fun z => g z - f z) 2 volume) :=
        add_le_add le_rfl (eLpNorm_add_le (by norm_num))
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := add_le_add hA (add_le_add ht hC)
    _ = ε := by
        rw [show ε / 3 + (ε / 3 + ε / 3) = 3 * (ε / 3) by ring,
          ENNReal.mul_div_cancel' (a := 3) (b := ε) (by norm_num) (by norm_num)]

/-- A function in `L²(ℂ)` with compact support is integrable. -/
theorem integrable_of_memLp_two_hasCompactSupport {f : ℂ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume) (hc : HasCompactSupport f) :
    MeasureTheory.Integrable f MeasureTheory.volume := by
  rw [← MeasureTheory.memLp_one_iff_integrable]
  exact hf.mono_exponent_of_measure_support_ne_top
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) hc.measure_lt_top.ne (by norm_num)

theorem mollification_pairing_tendsto {G P : ℂ → ℂ}
    (hG : MeasureTheory.MemLp G 2 MeasureTheory.volume) (hGc : HasCompactSupport G)
    (hP : MeasureTheory.MemLp P 2 MeasureTheory.volume) (hPc : HasCompactSupport P)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : ℂ)}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (nhds 0)) :
    Filter.Tendsto (fun i => ∫ z, P z * (MeasureTheory.convolution G (fun z => (((φ i).normed MeasureTheory.volume) z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) MeasureTheory.volume z - G z)) l (nhds 0) := by
  have hGint : Integrable G volume := integrable_of_memLp_two_hasCompactSupport hG hGc
  have hnormco : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
    intro r hr
    rw [enorm_eq_nnnorm, Complex.nnnorm_real, Real.nnnorm_of_nonneg hr]
    exact ENNReal.ofReal_coe_nnreal.symm
  have hψtop (i : ι) : MemLp (fun t => ((φ i).normed volume t : ℂ)) ⊤ volume :=
    (Complex.continuous_ofReal.comp (φ i).continuous_normed).memLp_top_of_hasCompactSupport
      ((φ i).hasCompactSupport_normed.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)) volume
  have hψint (i : ι) : Integrable (fun t => ((φ i).normed volume t : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (φ i).continuous_normed).integrable_of_hasCompactSupport
      ((φ i).hasCompactSupport_normed.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
  have hint (i : ι) : ∫ t, ((φ i).normed volume t : ℂ) ∂(volume : Measure ℂ) = 1 := by
    have h2 : (∫ t, ((φ i).normed volume t : ℂ) ∂(volume : Measure ℂ))
        = ∫ t, Complex.ofRealCLM ((φ i).normed volume t) ∂(volume : Measure ℂ) := rfl
    rw [h2, ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM (φ i).integrable_normed,
      (φ i).integral_normed]
    simp
  have hId (i : ι) (z : ℂ) :
      convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z
        = ∫ t, (G (z - t) - G z) * ((φ i).normed volume t : ℂ) ∂volume := by
    have h1 : Integrable (fun t => G (z - t) * ((φ i).normed volume t : ℂ)) volume := by
      have h2 := (hGint.comp_sub_left z).mul_of_top_right (hψtop i)
      refine h2.congr (Eventually.of_forall fun t => ?_)
      simp only [Pi.mul_apply, mul_comm]
    have h2 : Integrable (fun t => G z * ((φ i).normed volume t : ℂ)) volume :=
      (hψint i).const_mul (G z)
    rw [convolution_eq_swap]
    rw [show (∫ t, (ContinuousLinearMap.mul ℝ ℂ) (G (z - t)) (((φ i).normed volume) t : ℂ))
        = ∫ t, G (z - t) * ((φ i).normed volume t : ℂ) from
      integral_congr_ae (Eventually.of_forall fun t => by simp)]
    rw [show (∫ t, (G (z - t) - G z) * ((φ i).normed volume t : ℂ))
        = ∫ t, (G (z - t) * ((φ i).normed volume t : ℂ) - G z * ((φ i).normed volume t : ℂ)) from
      integral_congr_ae (Eventually.of_forall fun t => by ring)]
    rw [integral_sub h1 h2, integral_const_mul, hint i, mul_one]
  have hbound (i : ι) (z : ℂ) :
      ‖convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z‖ₑ
        ≤ ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ ∂volume := by
    rw [hId i z]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono fun t => ?_
    rw [enorm_mul, hnormco _ ((φ i).nonneg_normed t), mul_comm]
  set CP : ENNReal := ∫⁻ z, ‖P z‖ₑ * ‖P z‖ₑ ∂volume with hCPdef
  have hCPtop : CP ≠ ⊤ := by
    have h1 : (∫⁻ z, ‖P z‖ₑ ^ ((2 : ENNReal).toReal) ∂volume) = CP := by
      rw [hCPdef]
      exact lintegral_congr fun z => by
        rw [show (2 : ENNReal).toReal = 2 by norm_num, ENNReal.rpow_two, pow_two]
    have h2 : (1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) := by norm_num
    have heq : eLpNorm P 2 volume = CP ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
        hP.aestronglyMeasurable, h1, h2]
    have h3 : CP ^ (1 / 2 : ℝ) ≠ ⊤ := by rw [← heq]; exact hP.eLpNorm_ne_top
    intro hcon
    exact h3 (by rw [hcon]; exact ENNReal.top_rpow_of_pos (by norm_num))
  have hCtop : CP ^ (1 / 2 : ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCPtop).ne
  have hkey (i : ι) :
      ‖∫ z, P z * (convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z)‖ₑ
        ≤ CP ^ (1 / 2 : ℝ) * ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * eLpNorm (fun z => G (z - t) - G z) 2 volume := by
    have hPmeas : AEMeasurable (fun z : ℂ => ‖P z‖ₑ) volume := hP.aestronglyMeasurable.enorm
    have hSmeas : ∀ t : ℂ, AEMeasurable (fun z : ℂ => ‖G (z - t) - G z‖ₑ) volume := fun t =>
      ((hG.aestronglyMeasurable.comp_measurePreserving (measurePreserving_sub_right volume t)).sub
        hG.aestronglyMeasurable).enorm
    have hCmeas : ∀ t : ℂ, AEStronglyMeasurable (fun z : ℂ => G (z - t) - G z) volume := fun t =>
      (hG.aestronglyMeasurable.comp_measurePreserving (measurePreserving_sub_right volume t)).sub
        hG.aestronglyMeasurable
    have hmeas0 : AEMeasurable (fun p : ℂ × ℂ => ‖P p.1‖ₑ *
        (ENNReal.ofReal ((φ i).normed volume p.2) * ‖G (p.1 - p.2) - G p.1‖ₑ)) (volume.prod volume) := by
      have hP' : AEMeasurable (fun p : ℂ × ℂ => ‖P p.1‖ₑ) (volume.prod volume) :=
        (hP.aemeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume))).enorm
      have hψ' : AEMeasurable (fun p : ℂ × ℂ => ENNReal.ofReal ((φ i).normed volume p.2))
          (volume.prod volume) :=
        (((φ i).continuous_normed.measurable.comp measurable_snd)).ennreal_ofReal.aemeasurable
      have hG' : AEMeasurable (fun p : ℂ × ℂ => ‖G (p.1 - p.2) - G p.1‖ₑ) (volume.prod volume) :=
        (((hG.aemeasurable.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_of_right_invariant volume volume)).sub
          (hG.aemeasurable.comp_quasiMeasurePreserving
            (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume))))).enorm
      exact hP'.mul (hψ'.mul hG')
    have hmeas : AEMeasurable (Function.uncurry fun z t : ℂ => ‖P z‖ₑ *
        (ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ)) (volume.prod volume) := hmeas0
    have hholder : ∀ t : ℂ, (∫⁻ z, ‖P z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume)
        ≤ (∫⁻ z, ‖P z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
          * (∫⁻ z, ‖G (z - t) - G z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) := fun t =>
      ENNReal.lintegral_mul_le_Lp_mul_Lq volume (p := 2) (q := 2)
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hPmeas (hSmeas t)
    have hswap : (∫⁻ z, ‖P z‖ₑ *
          (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ ∂volume) ∂volume)
        = ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
          (∫⁻ z, ‖P z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ∂volume := by
      calc ∫⁻ z, ‖P z‖ₑ *
            (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ ∂volume) ∂volume
          = ∫⁻ z, ∫⁻ t, ‖P z‖ₑ *
              (ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ) ∂volume ∂volume := by
            refine lintegral_congr fun z => ?_
            rw [MeasureTheory.lintegral_const_mul' (‖P z‖ₑ) _ enorm_ne_top]
        _ = ∫⁻ t, ∫⁻ z, ‖P z‖ₑ *
              (ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ) ∂volume ∂volume := by
            rw [lintegral_lintegral_swap (μ := volume) (ν := volume) hmeas]
        _ = ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
              (∫⁻ z, ‖P z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ∂volume := by
            refine lintegral_congr fun t => ?_
            rw [show (fun z => ‖P z‖ₑ *
                  (ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ))
                = fun z => ENNReal.ofReal ((φ i).normed volume t) *
                  (‖P z‖ₑ * ‖G (z - t) - G z‖ₑ) from funext fun z => by ring]
            rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((φ i).normed volume t)) _
              ENNReal.ofReal_ne_top]
    have homega : (fun t : ℂ => eLpNorm (fun z => G (z - t) - G z) 2 volume)
        = fun t => (∫⁻ z, ‖G (z - t) - G z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ^ (1/2:ℝ) := by
      funext t
      have h2 : (1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) := by norm_num
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) (hCmeas t),
        h2]
      congr 1
      exact lintegral_congr fun z => by
        rw [show (2 : ENNReal).toReal = 2 by norm_num, ENNReal.rpow_two, pow_two]
    calc ‖∫ z, P z * (convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z)‖ₑ
        ≤ ∫⁻ z, ‖P z‖ₑ * ‖convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z‖ₑ := by
          refine (enorm_integral_le_lintegral_enorm _).trans ?_
          refine lintegral_mono fun z => ?_
          rw [enorm_mul]
      _ ≤ ∫⁻ z, ‖P z‖ₑ *
            (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * ‖G (z - t) - G z‖ₑ ∂volume) ∂volume := by
          refine lintegral_mono fun z => ?_
          gcongr
          exact hbound i z
      _ = ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
            (∫⁻ z, ‖P z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ∂volume := hswap
      _ ≤ ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
            (CP ^ (1/2:ℝ) * (∫⁻ z, ‖G (z - t) - G z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ^ (1/2:ℝ)) ∂volume := by
          refine lintegral_mono fun t => ?_
          gcongr
          calc ∫⁻ z, ‖P z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume
              ≤ (∫⁻ z, ‖P z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) *
                (∫⁻ z, ‖G (z - t) - G z‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) := hholder t
            _ = CP ^ (1/2:ℝ) *
                (∫⁻ z, ‖G (z - t) - G z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ^ (1/2:ℝ) := by
                have h1 : (∫⁻ z, ‖P z‖ₑ ^ (2:ℝ) ∂volume) = CP := by
                  rw [hCPdef]
                  exact lintegral_congr fun z => by rw [ENNReal.rpow_two, pow_two]
                have h2 : (∫⁻ z, ‖G (z - t) - G z‖ₑ ^ (2:ℝ) ∂volume)
                    = ∫⁻ z, ‖G (z - t) - G z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume :=
                  lintegral_congr fun z => by rw [ENNReal.rpow_two, pow_two]
                rw [h1, h2]
      _ = CP ^ (1/2:ℝ) * ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
            (∫⁻ z, ‖G (z - t) - G z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ^ (1/2:ℝ) ∂volume := by
          rw [show (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
                (CP ^ (1/2:ℝ) * (∫⁻ z, ‖G (z - t) - G z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ^ (1/2:ℝ)) ∂volume)
              = ∫⁻ t, CP ^ (1/2:ℝ) * (ENNReal.ofReal ((φ i).normed volume t) *
                (∫⁻ z, ‖G (z - t) - G z‖ₑ * ‖G (z - t) - G z‖ₑ ∂volume) ^ (1/2:ℝ)) ∂volume from
            lintegral_congr fun t => by ring]
          rw [MeasureTheory.lintegral_const_mul' (CP ^ (1/2:ℝ)) _ hCtop]
      _ = CP ^ (1/2:ℝ) * ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
            eLpNorm (fun z => G (z - t) - G z) 2 volume := by
          congr 1
          exact (congrArg (fun v : ℂ → ENNReal =>
            ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) * v t ∂volume) homega).symm
  have hω : Tendsto (fun t : ℂ => eLpNorm (fun z => G (z - t) - G z) 2 volume) (𝓝 0) (𝓝 0) :=
    tendsto_eLpNorm_sub_translate hG
  have hB : Tendsto (fun i => ∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
      eLpNorm (fun z => G (z - t) - G z) 2 volume) l (𝓝 0) :=
    tendsto_lintegral_ofReal_normed_mul hφ hω
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro η hη
  set ς : ENNReal := ENNReal.ofReal (η / (2 * ((CP ^ (1 / 2 : ℝ)).toReal + 1))) with hςdef
  have hςpos : ς > 0 := by
    rw [hςdef]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hB) ς hςpos] with i hBi
  have hBtop : (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
      eLpNorm (fun z => G (z - t) - G z) 2 volume) ≠ ⊤ := by
    refine lt_top_iff_ne_top.mp (lt_of_le_of_lt hBi ?_)
    rw [hςdef]; exact ENNReal.ofReal_lt_top
  have hprodtop : CP ^ (1 / 2 : ℝ) * (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
      eLpNorm (fun z => G (z - t) - G z) 2 volume) ≠ ⊤ := ENNReal.mul_ne_top hCtop hBtop
  rw [dist_zero_right, norm_norm]
  have hstep : ‖∫ z, P z * (convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z)‖
      ≤ (CP ^ (1 / 2 : ℝ)).toReal * (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
        eLpNorm (fun z => G (z - t) - G z) 2 volume).toReal := by
    have hT : ‖∫ z, P z * (convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z)‖
        = (‖∫ z, P z * (convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z)‖ₑ).toReal := by
      simp [enorm_eq_nnnorm]
    rw [hT, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hprodtop (hkey i)
  calc ‖∫ z, P z * (convolution G (fun z => ((φ i).normed volume z : ℂ)) (ContinuousLinearMap.mul ℝ ℂ) volume z - G z)‖
      ≤ (CP ^ (1 / 2 : ℝ)).toReal * (∫⁻ t, ENNReal.ofReal ((φ i).normed volume t) *
          eLpNorm (fun z => G (z - t) - G z) 2 volume).toReal := hstep
    _ ≤ (CP ^ (1 / 2 : ℝ)).toReal * ς.toReal :=
        mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono (by rw [hςdef]; exact ENNReal.ofReal_ne_top) hBi)
          ENNReal.toReal_nonneg
    _ = (CP ^ (1 / 2 : ℝ)).toReal * (η / (2 * ((CP ^ (1 / 2 : ℝ)).toReal + 1))) := by
        rw [hςdef, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ η / 2 := by
        have hle : (CP ^ (1 / 2 : ℝ)).toReal / (2 * ((CP ^ (1 / 2 : ℝ)).toReal + 1)) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith [ENNReal.toReal_nonneg (a := CP ^ (1 / 2 : ℝ))]
        calc (CP ^ (1 / 2 : ℝ)).toReal * (η / (2 * ((CP ^ (1 / 2 : ℝ)).toReal + 1)))
            = η * ((CP ^ (1 / 2 : ℝ)).toReal / (2 * ((CP ^ (1 / 2 : ℝ)).toReal + 1))) := by ring
          _ ≤ η * (1 / 2) := by gcongr
          _ = η / 2 := by ring
    _ < η := by linarith

end Work.MRMT.Sobolev
