import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.Flat2DAgmonNiceBPrelim2
import Submission.Work.FTS.EllSol.FlatFT.integral_mul_le_sqrt_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open Work.Spaces

local notation "thEta" => Work.FTS.EllipticEst.thEta
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1000000

theorem flat2DAgmonNiceB_lintegral {Cc : ℝ} (hCcpos : 0 < Cc)
    (hCc : ∀ F : ℝ → ℂ,
      ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)) → F 0 = 0 → F (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖F θ‖ ^ 2 * thEta θ)
        Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv F θ‖ ^ 2 * thEta θ)
        Iθ →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => ‖deriv (deriv F) θ‖ ^ 2 * thEta θ) Iθ →
      (∫ θ in Iθ, ‖deriv F θ‖ ^ 2 * thEta θ) ≤
        Cc * ((∫ θ in Iθ, ‖F θ‖ ^ 2 * thEta θ) +
          Real.sqrt ((∫ θ in Iθ, ‖F θ‖ ^ 2 * thEta θ) *
            (∫ θ in Iθ,
              ‖deriv (deriv F) θ‖ ^ 2 * thEta θ))))
    (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : NiceFlat g)
    (hA2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (pz (pz g) p.1 p.2) ^ 2 * wE p.2)
      ((Set.univ : Set ℝ) ×ˢ Iθ))
    (hBq : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (pth (pth g) p.1 p.2) ^ 2 * wE p.2)
      ((Set.univ : Set ℝ) ×ˢ Iθ))
    (hB0 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (pz g p.1 p.2) ^ 2 * wE p.2)
      ((Set.univ : Set ℝ) ×ˢ Iθ))
    (hα4 : α ≤ 1 / 4) :
    (∫⁻ p in Set.univ ×ˢ Iθ,
        ENNReal.ofReal ((pz (pth g) p.1 p.2) ^ 2
          * wA α p.2))
      ≤ ENNReal.ofReal (Cc * ((∫ p in Set.univ ×ˢ Iθ,
              (pz g p.1 p.2) ^ 2 * wE p.2)
          + Real.sqrt ((∫ p in Set.univ ×ˢ Iθ,
                (pz (pz g) p.1 p.2) ^ 2 * wE p.2)
              * (∫ p in Set.univ ×ˢ Iθ,
                  (pth (pth g) p.1 p.2) ^ 2
                    * wE p.2)))) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hs : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    MeasurableSet.univ.prod measurableSet_Iθ
  have hdth := dthBound g hg hBq
  have hA1 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (pth g p.1 p.2) ^ 2 * wE p.2)
      (Set.univ ×ˢ Iθ) := hdth.1
  have hA0 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2 * wE p.2)
      (Set.univ ×ˢ Iθ) := hdth.2
  have he0 : MeasureTheory.IntegrableOn (fun θ : ℝ => (∫ t : ℝ, (g t θ) ^ 2) * wE θ)
      Iθ := integrableOn_energy_mul measurable_wE hA0
  have he1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (pth g t θ) ^ 2) * wE θ) Iθ :=
    integrableOn_energy_mul measurable_wE hA1
  have heq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (pth (pth g) t θ) ^ 2) * wE θ)
      Iθ := integrableOn_energy_mul measurable_wE hBq
  have hcd_g : ContDiffOn ℝ 2 (Function.uncurry g) flStrip := hg.1
  have hcd_pth : ContDiffOn ℝ 1 (Function.uncurry (pth g)) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_g
  have hcd_pthpth : ContDiffOn ℝ 0
      (Function.uncurry (pth (pth g))) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_pth
  have hcd_pz : ContDiffOn ℝ 1 (Function.uncurry (pz g)) flStrip :=
    pz_contDiffOn_succ flStrip_isOpen hcd_g
  have hcd_pzpz : ContDiffOn ℝ 0
      (Function.uncurry (pz (pz g))) flStrip :=
    pz_contDiffOn_succ flStrip_isOpen hcd_pz
  have hcd_pzpth : ContDiffOn ℝ 0
      (Function.uncurry (pz (pth g))) flStrip :=
    pz_contDiffOn_succ flStrip_isOpen hcd_pth
  have hsupp_pth : ∀ t θ : ℝ, M < |t| → pth g t θ = 0 := supp_pth hM
  have hsupp_pz : ∀ t θ : ℝ, M < |t| → pz g t θ = 0 := supp_pz hM
  have hsupp_pthpth : ∀ t θ : ℝ, M < |t| → pth (pth g) t θ = 0 :=
    supp_pthpth hM
  have hsupp_pzpth : ∀ t θ : ℝ, M < |t| → pz (pth g) t θ = 0 :=
    supp_pzpth hM
  have hsl_g : ContinuousOn (fun p : ℝ × ℝ => slice g p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_g.continuousOn ⟨M, hM0, hM⟩
  have hsl_pth : ContinuousOn (fun p : ℝ × ℝ => slice (pth g) p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_pth.continuousOn ⟨M, hM0, hsupp_pth⟩
  have hsl_pthpth : ContinuousOn
      (fun p : ℝ × ℝ => slice (pth (pth g)) p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_pthpth.continuousOn ⟨M, hM0, hsupp_pthpth⟩
  have hslice_g : ∀ ξ : ℝ, ContinuousOn (fun θ : ℝ => slice g ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => by
      simpa [Function.comp_def] using
        hsl_g.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => mem_flStrip hθ)
  have hslice_pth : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice (pth g) ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => by
      simpa [Function.comp_def] using
        hsl_pth.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => mem_flStrip hθ)
  have hslice_pthpth : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice (pth (pth g)) ξ θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => by
      simpa [Function.comp_def] using
        hsl_pthpth.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => mem_flStrip hθ)
  have hJg : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice g ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_g.continuousOn hM
      (fun θ hθ => wE_nonneg hθ) measurable_wE (hslice_g ξ) he0
  have hJpth : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth g) ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_pth.continuousOn hsupp_pth
      (fun θ hθ => wE_nonneg hθ) measurable_wE (hslice_pth ξ) he1
  have hJpthpth : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)
      Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_pthpth.continuousOn hsupp_pthpth
      (fun θ hθ => wE_nonneg hθ) measurable_wE (hslice_pthpth ξ) heq
  have hJpthA : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth g) ξ θ‖ ^ 2 * wA α θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul_le (fun θ hθ => wA_nonneg hθ) (fun θ hθ => wE_nonneg hθ)
      (fun θ hθ => wA_le_wE hα1 hθ) (hslice_pth ξ) (measurable_wA α) (hJpth ξ)
  have hξA : ∀ ξ : ℝ,
      (∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wA α θ)
        ≤ Cc * ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
          + Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ,
                  ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))) := by
    intro ξ
    have hΦcd : ContDiffOn ℝ 2 (fun θ : ℝ => slice g ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
      sliceContDiffOn (n := 2) (by norm_num) hcd_g ⟨M, hM0, hM⟩ ξ
    have hderiv_ae : (fun θ : ℝ => deriv (fun θ' => slice g ξ θ') θ)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Iθ]
          (fun θ : ℝ => slice (pth g) ξ θ) := by
      have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2)
          =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact (slice_hasDerivAt g hg ξ hθ).1.deriv
    have hderiv2_ae : (fun θ : ℝ => deriv (deriv (fun θ'' => slice g ξ θ'')) θ)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Iθ]
          (fun θ : ℝ => slice (pth (pth g)) ξ θ) := by
      have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2)
          =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hev : (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ')
          =ᶠ[𝓝 θ] (fun θ' => slice (pth g) ξ θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact (slice_hasDerivAt g hg ξ hθ').1.deriv
      rw [hev.deriv_eq, (slice_hasDerivAt g hg ξ hθ).2.deriv]
    have hI1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ‖deriv (fun θ' => slice g ξ θ') θ‖ ^ 2
          * thEta θ) Iθ :=
      (hJpth ξ).congr (by filter_upwards [hderiv_ae] with θ hθ; rw [hθ]; rfl)
    have hI2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ‖deriv (deriv (fun θ'' => slice g ξ θ'')) θ‖ ^ 2
          * thEta θ) Iθ :=
      (hJpthpth ξ).congr (by filter_upwards [hderiv2_ae] with θ hθ; rw [hθ]; rfl)
    have hkey := hCc (fun θ : ℝ => slice g ξ θ) hΦcd (slice_eq_zero hg ξ)
      (slice_eq_zero_pi hg ξ) (hJg ξ) hI1 hI2
    have e1 : (∫ θ in Iθ, ‖deriv (fun θ' => slice g ξ θ') θ‖ ^ 2
          * thEta θ)
        = ∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (by filter_upwards [hderiv_ae] with θ hθ; rw [hθ]; rfl)
    have e2 : (∫ θ in Iθ, ‖deriv (deriv (fun θ'' => slice g ξ θ'')) θ‖ ^ 2
          * thEta θ)
        = ∫ θ in Iθ,
            ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (by filter_upwards [hderiv2_ae] with θ hθ; rw [hθ]; rfl)
    have hmain : (∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wE θ)
        ≤ Cc * ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
          + Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ,
                  ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))) := by
      rw [e1, e2] at hkey
      exact hkey
    have hBle : (∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wA α θ)
        ≤ ∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wE θ := by
      refine integral_mono_ae (hJpthA ξ) (hJpth ξ) ?_
      filter_upwards [ae_mem_Iθ] with θ hθ
      exact mul_le_mul_of_nonneg_left (wA_le_wE hα1 hθ) (sq_nonneg _)
    exact le_trans hBle hmain
  have hW2c : Continuous fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2 := by fun_prop
  have hW2m : Measurable fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2 := hW2c.measurable
  have hW4c : Continuous fun ξ : ℝ => (2 * Real.pi * ξ) ^ 4 := by fun_prop
  have hW4m : Measurable fun ξ : ℝ => (2 * Real.pi * ξ) ^ 4 := hW4c.measurable
  have hW1m : Measurable fun _ : ℝ => (1 : ℝ) := measurable_const
  have hid_g : (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
        * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ,
          ENNReal.ofReal ((pz g p.1 p.2) ^ 2 * wE p.2) :=
    lintegral_slice_plancherel g (pz g) (fun ξ => (2 * Real.pi * ξ) ^ 2) wE
      (fun ξ => sq_nonneg _) (fun θ hθ => wE_nonneg hθ) hJg
      (ae_mem_Ioo_Iθ.mono fun θ hθ => integrable_sq_slice hM0 hcd_pz.continuousOn hsupp_pz hθ)
      (ae_mem_Ioo_Iθ.mono fun θ hθ => plancherel_g_one hg hθ)
      (aemeasurable_ofReal_weight_mul hsl_g hW2m measurable_wE)
      (aemeasurable_ofReal_sq_mul_snd hcd_pz.continuousOn measurable_wE)
  have hid_g4 : (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 4
        * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ,
          ENNReal.ofReal ((pz (pz g) p.1 p.2) ^ 2 * wE p.2) :=
    lintegral_slice_plancherel g (pz (pz g))
      (fun ξ => (2 * Real.pi * ξ) ^ 4) wE
      (fun ξ => by positivity) (fun θ hθ => wE_nonneg hθ) hJg
      (ae_mem_Ioo_Iθ.mono fun θ hθ =>
        integrable_sq_slice hM0 hcd_pzpz.continuousOn (supp_pzpz hM) hθ)
      (ae_mem_Ioo_Iθ.mono fun θ hθ => plancherel_g_two hg hθ)
      (aemeasurable_ofReal_weight_mul hsl_g hW4m measurable_wE)
      (aemeasurable_ofReal_sq_mul_snd hcd_pzpz.continuousOn measurable_wE)
  have hid_lhs : (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
        * ∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wA α θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ,
          ENNReal.ofReal ((pz (pth g) p.1 p.2) ^ 2 * wA α p.2) :=
    lintegral_slice_plancherel (pth g) (pz (pth g))
      (fun ξ => (2 * Real.pi * ξ) ^ 2) (wA α)
      (fun ξ => sq_nonneg _) (fun θ hθ => wA_nonneg hθ) hJpthA
      (ae_mem_Ioo_Iθ.mono fun θ hθ =>
        integrable_sq_slice hM0 hcd_pzpth.continuousOn hsupp_pzpth hθ)
      (ae_mem_Ioo_Iθ.mono fun θ hθ => plancherel_pth hg hθ)
      (aemeasurable_ofReal_weight_mul hsl_pth hW2m (measurable_wA α))
      (aemeasurable_ofReal_sq_mul_snd hcd_pzpth.continuousOn (measurable_wA α))
  have hid_D : (∫⁻ ξ, ENNReal.ofReal ((1 : ℝ)
        * ∫ θ in Iθ,
            ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ,
          ENNReal.ofReal ((pth (pth g) p.1 p.2) ^ 2 * wE p.2) := by
    refine lintegral_slice_plancherel (pth (pth g))
      (pth (pth g)) (fun _ : ℝ => (1 : ℝ)) wE
      (fun ξ => zero_le_one) (fun θ hθ => wE_nonneg hθ) hJpthpth
      (ae_mem_Ioo_Iθ.mono fun θ hθ =>
        integrable_sq_slice hM0 hcd_pthpth.continuousOn hsupp_pthpth hθ)
      ?_ (aemeasurable_ofReal_weight_mul hsl_pthpth hW1m measurable_wE)
      (aemeasurable_ofReal_sq_mul_snd hcd_pthpth.continuousOn measurable_wE)
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    refine ⟨?_, ?_⟩
    · exact (plancherel_pthpth hg hθ).1.congr
        (Eventually.of_forall fun ξ => by simp only [one_mul])
    · rw [show (∫ ξ : ℝ, (1 : ℝ)
            * ‖slice (pth (pth g)) ξ θ‖ ^ 2)
          = ∫ ξ : ℝ, ‖slice (pth (pth g)) ξ θ‖ ^ 2 from
        integral_congr_ae (Eventually.of_forall fun ξ => one_mul _)]
      exact (plancherel_pthpth hg hθ).2
  have hPnn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pz g p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  have hP2nn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pz (pz g) p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  have hQ2nn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pth (pth g) p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  have hnn_s : 0 ≤ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))).restrict
      (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pz g p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hnn_s2 : 0 ≤ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))).restrict
      (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pz (pz g) p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hnn_sq : 0 ≤ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))).restrict
      (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pth (pth g) p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hP : (∫⁻ p in Set.univ ×ˢ Iθ,
        ENNReal.ofReal ((pz g p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz g p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hB0 hnn_s).symm
  have hP2 : (∫⁻ p in Set.univ ×ˢ Iθ,
        ENNReal.ofReal ((pz (pz g) p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz (pz g) p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hA2 hnn_s2).symm
  have hQ2 : (∫⁻ p in Set.univ ×ˢ Iθ,
        ENNReal.ofReal ((pth (pth g) p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pth (pth g) p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hBq hnn_sq).symm
  have hlimA : (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
        * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz g p.1 p.2) ^ 2 * wE p.2) := hid_g.trans hP
  have hlimA2 : (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 4
        * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz (pz g) p.1 p.2) ^ 2 * wE p.2) := hid_g4.trans hP2
  have hlimD : (∫⁻ ξ, ENNReal.ofReal
        (∫ θ in Iθ,
          ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pth (pth g) p.1 p.2) ^ 2 * wE p.2) := by
    have h := hid_D
    rw [show (∫⁻ ξ, ENNReal.ofReal ((1 : ℝ) * ∫ θ in Iθ,
          ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))
        = ∫⁻ ξ, ENNReal.ofReal (∫ θ in Iθ,
            ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ) from
      lintegral_congr fun ξ => by rw [one_mul]] at h
    rw [h, hQ2]
  have hL1 : (∫⁻ p in Set.univ ×ˢ Iθ,
        ENNReal.ofReal ((pz (pth g) p.1 p.2) ^ 2 * wA α p.2))
      = ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
          * ∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wA α θ) :=
    hid_lhs.symm
  have hAmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    (aemeasurable_slice_sq_mul_snd hsl_g measurable_wE).aestronglyMeasurable.integral_prod_right'
  have hDmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∫ θ in Iθ,
        ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    (aemeasurable_slice_sq_mul_snd hsl_pthpth measurable_wE).aestronglyMeasurable
      |>.integral_prod_right'
  have hAnon : ∀ ξ : ℝ, 0 ≤ ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ :=
    fun ξ => integral_nonneg_of_ae
      (ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (wE_nonneg hθ))
  have hDnon : ∀ ξ : ℝ, 0 ≤ ∫ θ in Iθ,
      ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ :=
    fun ξ => integral_nonneg_of_ae
      (ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (wE_nonneg hθ))
  have hintA2 : MeasureTheory.Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 4
      * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
    · exact hW4c.aestronglyMeasurable.mul hAmeas
    · exact Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hAnon ξ)
    · rw [hlimA2]
      exact ENNReal.ofReal_ne_top
  have hintD : MeasureTheory.Integrable (fun ξ : ℝ => ∫ θ in Iθ,
      ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
    · exact hDmeas
    · exact Eventually.of_forall hDnon
    · rw [hlimD]
      exact ENNReal.ofReal_ne_top
  have hcs := integral_mul_le_sqrt_mul
    (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2
      * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
    (fun ξ : ℝ => Real.sqrt (∫ θ in Iθ,
      ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))
    (fun ξ => mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    (fun ξ => Real.sqrt_nonneg _)
    (by
      refine hintA2.congr (Eventually.of_forall fun ξ => ?_)
      show (2 * Real.pi * ξ) ^ 4 * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ
        = ((2 * Real.pi * ξ) ^ 2
          * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) ^ 2
      have hsq : (Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) ^ 2
          = ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ := Real.sq_sqrt (hAnon ξ)
      calc (2 * Real.pi * ξ) ^ 4 * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ
          = (2 * Real.pi * ξ) ^ 4
              * (Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) ^ 2 := by rw [hsq]
        _ = ((2 * Real.pi * ξ) ^ 2
              * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) ^ 2 := by ring)
    (by
      refine hintD.congr (Eventually.of_forall fun ξ => ?_)
      show ∫ θ in Iθ, ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ
        = (Real.sqrt (∫ θ in Iθ,
          ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)) ^ 2
      rw [Real.sq_sqrt (hDnon ξ)])
  have h1sq : (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2
        * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) ^ 2)
      = ∫ p in Set.univ ×ˢ Iθ,
          (pz (pz g) p.1 p.2) ^ 2 * wE p.2 := by
    have h : (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2
          * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) ^ 2)
        = ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 4
            * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show ((2 * Real.pi * ξ) ^ 2
            * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) ^ 2
          = (2 * Real.pi * ξ) ^ 4 * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ
        rw [mul_pow, Real.sq_sqrt (hAnon ξ)]
        ring)
    rw [h]
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp ?_
    · exact integral_nonneg fun ξ => mul_nonneg (by positivity) (hAnon ξ)
    · exact hP2nn
    · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintA2
        (Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hAnon ξ))]
      exact hlimA2
  have h2sq : (∫ ξ : ℝ, (Real.sqrt (∫ θ in Iθ,
        ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)) ^ 2)
      = ∫ p in Set.univ ×ˢ Iθ,
          (pth (pth g) p.1 p.2) ^ 2 * wE p.2 := by
    have h : (∫ ξ : ℝ, (Real.sqrt (∫ θ in Iθ,
          ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)) ^ 2)
        = ∫ ξ : ℝ, ∫ θ in Iθ,
            ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show (Real.sqrt (∫ θ in Iθ,
            ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)) ^ 2
          = ∫ θ in Iθ,
            ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ
        rw [Real.sq_sqrt (hDnon ξ)])
    rw [h]
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp ?_
    · exact integral_nonneg fun ξ => hDnon ξ
    · exact hQ2nn
    · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintD
        (Eventually.of_forall fun ξ => hDnon ξ)]
      exact hlimD
  have hcs' : (∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2
        * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
            * (∫ θ in Iθ,
                ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)))
      ≤ Real.sqrt ((∫ p in Set.univ ×ˢ Iθ,
              (pz (pz g) p.1 p.2) ^ 2 * wE p.2)
          * (∫ p in Set.univ ×ˢ Iθ,
              (pth (pth g) p.1 p.2) ^ 2 * wE p.2)) := by
    have hL : (∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2
          * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ,
                  ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)))
        = ∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2
              * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
            * Real.sqrt (∫ θ in Iθ,
                ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ) :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show (2 * Real.pi * ξ) ^ 2
            * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ,
                  ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))
          = ((2 * Real.pi * ξ) ^ 2
                * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
              * Real.sqrt (∫ θ in Iθ,
                  ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)
        rw [Real.sqrt_mul (hAnon ξ)]
        ring)
    rw [hL]
    have h := hcs.2
    rw [h1sq, h2sq] at h
    exact h
  have hptw : ∀ ξ : ℝ,
      ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
          * ∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wA α θ)
        ≤ ENNReal.ofReal Cc * (ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
              * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
          + ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
              * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
                  * (∫ θ in Iθ,
                      ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)))) := by
    intro ξ
    have hW0 : (0 : ℝ) ≤ (2 * Real.pi * ξ) ^ 2 := sq_nonneg _
    have hAξ : 0 ≤ ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ := hAnon ξ
    have hkey : (2 * Real.pi * ξ) ^ 2
          * (∫ θ in Iθ, ‖slice (pth g) ξ θ‖ ^ 2 * wA α θ)
        ≤ Cc * ((2 * Real.pi * ξ) ^ 2 * (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
          + (2 * Real.pi * ξ) ^ 2 * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ,
                  ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))) := by
      have h1 := mul_le_mul_of_nonneg_left (hξA ξ) hW0
      refine h1.trans (le_of_eq ?_)
      ring
    refine (ENNReal.ofReal_le_ofReal hkey).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (le_of_lt hCcpos),
      ENNReal.ofReal_add (mul_nonneg hW0 hAξ) (mul_nonneg hW0 (Real.sqrt_nonneg _))]
  have hpair_int : MeasureTheory.Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2
      * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
          * (∫ θ in Iθ,
              ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))) :=
    hcs.1.congr (Eventually.of_forall fun ξ => by
      show ((2 * Real.pi * ξ) ^ 2
              * Real.sqrt (∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ))
            * Real.sqrt (∫ θ in Iθ,
                ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)
          = (2 * Real.pi * ξ) ^ 2
              * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
                  * (∫ θ in Iθ,
                      ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ))
      rw [Real.sqrt_mul (hAnon ξ)]
      ring)
  have hpair_nn : ∀ ξ : ℝ, 0 ≤ (2 * Real.pi * ξ) ^ 2
      * Real.sqrt ((∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)
          * (∫ θ in Iθ,
              ‖slice (pth (pth g)) ξ θ‖ ^ 2 * wE θ)) :=
    fun ξ => mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hAmeas2 : AEMeasurable (fun ξ : ℝ => ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2
      * ∫ θ in Iθ, ‖slice g ξ θ‖ ^ 2 * wE θ)) (MeasureTheory.volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hW2m.aemeasurable.mul hAmeas.aemeasurable)
  have hmain : (∫⁻ p in Set.univ ×ˢ Iθ,
        ENNReal.ofReal ((pz (pth g) p.1 p.2) ^ 2 * wA α p.2))
      ≤ ENNReal.ofReal (Cc * ((∫ p in Set.univ ×ˢ Iθ,
              (pz g p.1 p.2) ^ 2 * wE p.2)
          + Real.sqrt ((∫ p in Set.univ ×ˢ Iθ,
                (pz (pz g) p.1 p.2) ^ 2 * wE p.2)
              * (∫ p in Set.univ ×ˢ Iθ,
                  (pth (pth g) p.1 p.2) ^ 2 * wE p.2)))) := by
    rw [hL1]
    refine (lintegral_mono hptw).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hAmeas2,
      ENNReal.ofReal_mul (le_of_lt hCcpos),
      ENNReal.ofReal_add hPnn (Real.sqrt_nonneg _)]
    refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
    · exact le_of_eq hlimA
    · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpair_int
        (Eventually.of_forall hpair_nn)]
      exact ENNReal.ofReal_le_ofReal hcs'
  exact hmain

end

end Work.FTS.EllSol.FlatFT
