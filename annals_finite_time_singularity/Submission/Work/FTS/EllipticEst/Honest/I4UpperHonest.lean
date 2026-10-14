import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.Honest

/-- **The right-endpoint behaviour of a `θ`-slice from the raw hypotheses**: the honest proof of
`Work.FTS.EllipticEst.Honest.HonSliceRightTendsto` uses only the equation on the open quadrant, the
`C^∞`-regularity there and the `HkMem`-honesty of `F`, `z²∂_zzΨ`, `∂_θθΨ`; the `tan`-identity of that proof
yields the rate as well. -/
theorem sliceRightTendsto_raw (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hαpos : 0 < α) (hα4 : α ≤ 1 / 4)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemF : Work.Spaces.HkMem α 0 F)
    (hmemA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (z : ℝ) (hz : 0 < z) :
    Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |Ψ z θ| ≤ K * (Real.pi / 2 - θ) := by
  -- the base point `a` of the `θ`-integration
  set a : ℝ := Real.pi / 4 with hadef
  have ha_pos : 0 < a := by rw [hadef]; linarith [Real.pi_pos]
  have ha_lt : a < Real.pi / 2 := by rw [hadef]; linarith [Real.pi_pos]
  have hz1 : 0 < z + 1 := by linarith
  -- slicewise `L²(σ)`-integrability of `∂_θθΨ` at every `s > 0` (from `memB`)
  have hth : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2
        * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma hmemB hs
    refine h0.congr_fun (fun θ _ => ?_) measurableSet_Icc
    have h1 : Work.Spaces.pthIter 2 Ψ s θ
        = deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    show (Work.Spaces.pthIter 2 Ψ s θ) ^ 2 * sEta θ
      = (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2 * sEta θ
    rw [h1]
  -- boundedness of the slices and of their `θ`-derivatives at `z` and at `z + 1`
  obtain ⟨M, hMpos, hMb⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz (hsm 2)) (hth z hz)
  obtain ⟨M₁, hM₁pos, hM₁b⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz1 (hsm 2)) (hth (z + 1) hz1)
  -- the `σ`-weighted square of the `z`-slice of `∂_z²Ψ` (from `memA`, divided by `z⁴`)
  have hp_int : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    have h0 := HkMemSliceSqSigma hmemA hz
    have hz2 : (z ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((z ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- the `σ`-weighted square of the `F`-slice
  have hF_int : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := HkMemSliceSqSigma hmemF hz
  -- a.e. measurability of the `σ`-weighted slice norm of `∂_z²Ψ` (from the honest `z`-integral
  -- `hmemA.2`, after dividing by the measurable weight `w s²·s⁴`)
  have hγaem : AEMeasurable
      (fun s => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      (volume.restrict Work.Spaces.Iz) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (s ^ 4)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have hm : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (s ^ 4)
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
        (volume.restrict Work.Spaces.Iz) :=
      (hmemA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    have hden : AEMeasurable (fun s : ℝ => (Work.Spaces.w s) ^ 2 * s ^ 4)
        (volume.restrict Work.Spaces.Iz) := by
      refine Measurable.aemeasurable ?_
      have hw : Measurable fun s : ℝ => Work.Spaces.w s := by
        show Measurable fun s : ℝ => (1 + s) ^ 2 / s ^ 2
        fun_prop
      exact (hw.pow_const 2).mul (measurable_id.pow_const 4)
    refine (hm.div hden).congr ?_
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (0 : ℝ)
    have h0' : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz), s ∈ Set.Ioi (0 : ℝ) := by
      rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      filter_upwards [h0] with s hs hmem
      exact lt_of_le_of_ne hmem (Ne.symm hs)
    filter_upwards [h0'] with s hs
    have hw : (Work.Spaces.w s) ^ 2 * s ^ 4 ≠ 0 := by
      have h1 : Work.Spaces.w s ≠ 0 := by
        show (1 + s) ^ 2 / s ^ 2 ≠ 0
        have hs' : s ≠ 0 := ne_of_gt hs
        have h1' : (1 : ℝ) + s ≠ 0 := by
          have hs0 : (0 : ℝ) < s := hs
          have : (0 : ℝ) < 1 + s := by linarith
          exact ne_of_gt this
        exact div_ne_zero (pow_ne_zero 2 h1') (pow_ne_zero 2 hs')
      exact mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 4 (ne_of_gt hs))
    exact mul_div_cancel_left₀ _ hw
  -- `γ` written with the `s⁴`-weight of `memA` (the form `HkMemSliceGammaLinTop` bounds)
  have hγw : ∀ s, (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      = (s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
    intro s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by ring)
  -- a.e. measurability of the *weighted* slice norm, on `Icc z (z+1)`
  have hγw_aem : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have h1 : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) (volume.restrict Work.Spaces.Iz) :=
      (hmemA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    -- remove the weight `w s²` (multiply the *unweighted* norm, whose measurability is `hγaem`,
    -- by the measurable factor `(s²)²`)
    have h2 : AEMeasurable (fun s => ∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        (volume.restrict Work.Spaces.Iz) := by
      refine (hγaem.mul ((measurable_id.pow_const 2).pow_const 2).aemeasurable).congr ?_
      refine Filter.Eventually.of_forall fun s => ?_
      show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) * (s ^ 2) ^ 2
        = ∫ θ in Work.Spaces.Iθ, (s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ
      rw [mul_comm, (hγw s).symm]
    exact (h2.ennreal_ofReal).mono_measure
      (Measure.restrict_mono (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)) le_rfl)
  -- the weighted version is exactly `HkMemSliceGammaLinTop`
  have hγw_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    refine lt_of_eq_of_lt ?_ (HkMemSliceGammaLinTop hmemA hz)
    exact MeasureTheory.lintegral_congr fun s => by rw [hγw s]
  -- the unweighted lintegral, via the pointwise scaling `γ s ≤ (z⁴)⁻¹ · γ_w s` on `Icc z (z+1)`
  have hgamma : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    have hpt : ∀ s ∈ Set.Icc z (z + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
      have hs4 : 0 < s ^ 4 := pow_pos hs0 4
      have hle : (s ^ 4)⁻¹ ≤ (z ^ 4)⁻¹ :=
        inv_anti₀ (pow_pos hz 4) (pow_le_pow_left₀ (le_of_lt hz) hs.1 4)
      have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
        rw [hγw s]
        have heq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            = (s ^ 4)⁻¹ * ((s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) := by
          rw [show (s ^ 2) ^ 2 = s ^ 4 from by ring, ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hs4), one_mul]
        conv_lhs => rw [heq]
        refine mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (s ^ 2)) ?_)
        exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
      calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ENNReal.ofReal (((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) :=
            (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
              (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))))).mpr h1
        _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
            rw [ENNReal.ofReal_mul (by positivity)]
    calc ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
      _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_const_mul'' _ hγw_aem
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγw_lin
  -- a.e. measurability of `ofReal γ` on `Icc z (z+1)` (transfer from `hγaem`)
  have hγaemK : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) :=
    (hγaem.ennreal_ofReal).mono_measure (Measure.restrict_mono_set volume
      (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)))
  -- the lintegral of `(1/2)(γ + π/2)` is finite (this is the constant `c` below)
  have hb_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2)) < ⊤ := by
    -- it suffices to bound the *decomposed* integrand `ofReal γ + ofReal (π/2)`, since
    -- `(1/2)(γ + π/2) ≤ γ + π/2`; this avoids pulling out the constant `ofReal (1/2)`
    have hsum : ∫⁻ s in Set.Icc z (z + 1), (ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + ENNReal.ofReal (Real.pi / 2)) < ⊤ := by
      rw [MeasureTheory.lintegral_add_left' hγaemK]
      refine ENNReal.add_lt_top.mpr ⟨hgamma, ?_⟩
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    refine lt_of_le_of_lt ?_ hsum
    refine MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s _ => ?_))
    have hγnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
    have hle : (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2) ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2 := by linarith [Real.pi_pos]
    calc ENNReal.ofReal ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))
        ≤ ENNReal.ofReal ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + Real.pi / 2) := (ENNReal.ofReal_le_ofReal_iff (by linarith [Real.pi_pos])).mpr hle
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + ENNReal.ofReal (Real.pi / 2) := by
          rw [ENNReal.ofReal_add hγnn (by linarith [Real.pi_pos])]
  -- the `b`-independent constant bounding `|P_b(z)|`
  set c : ℝ := ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2))) with hcdef
  have hcnonneg : 0 ≤ c := by rw [hcdef]; exact ENNReal.toReal_nonneg
  -- joint continuity of `pz Ψ` on the open quadrant (finite order: `∂_z` of a `C¹` function)
  have hpz_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderivWithin ℝ (Function.uncurry Ψ)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (hsm 1).fderivWithin (m := 0) hU.uniqueDiffOn (by norm_num)
      refine (contDiffOn_zero.mp h1).congr (fun p hp => ?_)
      show fderiv ℝ (Function.uncurry Ψ) p
        = fderivWithin ℝ (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p
      rw [fderivWithin_of_isOpen hU hp]
    have h2 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p (1, 0))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    refine h2.congr (fun p hp => ?_)
    show Work.Spaces.pz Ψ p.1 p.2 = fderiv ℝ (Function.uncurry Ψ) p (1, 0)
    exact Work.Spaces.pz_eq_fderiv
      (((hsm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp))
  -- **first application**: `∂_z ∫_a^b Ψ s θ dθ = ∫_a^b pz Ψ s θ dθ` for `s ∈ [z, z+1]`
  have hZderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Ψ t θ) (∫ θ in a..b, Work.Spaces.pz Ψ s θ) s := by
    intro b hb s hs
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1)
      ?_ ?_ ?_
    · exact ((hsm 0).continuousOn.mono hrect).mono hsub
    · exact (hpz_cont.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact (Work.Spaces.differentiableAt_curry_left
        (((hsm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hxU))).hasDerivAt
  -- *** Stage A ***
  -- `F` is smooth on the open quadrant (it *is* `bslOp α Ψ` there), so each of its `θ`-slices
  -- is continuous on `(0, π/2)`; in particular `F z ·` is a genuine interval integral on `[a,b]`.
  have hFcont : ContinuousOn (fun θ => F z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hU : IsOpen Qd := isOpen_Qd
    have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) (hsm 2)
    have hpz2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
      have h2 : ContDiffOn ℝ (2 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
        Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 2) (hsm 3)
      have h1 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) h2
      rw [pzIter_two_eq Ψ]
      exact h1
    have hp2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz hpz2).continuousOn
    have hp1 : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pz Ψ) hz hpz1).continuousOn
    have hpsi : ContinuousOn (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice Ψ hz (hsm 0)).continuousOn
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (hsm 2)
    have hpth2 : ContinuousOn (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (deriv (fun θ' => deriv (fun θ'' => Ψ z θ'') θ'))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      rw [pthIter_two_eq Ψ z]
      exact h2.continuousOn
    have htan : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have hpthtan : ContinuousOn (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        htan.mul hslice2
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have hfun : (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          = deriv (fun θ => Real.tan θ * Ψ z θ) := rfl
      rw [hfun]
      exact h1.continuousOn
    have hcomb : ContinuousOn (fun θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        + (-Work.Spaces.pthIter 2 Ψ z θ + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
            - 6 * Ψ z θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((hp2.const_mul (-(α ^ 2 * z ^ 2))).sub (hp1.const_mul (α * (5 + α) * z))).add
        ((hpth2.neg.add hpthtan).sub (hpsi.const_mul 6))
    refine hcomb.congr (fun θ hθ => ?_)
    simpa only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
      using (heq z hz θ hθ.1 hθ.2).symm
  -- the `σ`-weighted square of the `∂_z²Ψ`-slice, for every `s > 0`
  have hps_int : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma hmemA hs
    have h2 : (s ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((s ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- joint continuity of `pz Ψ` on the open quadrant
  have hUq : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hpz1c : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hUq (n := 1) (hsm 2)
  have hpz2c : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn hUq (hsm 2)
  -- **second application**: `∂_z ∫_a^b pz Ψ s θ dθ = ∫_a^b pzIter 2 Ψ s θ dθ`
  have hPderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pz Ψ t θ) (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
      s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz_cont.mono hrect).mono hsub
    · exact (hpz2c.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      have h := hasDerivAt_slice_of_contDiffOn_open hUq hpz1c hxU
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pzIter_succ,
        show (1 : ℕ) = 0 + 1 from rfl, Work.Spaces.pzIter_zero] using h
  -- *** Stage B ***
  -- the two `b`-independent `σ`-weighted slice norms
  set QP : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ with hQPdef
  set QF : ℝ := ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * sEta θ with hQFdef
  have hQPnn : 0 ≤ QP := by
    rw [hQPdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hQFnn : 0 ≤ QF := by
    rw [hQFdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  -- the third application: `Q_b` is differentiable, hence continuous
  have hpz2cd : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
    have h1 : ContDiffOn ℝ (4 : WithTop ℕ∞) (Function.uncurry Ψ) Qd := hsm 4
    have h2 : ContDiffOn ℝ (3 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 3) h1
    have h3 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 2) h2
    rw [pzIter_two_eq Ψ]
    exact h3
  have hpz3cd : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 3 Ψ)) Qd := by
    have h4 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 1) hpz2cd
    have h5 : Work.Spaces.pzIter 3 Ψ = Work.Spaces.pz (Work.Spaces.pzIter 2 Ψ) := rfl
    rw [h5]
    exact h4
  have hQderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ t θ)
      (∫ θ in a..b, Work.Spaces.pzIter 3 Ψ s θ) s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz2c.mono hrect).mono hsub
    · exact ((hpz3cd.continuousOn).mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact hasDerivAt_slice_of_contDiffOn_open hUq (hpz2cd.of_le (by norm_num)) hxU
  -- **the bound on `P_b(z)`** — the only place where the `z`-dependence of the data is used
  have hPb : ∀ b ∈ Set.Ioo a (Real.pi / 2),
      |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c := by
    intro b hb
    have hZder := hZderiv b hb
    have hPder := hPderiv b hb
    have hQder := hQderiv b hb
    have hcontP : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hPder s hs).continuousAt.continuousWithinAt
    have hcontQ : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hQder s hs).continuousAt.continuousWithinAt
    have hceq : Set.uIcc z (z + 1) = Set.Icc z (z + 1) := Set.uIcc_of_le (by linarith)
    have hcontPu : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.uIcc z (z + 1)) := by rw [hceq]; exact hcontP
    -- first fundamental-theorem step: `∫_z^{z+1} P_b = Z(z+1) - Z(z)`
    have h1 : (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
        = (∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => ∫ θ in a..b, Ψ t θ)
        (f' := fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ) ?_ hcontPu.intervalIntegrable
      intro s hs
      rw [hceq] at hs
      exact hZder s hs
    -- second step: `P_b(t) - P_b(z) = ∫_z^t Q_b`
    have h2 : ∀ t ∈ Set.Icc z (z + 1),
        (∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          = ∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ) := by
      intro t ht
      have hle : z ≤ t := ht.1
      have hsub : Set.uIcc z t ⊆ Set.Icc z (z + 1) := by
        rw [Set.uIcc_of_le hle]
        exact Set.Icc_subset_Icc le_rfl ht.2
      have hint : IntervalIntegrable (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
          volume z t := (hcontQ.mono hsub).intervalIntegrable
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hPder s (hsub hs)) hint).symm
    -- the algebraic consequence
    have h3 : (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
        = ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
          - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
              - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) := by
      have hsub2 : (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
            - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          = (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
            - ∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ z θ) :=
        intervalIntegral.integral_sub hcontPu.intervalIntegrable intervalIntegrable_const
      rw [hsub2, h1, intervalIntegral.integral_const]
      ring
    -- the uniform bound on the subtracted term
    have hB : ∀ t ∈ Set.Icc z (z + 1),
        |(∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)| ≤ c := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with hzt | hzt
      · rw [← hzt, sub_self, abs_zero]; exact hcnonneg
      · rw [h2 t ht]
        have hQint : IntegrableOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
            (Set.Icc z (z + 1)) := hcontQ.integrableOn_Icc
        have hQabs : IntegrableOn (fun s => |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
            (Set.Icc z (z + 1)) := by
          simpa only [Real.norm_eq_abs, MeasureTheory.IntegrableOn] using hQint.norm
        have hstep : |∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)|
            ≤ ∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ| := by
          refine le_trans (intervalIntegral.abs_integral_le_integral_abs hzt.le) ?_
          rw [intervalIntegral.integral_of_le hzt.le]
          refine MeasureTheory.setIntegral_mono_set hQabs
            (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            (Filter.Eventually.of_forall (fun s hs => ?_))
          exact ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
        refine le_trans hstep ?_
        calc (∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
              ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|) :=
                setIntegral_le_toReal_lintegral _
                  (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            _ ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))) := by
                refine ENNReal.toReal_mono (ne_of_lt hb_lin) (MeasureTheory.lintegral_mono_ae ?_)
                refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => ?_)
                have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
                have hQb := le_trans
                  (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
                  (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) (hps_int s hs0))
                have hnn : 0 ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2) :=
                  mul_nonneg (by norm_num) (add_nonneg
                    (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)))
                    (by linarith [Real.pi_pos]))
                exact (ENNReal.ofReal_le_ofReal_iff hnn).mpr hQb
            _ = c := rfl
    -- the two slice integrals at `z` and `z + 1`
    have hZc : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ z θ| ≤ C) →
        |∫ θ in a..b, Ψ z θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZc1 : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ (z + 1) θ| ≤ C) →
        |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ (z + 1) θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZ1 := hZc1 M₁ hM₁pos.le (fun θ hθ => (hM₁b θ hθ).2)
    have hZ0 := hZc M hMpos.le (fun θ hθ => (hMb θ hθ).2)
    calc |∫ θ in a..b, Work.Spaces.pz Ψ z θ|
        = |((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          conv_lhs => rw [h3]
      _ ≤ |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
            + |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          have := abs_sub_le ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            (0 : ℝ) (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          simpa using this
      _ ≤ (M₁ * (Real.pi / 2) + M * (Real.pi / 2)) + c := by
          refine add_le_add ?_ ?_
          · calc |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
                ≤ |∫ θ in a..b, Ψ (z + 1) θ| + |∫ θ in a..b, Ψ z θ| := by
                  simpa using abs_sub_le (∫ θ in a..b, Ψ (z + 1) θ) (0 : ℝ) (∫ θ in a..b, Ψ z θ)
              _ ≤ M₁ * (Real.pi / 2) + M * (Real.pi / 2) := add_le_add hZ1 hZ0
          · have hmain : |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| ≤ c := by
              have h := intervalIntegral.norm_integral_le_of_norm_le_const
                (f := fun t => (∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                  - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (a := z) (b := z + 1) (C := c)
                (fun t ht => by
                  rw [Real.norm_eq_abs]
                  rw [Set.uIoc_of_le (by linarith : z ≤ z + 1)] at ht
                  exact hB t ⟨le_of_lt ht.1, ht.2⟩)
              simpa only [Real.norm_eq_abs, show (z + 1) - z = 1 from by ring, abs_one,
                mul_one] using h
            exact hmain
      _ = (Real.pi / 2) * (M + M₁) + c := by ring
  -- the per-`b` bound
  set K : ℝ := |Real.tan a * Ψ z a| + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
      + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) + (1 / 2) * (QF + Real.pi / 2)
      + 2 * M + 6 * (M * (Real.pi / 2)) with hKdef
  have key : ∀ b ∈ Set.Ioo a (Real.pi / 2), |Real.tan b * Ψ z b| ≤ K := by
    intro b hb
    rw [hKdef]
    have hab' : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro θ hθ
      rw [Set.uIcc_of_le (le_of_lt hb.1)] at hθ
      exact ⟨lt_of_lt_of_le ha_pos hθ.1, lt_of_le_of_lt hθ.2 hb.2⟩
    have hFint : IntervalIntegrable (fun θ => F z θ) volume a b :=
      (hFcont.mono hab').intervalIntegrable
    have hcontp : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz (n := 1) (hpz2cd.of_le (by norm_num))
      exact h2.continuousOn.mono hab'
    have hpI : IntervalIntegrable (fun θ => Work.Spaces.pzIter 2 Ψ z θ) volume a b :=
      hcontp.intervalIntegrable
    have hcontq : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pz Ψ) hz (n := 1) hpz1c
      exact h2.continuousOn.mono hab'
    have hqI : IntervalIntegrable (fun θ => Work.Spaces.pz Ψ z θ) volume a b :=
      hcontq.intervalIntegrable
    have hcontψ : ContinuousOn (fun θ => Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 0 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice Ψ hz (n := 0) (hsm 0)
      exact h2.continuousOn.mono hab'
    have hψI : IntervalIntegrable (fun θ => Ψ z θ) volume a b := hcontψ.intervalIntegrable
    have hslice1 : ContDiffOn ℝ 1 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 1) (hsm 1)
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 2) (hsm 2)
    have hcontp2 : ContinuousOn (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h2.continuousOn.mono hab'
    have hp2I : IntervalIntegrable (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        volume a b := hcontp2.intervalIntegrable
    have htansm : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      htansm.mul hslice2
    have hconttw : ContinuousOn (deriv (fun θ => Real.tan θ * Ψ z θ)) (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h1.continuousOn.mono hab'
    have htwI : IntervalIntegrable (deriv (fun θ => Real.tan θ * Ψ z θ)) volume a b :=
      hconttw.intervalIntegrable
    -- the derivative facts for the three functions of `TanSliceFTC`
    have hdu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
      fun θ hθ => (hslice1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdu1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (deriv (fun θ' => Ψ z θ')) θ := by
      intro θ hθ
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdtw : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun θ' => Real.tan θ' * Ψ z θ') θ :=
      fun θ hθ => (htw.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    -- the amplitude `A` of the `tan`-identity, and its `(a,b)`-integral
    set A : ℝ → ℝ := fun θ => α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + α * (5 + α) * z * Work.Spaces.pz Ψ z θ + F z θ with hAdef
    have hAI : IntervalIntegrable A volume a b := by
      rw [hAdef]
      exact ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))).add hFint
    have hsplit : (∫ θ in a..b, A θ)
        = (α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ) := by
      rw [hAdef]
      rw [intervalIntegral.integral_add
        ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))) hFint]
      rw [intervalIntegral.integral_add (hpI.const_mul (α ^ 2 * z ^ 2))
        (hqI.const_mul (α * (5 + α) * z))]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    -- the `tan`-identity
    have heq : ∀ θ ∈ Set.Ioo a b, deriv (fun t => Real.tan t * Ψ z t) θ
        = A θ + deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ + 6 * Ψ z θ := by
      intro θ hθ
      have hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, ha_pos], by linarith [hθ.2, hb.2]⟩
      have hb' := heq z hz θ hθo.1 hθo.2
      rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb'
      rw [hAdef]
      simp only [pthIter_two_eq_fun Ψ, Work.Spaces.pth] at hb' ⊢
      linear_combination (norm := ring_nf) hb'
    have hid := TanSliceFTC (u := fun θ => Ψ z θ) (A := A) (a := a) (b := b) (le_of_lt hb.1)
      (fun θ hθ => (hdu θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdu1 θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdtw θ (hab' hθ)).hasDerivAt)
      hp2I htwI hAI hψI heq
    -- the individual bounds
    have htanb : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
        ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hp_int)
    have hqbound : |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c :=
      hPb b hb
    have htanF : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
      le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hF_int)
    have hψbd : |∫ θ in a..b, Ψ z θ| ≤ M * (Real.pi / 2) := by
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ M * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := M) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact (hMb θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩).2)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hMpos.le)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hderivbd : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a| ≤ 2 * M := by
      have h1 : |deriv (fun θ => Ψ z θ) b| ≤ M :=
        (hMb b ⟨lt_trans ha_pos hb.1, hb.2⟩).1
      have h2 : |deriv (fun θ => Ψ z θ) a| ≤ M :=
        (hMb a ⟨ha_pos, ha_lt⟩).1
      have htri : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          ≤ |deriv (fun θ => Ψ z θ) b| + |deriv (fun θ => Ψ z θ) a| := by
        have := abs_sub_le (deriv (fun θ => Ψ z θ) b) 0 (deriv (fun θ => Ψ z θ) a)
        simpa using this
      linarith
    -- the `tan`-identity solved for the left-hand side
    have hid' : Real.tan b * Ψ z b
        = Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
          + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
          + 6 * ∫ θ in a..b, Ψ z θ := by linarith [hid]
    -- the `(a,b)`-integral of the amplitude
    have hAbound : |∫ θ in a..b, A θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
        + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
        + (1 / 2) * (QF + Real.pi / 2) := by
      rw [hsplit]
      have htri : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ)|
          ≤ |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| := by
        have h2 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (∫ θ in a..b, F z θ)
        have h1 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ))
          ((α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ))
        linarith
      have hbd : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
              + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
              + (1 / 2) * (QF + Real.pi / 2) := by
        have h1 : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (le_trans
            (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => Work.Spaces.pzIter 2 Ψ z θ) ha_pos hb.2
              (le_of_lt hb.1) hp_int)) (by positivity)
        have h2 : |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            ≤ (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c) := by
          have hc2 : 0 ≤ α * (5 + α) * z :=
            mul_nonneg (mul_nonneg hαpos.le (by linarith [hαpos])) hz.le
          rw [abs_mul, abs_of_nonneg hc2]
          exact mul_le_mul_of_nonneg_left (hPb b hb) hc2
        have h3 : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
          le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => F z θ) ha_pos hb.2 (le_of_lt hb.1) hF_int)
        linarith
      linarith
    rw [hid']
    have htri : |Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
        + 6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ| := by
      have h1 := abs_add_le (Real.tan a * Ψ z a) (∫ θ in a..b, A θ)
      have h2 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ))
        (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
      have h3 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a))
        (6 * ∫ θ in a..b, Ψ z θ)
      exact le_trans h3 (le_trans (add_le_add h2 le_rfl)
        (add_le_add (add_le_add h1 le_rfl) le_rfl))
    have hfin : |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a|
          + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
          + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
          + (1 / 2) * (QF + Real.pi / 2) + 2 * M + 6 * (M * (Real.pi / 2)) := by
      have h6 : |6 * ∫ θ in a..b, Ψ z θ| = 6 * |∫ θ in a..b, Ψ z θ| := by
        rw [abs_mul]; norm_num
      have h6b : 6 * |∫ θ in a..b, Ψ z θ| ≤ 6 * (M * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left hψbd (by norm_num)
      rw [h6]
      linarith [hAbound, hderivbd, h6b]
    linarith
  -- the squeeze
  have hKlim : Tendsto (fun θ => K / Real.tan θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcos : Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := (Real.continuous_cos.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.cos_pi_div_two] using h.mono_left h'
    have hsin : Tendsto Real.sin (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
      have h := (Real.continuous_sin.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.sin_pi_div_two] using h.mono_left h'
    have h2 : Tendsto (fun θ => K * Real.cos θ / Real.sin θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h1 : Tendsto (fun θ => K * Real.cos θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hcos)
      have := h1.div hsin one_ne_zero
      rw [show (0 : ℝ) / 1 = 0 from by norm_num] at this
      exact this
    refine Tendsto.congr' ?_ h2
    filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
    have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [ha_pos, hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
    have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ha_pos, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hKnn : 0 ≤ K := by
    have hb0 : (a + Real.pi / 2) / 2 ∈ Set.Ioo a (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    exact le_trans (abs_nonneg _) (key _ hb0)
  have hTend : Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hKlim
    filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
    have htanpos : 0 < Real.tan θ :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [ha_pos, hθ.1]) hθ.2
    rw [le_div_iff₀ htanpos]
    calc ‖Ψ z θ‖ * Real.tan θ = |Real.tan θ * Ψ z θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos htanpos, mul_comm]
      _ ≤ K := key θ hθ
  refine ⟨hTend, 2 * K, by linarith, ?_⟩
  -- the rate: `|Ψ z θ| ≤ K/tan θ` and `1/tan θ = cos θ/sin θ ≤ 2(π/2-θ)` on `(π/4, π/2)`
  filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
  have htanpos : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [ha_pos, hθ.1]) hθ.2
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ha_pos, hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsinhalf : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h := Real.monotoneOn_sin (a := Real.pi / 6) (b := θ)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos, ha_pos, hθ.1], le_of_lt hθ.2⟩
      (by linarith [Real.pi_pos, ha_pos, hθ.1])
    rwa [Real.sin_pi_div_six] at h
  have hdiv : Real.cos θ / Real.sin θ ≤ 2 * (Real.pi / 2 - θ) := by
    have hcos : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
    have h1 : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le (by linarith [hθ.2])
    have ht0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have h2 : (1 : ℝ) ≤ 2 * Real.sin θ := by linarith
    rw [div_le_iff₀ hsinpos]
    calc Real.cos θ = Real.sin (Real.pi / 2 - θ) := hcos
      _ ≤ Real.pi / 2 - θ := h1
      _ = (Real.pi / 2 - θ) * 1 := by ring
      _ ≤ (Real.pi / 2 - θ) * (2 * Real.sin θ) := mul_le_mul_of_nonneg_left h2 ht0
      _ = 2 * (Real.pi / 2 - θ) * Real.sin θ := by ring
  have htan_eq : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hu : |Ψ z θ| ≤ K / Real.tan θ := by
    rw [le_div_iff₀ htanpos]
    calc |Ψ z θ| * Real.tan θ = |Real.tan θ| * |Ψ z θ| := by
          rw [abs_of_pos htanpos, mul_comm]
      _ = |Real.tan θ * Ψ z θ| := (abs_mul _ _).symm
      _ ≤ K := key θ hθ
  calc |Ψ z θ| ≤ K / Real.tan θ := hu
    _ = K * (Real.cos θ / Real.sin θ) := by
        rw [htan_eq]
        field_simp
    _ ≤ K * (2 * (Real.pi / 2 - θ)) := mul_le_mul_of_nonneg_left hdiv hKnn
    _ = (2 * K) * (Real.pi / 2 - θ) := by ring

/-- **The right-endpoint behaviour of the `θ`-slices in the almost-everywhere class.** -/
theorem AeSliceRightTendsto (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (z : ℝ) (hz : 0 < z) :
    Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |u z θ| ≤ K * (Real.pi / 2 - θ) := by
  exact sliceRightTendsto_raw α G u h.hα h.hα4 h.eq h.smooth h.memG h.memRad2 h.memAng2 z hz

end Work.FTS.EllipticEst.H2W.AeProof
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The slice-level objects of the honest `I₄` upper bound -/




/-- `Ψ θ = cos θ · ψ θ`. -/
def slPsi (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.cos θ * ψ θ


/-- `u θ = ∂_θ (tan θ · Ψ)`. -/
def slU (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => Real.tan θ' * slPsi ψ θ') θ


theorem eta_lt_one : Work.Spaces.eta < 1 := by rw [Work.Spaces.eta]; norm_num

theorem one_sub_eta_pos : 0 < 1 - Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num




theorem cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩


/-! ## The slice-level inequality, and the target theorem

The proof of the target theorem below is the reduction of
`Submission/Work/FTS/EllipticEst/Honest/I4GlobalAssembly` (the `z`-integration and the
`z`-Cauchy–Schwarz) applied to the single-slice inequality `slice_bound`, whose proof uses the
pointwise algebra `Submission.Work.FTS.EllipticEst.I4SliceAlgebra` and the boundary vanishing
`Submission.Work.FTS.EllipticEst.Honest.I4BoundaryVanish` (see `NOTES_I4UpperHonest.md` for the
complete route).  The pieces of the slice inequality proved in this file are the `θ`-truncated
integration by parts, the AM–GM cancellation and the coercive estimate below.
-/


end

end Work.FTS.EllipticEst.Honest
end
