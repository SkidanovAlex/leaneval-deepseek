import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.AeI1Fts.HardyOpenAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Auxiliary facts -/

/-- The level-`0` `ℋ`-integrand is the weighted square of the function. -/
theorem hkIntegrand_zero_eq_of_mem (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigE θ := by
  rw [Work.FTS.EllipticEst.TT.AeI1.HkIntegrand_zero_eq α f hθ]
  rfl

/-- **Pointwise equality of the level-`0` integrands** on the domain, from agreement of the
functions on the open quadrant. -/
theorem HkIntegrand_zero_congr (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ = Work.Spaces.HkIntegrand α 0 g z θ := by
  rw [hkIntegrand_zero_eq_of_mem α f hθ, hkIntegrand_zero_eq_of_mem α g hθ]
  by_cases hw : Work.Spaces.w z = 0
  · rw [hw]; ring
  by_cases hs : sigE θ = 0
  · rw [hs]; ring
  have hzpos : 0 < z := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
    · exact absurd (by rw [← h0, Work.FTS.EllipticEst.TT.AeI1.w_eq_zero_at_zero]) hw
    · exact h0
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    intro hsin0
    apply hs
    rw [sigE, hsin0,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
  have hθ0 : θ ≠ 0 := by
    intro h; exact hsin (by rw [h]; norm_num)
  have hθπ : θ ≠ Real.pi / 2 := by
    intro h
    exact hsin (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
  have hθIoo : 0 < θ ∧ θ < Real.pi / 2 :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθπ⟩
  rw [heq z θ hzpos hθIoo.1 hθIoo.2]

/-- **`HkMem` is invariant under equality on the open quadrant.** -/
theorem HkMem_zero_congr {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hf : Work.Spaces.HkMem α 0 f) : Work.Spaces.HkMem α 0 g := by
  refine ⟨fun z hz => ?_, ?_⟩
  · exact (hf.1 z hz).congr_fun (fun θ hθ => HkIntegrand_zero_congr α heq hz hθ)
      measurableSet_Icc
  · exact (hf.2).congr_fun (fun z hz =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ hθ => HkIntegrand_zero_congr α heq hz hθ)) measurableSet_Ici

/-- The slice derivative of `U u = z ∂_z u` is `V u = z ∂_z ∂_θ u` on the open quadrant. -/
theorem slice_deriv_eq {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ}
    (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Iθo) :
    deriv (fun θ' => U u z θ') θ = V u z θ := by
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
  have hcl := Work.Spaces.pz_pth_comm (f := u) hcd2
  have hcd1 : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.pz u z θ') Iθo := by
    refine (hS.pz.curry_θ hz).of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have hdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz u z θ') θ :=
    (hcd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  calc deriv (fun θ' => U u z θ') θ
      = deriv (fun θ' => z * Work.Spaces.pz u z θ') θ := rfl
    _ = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ := deriv_const_mul z hdiff
    _ = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth u) z θ := by rw [hcl]
    _ = V u z θ := rfl

/-! ## The per-slice bound -/

/-- **The per-slice bound.**  For a slice `z > 0` whose two endpoint traces vanish and for which
`V u z ·` is weighted-square-integrable, the `N`-integrand of the slice is integrable and
dominated by the `V`-energy of the slice, with the constant `40000`. -/
theorem slice_bound {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hV : Work.Spaces.HkMem α 0 (V u)) {z : ℝ} (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => U u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto (fun θ => U u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    MeasureTheory.IntegrableOn
        (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo
      ∧ (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
        ≤ 40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hzmem : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.EllipticEst.TT.AeI1.w_pos_of_pos hz
  -- the `C¹` slice
  have hcd : ContDiffOn ℝ 1 (fun θ => U u z θ) Iθo := by
    refine (hS.Dz.curry_θ hz).of_le ?_
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  have haem : AEMeasurable (fun θ => U u z θ) (volume.restrict Iθo) :=
    hcd.continuousOn.aemeasurable measurableSet_Ioo
  -- integrability of the `V`-energy of the slice
  have hintV : MeasureTheory.IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Iθo := by
    have h1' : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (V u) z θ) Work.Spaces.Iθ := hV.1 z hzmem
    have h2' : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.w z) ^ 2 * ((V u z θ) ^ 2 * sigE θ)) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h1' (fun θ hθ => ?_) measurableSet_Icc
      show Work.Spaces.HkIntegrand α 0 (V u) z θ = (Work.Spaces.w z) ^ 2 * ((V u z θ) ^ 2 * sigE θ)
      rw [hkIntegrand_zero_eq_of_mem α (V u) hθ]
      ring
    have h4' : MeasureTheory.IntegrableOn
        (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.w z) ^ 2 * ((V u z θ) ^ 2 * sigE θ))) Work.Spaces.Iθ :=
      MeasureTheory.Integrable.const_mul h2' _
    have h3' : MeasureTheory.IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h4' (fun θ _ => ?_) measurableSet_Icc
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hwpos)), one_mul]
    exact (MeasureTheory.integrableOn_congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))).mpr h3'
  have hVnn : ∀ θ ∈ Iθo, 0 ≤ (V u z θ) ^ 2 * sigE θ := by
    intro θ hθ
    refine mul_nonneg (sq_nonneg _) ?_
    rw [sigE]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hBnn : 0 ≤ ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo hVnn
  -- the two facts about the constant
  have hKnn : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
      * (4 / (1 + Work.Spaces.eta) ^ 2) := by
    have h2'' : (0 : ℝ) ≤ 2 ^ Work.Spaces.eta :=
      Real.rpow_nonneg (by norm_num) _
    have h3'' : (0 : ℝ) ≤ 4 / (1 + Work.Spaces.eta) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) h2'') h3''
  have hKle : (Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
      * (4 / (1 + Work.Spaces.eta) ^ 2) ≤ 40000 := by
    have h1'' : (Real.pi / 4) ^ (2 + Work.Spaces.eta) ≤ 1 := by
      refine Real.rpow_le_one (by positivity) ?_ (by linarith [hη0])
      rw [div_le_one (by norm_num : (0 : ℝ) < 4)]
      linarith [Real.pi_lt_four]
    have h2'' : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
      calc (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hη1)
        _ = 2 := Real.rpow_one 2
    have h3'' : 4 / (1 + Work.Spaces.eta) ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hη0]
    have h1''' : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta) :=
      Real.rpow_nonneg (by positivity) _
    have h2''' : (0 : ℝ) ≤ (2 : ℝ) ^ Work.Spaces.eta := Real.rpow_nonneg (by norm_num) _
    have h3''' : (0 : ℝ) ≤ 4 / (1 + Work.Spaces.eta) ^ 2 := by positivity
    calc (Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
          * (4 / (1 + Work.Spaces.eta) ^ 2)
        ≤ 1 * 2 * 4 :=
          mul_le_mul (mul_le_mul h1'' h2'' h2''' (by norm_num)) h3'' h3''' (by norm_num)
      _ = 8 := by norm_num
      _ ≤ 40000 := by norm_num
  -- the `∫⁻`-bound
  have hpow := powerHardySinOpen hη0 hη1 haem hcd h0 h1
  have hR : (∫⁻ θ in Iθo, ENNReal.ofReal
        ((deriv (fun θ' => U u z θ') θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      = ENNReal.ofReal (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintV
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hVnn)]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [slice_deriv_eq hS hz hθ]
    simp only [sigE]
  have hmain : (∫⁻ θ in Iθo, ENNReal.ofReal
        ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
      ≤ ENNReal.ofReal (40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) := by
    calc (∫⁻ θ in Iθo, ENNReal.ofReal
          ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
        ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
            * (4 / (1 + Work.Spaces.eta) ^ 2))
          * (∫⁻ θ in Iθo, ENNReal.ofReal
              ((deriv (fun θ' => U u z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
          simpa only [sig2] using hpow
      _ = ENNReal.ofReal ((Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
            * (4 / (1 + Work.Spaces.eta) ^ 2))
          * ENNReal.ofReal (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by rw [hR]
      _ = ENNReal.ofReal (((Real.pi / 4) ^ (2 + Work.Spaces.eta) * 2 ^ Work.Spaces.eta
            * (4 / (1 + Work.Spaces.eta) ^ 2))
          * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) := (ENNReal.ofReal_mul hKnn).symm
      _ ≤ ENNReal.ofReal (40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKle hBnn)
  have hfin : (∫⁻ θ in Iθo, ENNReal.ofReal
      ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)) < ⊤ :=
    lt_of_le_of_lt hmain ENNReal.ofReal_lt_top
  -- a.e. strong measurability of the slice integrand
  have hcont_sig2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      Iθo :=
    (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by linarith only [hθ.1]) (by linarith only [hθ.2, Real.pi_pos]))))
  have haesm : AEStronglyMeasurable
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (volume.restrict Iθo) := by
    have h1'' : AEStronglyMeasurable (fun θ => (U u z θ) ^ 2) (volume.restrict Iθo) :=
      (hcd.continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioo
    have h2'' : AEStronglyMeasurable (fun θ => (Real.cos (2 * θ)) ^ 2)
        (volume.restrict Iθo) :=
      (((by fun_prop : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Iθo).pow 2)).aestronglyMeasurable
        measurableSet_Ioo
    have h3'' : AEStronglyMeasurable (fun θ => sig2 θ) (volume.restrict Iθo) := by
      have hh : (fun θ => sig2 θ)
          = fun θ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
        funext θ; rw [sig2]
      rw [hh]
      exact hcont_sig2.aestronglyMeasurable measurableSet_Ioo
    exact (h1''.mul h2'').mul h3''
  have hnnslice : ∀ θ ∈ Iθo, 0 ≤ (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ := by
    intro θ hθ
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
    rw [sig2]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hnn : 0 ≤ᵐ[volume.restrict Iθo]
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hnnslice
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo :=
    ⟨haesm, (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mpr hfin⟩
  refine ⟨hint, ?_⟩
  have htoReal : (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      = (∫⁻ θ in Iθo, ENNReal.ofReal
          ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)).toReal := by
    have h1'' := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
    have h2'' := congrArg ENNReal.toReal h1''
    rwa [ENNReal.toReal_ofReal
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioo hnnslice)] at h2''
  calc (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      = (∫⁻ θ in Iθo, ENNReal.ofReal
          ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)).toReal := htoReal
    _ ≤ (ENNReal.ofReal (40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) :=
        ENNReal.toReal_ofReal (by positivity)

/-! ## The target -/

theorem N_bound {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u)) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
            * Work.FTS.EllipticEst.AeI1Fts.sig2 θ) (Set.Ioo 0 (Real.pi / 2)))
      ∧ (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
              * Work.FTS.EllipticEst.AeI1Fts.sig2 θ)
        ≤ 40000 * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the two honesties feeding the trace lemma
  have hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  have hMix : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) := by
    refine HkMem_zero_congr (α := α) (f := V u)
      (g := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ?_ hV
    intro z θ hz hθ0 hθπ
    show z * Work.Spaces.pz (Work.Spaces.pth u) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz u) z θ
    exact congrArg (fun t => z * t) (Work.Spaces.pz_pth_comm (f := u)
      ((h.smooth 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθπ⟩))))
  have htr := Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk α u G h hU hMix
  -- the a.e. slice bound
  have hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
        ≤ 40000 * (∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by
    filter_upwards [htr, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hztr hz
    exact (slice_bound hS hV hz hztr.1 hztr.2).2
  -- integrability of the weighted `V`-energy
  have hBint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)
      (Set.Ioi 0) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (V u) z θ)
        Work.Spaces.Iz := hV.2
    have h2 : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (V u z θ) ^ 2 * sigE θ)
        Work.Spaces.Iz := by
      refine MeasureTheory.IntegrableOn.congr_fun h1 (fun z _ => ?_) measurableSet_Ici
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [hkIntegrand_zero_eq_of_mem α (V u) hθ]
      ring
    have h3 : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)
        Work.Spaces.Iz := by
      refine MeasureTheory.IntegrableOn.congr_fun h2 (fun z _ => ?_) measurableSet_Ici
      congr 1
      exact (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))).symm
    exact h3.mono_set (fun z hz =>
      show z ∈ Work.Spaces.Iz from Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz)))
  constructor
  · filter_upwards [htr, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hztr hz
    exact (slice_bound hS hV hz hztr.1 hztr.2).1
  · by_cases hInt : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
          (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) (Set.Ioi 0)
    · have hle : (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
            (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
          ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
          (fun z => 40000 * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) := by
        filter_upwards [hsl] with z hz
        calc (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
              (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ
            ≤ (Work.Spaces.w z) ^ 2 * (40000 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) :=
              mul_le_mul_of_nonneg_left hz (sq_nonneg _)
          _ = 40000 * ((Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by
              ring
      have h2 : MeasureTheory.IntegrableOn
          (fun z => 40000 * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) (Set.Ioi 0) := hBint.const_mul 40000
      have hkey := MeasureTheory.integral_mono_ae hInt h2 hle
      rwa [MeasureTheory.integral_const_mul] at hkey
    · rw [MeasureTheory.integral_undef hInt]
      have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
          (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z _ =>
          mul_nonneg (sq_nonneg _)
            (MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
              mul_nonneg (sq_nonneg _) (by
                rw [sigE]
                exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
                  (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _))))
      have h0 := MeasureTheory.integral_nonneg_of_ae hnn
      linarith

end Work.FTS.EllipticEst.AeI1Fts
