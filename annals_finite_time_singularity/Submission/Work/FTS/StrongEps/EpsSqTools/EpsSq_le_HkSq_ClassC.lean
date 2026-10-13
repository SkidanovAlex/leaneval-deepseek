import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaO_open
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary `rpow` bookkeeping on `Iθ` -/

/-- `sin (2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg_Iθ_eps {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `((sin 2θ)^a)^2 = (sin 2θ)^(2a)` on `Iθ`. -/
theorem sin_rpow_sq {θ a : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ a) ^ 2 = (Real.sin (2 * θ)) ^ (2 * a) := by
  calc ((Real.sin (2 * θ)) ^ a) ^ (2 : ℕ)
      = ((Real.sin (2 * θ)) ^ a) ^ ((2 : ℕ) : ℝ) := by norm_num
    _ = (Real.sin (2 * θ)) ^ (a * ((2 : ℕ) : ℝ)) := by rw [← Real.rpow_mul hs]
    _ = (Real.sin (2 * θ)) ^ (2 * a) := by congr 1; ring

/-- **The square of the weight of the `ε`-scheme** is the `γ`-weighted square on `Iθ`:
`(epsW α z θ)² = w(z)² sin(2θ)^{-γ}`. -/
theorem epsW_sq_eq {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs := sin_two_nonneg_Iθ_eps hθ
  have hpow : ((Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) := by
    rw [sin_rpow_sq hs]
    congr 1
    ring
  rw [Work.FTS.StrongEps.epsW, div_pow, hpow, div_eq_mul_inv, ← Real.rpow_neg hs]

/-- **The square of the mixed weight** is the `γ`-weighted square on `Iθ`:
`(Wt α z θ)² = w(z)² sin(2θ)^{-γ}` (the `Iθ`-version of `Work.FTS.H2.Wt_sq`). -/
theorem Wt_sq_eq_eps {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs := sin_two_nonneg_Iθ_eps hθ
  have hpow : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sin_rpow_sq hs]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hpow]

/-! ## The two slice identities -/

/-- **The `EpsSq`-slice is `w²` times the `γ`-weighted `L²` of the slice.** -/
theorem epsSq_slice_eq (α z : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
  intro θ hθ
  simp only []
  have h1 : (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (f z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [mul_pow, epsW_sq_eq hθ]
  rw [h1]
  ring

/-- **The `(0,1)`-slot of the `ℋ⁴`-integrand is `w²` times the `2-γ`-weighted square of the
unguarded angular derivative.**  Uses `sin(2θ)^{2-γ}(∂_θ u)² = sin(2θ)^{-γ}(D_θ u)²`
(`Work.FTS.H2.pth_sq_mul_sin_eq`). -/
theorem slot_slice_eq {α z : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2 := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_
  intro θ hθ
  simp only []
  have hcomm : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by ring
  have h1 : (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
    rw [mul_pow, Wt_sq_eq_eps hθ, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero]
    rw [hcomm, Work.FTS.H2.pth_sq_mul_sin_eq α hα0 hα1 f z θ hθ]
    ring
  rw [h1]

/-- **The `pth`-form of the Hardy hypothesis at a fixed `z`**, converted from the
`(0,1)`-slot integrability. -/
theorem pth_slice_integrable {α z : ℝ} {f : ℝ → ℝ → ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 < z)
    (hslot : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2)
      Work.Spaces.Iθ := by
  have hw : Work.Spaces.w z ≠ 0 := by
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < z ^ 2 := by positivity
    rw [Work.Spaces.w]
    exact div_ne_zero (ne_of_gt h1) (ne_of_gt h2)
  refine ((hslot.const_mul ((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
  have h1 : (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
    rw [mul_pow, Wt_sq_eq_eps hθ, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero]
    rw [show (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2
        = (Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) by ring,
      Work.FTS.H2.pth_sq_mul_sin_eq α hα0 hα1 f z θ hθ]
    ring
  calc (Work.Spaces.w z ^ 2)⁻¹ * (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z ^ 2)⁻¹
        * ((Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2)) := by
          rw [h1]
    _ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2 := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hw), one_mul]

/-! ## The `(0,1)`-slot of `ℋ⁴` -/

/-- **The `(0,1)`-slot of the `ℋ⁴`-integrand is integrable in `z` and bounded by `HkSq α 4`**
(in the order `∫_z ∫_θ`). -/
theorem slot01_le_HkSq4 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 4 f := by
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed 0 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
      (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · simpa only [Function.uncurry, MeasureTheory.IntegrableOn]
      using hprod.integral_prod_left
  · rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
      hm.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hm.1 z hz) ?_
    filter_upwards with θ
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 0 (by norm_num) (by norm_num)

/-- **The `(0,1)`-slot is `θ`-integrable for almost every `z`** (from the product integrability). -/
theorem slot01_ae_integrable {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
    (by norm_num) (by norm_num)).prod_right_ae

/-- **Almost every `z` of `Iz` is positive** (`Iz = [0,∞)` and `{0}` is null). -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  have h1 : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici 0 := Ioi_ae_eq_Ici
  rw [Work.Spaces.Iz, ← Measure.restrict_congr_set h1]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- **Continuity of the weight of the `ε`-scheme on the open quadrant.** -/
theorem continuousOn_epsW (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StrongEps.epsW α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.H2.continuousOn_Wt_Qd α
  refine hWt.congr fun p hp => ?_
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact epsW_eq_Wt_of_mem_Iθ ⟨hθ1.le, hθ2.le⟩

theorem EpsSq_le_HkSq_ClassC : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.StrongEps.EpsMem α f ∧
      Work.FTS.StrongEps.EpsSq α f
        ≤ C / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 4 f := by
  obtain ⟨CH, hCHpos, hCH⟩ := hardySinGam_weak
  refine ⟨max 1 (CH / 1000000), by positivity, ?_⟩
  intro α hα f hf
  obtain ⟨hα0, hα1⟩ := hα
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
  have hγ32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hγpos : 0 < Work.Spaces.gam α - 1 := by linarith
  have hγδ : (Work.Spaces.gam α - 1) ^ 6 ≤ 1 / 1000000 := by
    have hle : Work.Spaces.gam α - 1 ≤ 1 / 10 := by rw [Work.Spaces.gam]; linarith
    have h0 : (0 : ℝ) ≤ Work.Spaces.gam α - 1 := by linarith
    calc (Work.Spaces.gam α - 1) ^ 6 ≤ (1 / 10 : ℝ) ^ 6 := pow_le_pow_left₀ h0 hle 6
      _ = 1 / 1000000 := by norm_num
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem8
  obtain ⟨hEint, hEle⟩ := slot01_le_HkSq4 hf.reg hmem4
  have hslot_ae := slot01_ae_integrable hf.reg hmem4
  have hae_pos := ae_pos_Iz
  -- the a.e.-in-`z` slice Hardy bound, together with the θ-integrability of the slice
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ CH / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) ∧
      MeasureTheory.Integrable
        (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hslot_ae, hae_pos] with z hslot hz
    have hcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hf.reg.curry_θ hz).of_le
        (show (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from by
          simp [Work.Stability.smoothOrder])
    have htrace := (hf.tr 0 0 (by norm_num)).2 z (Set.mem_Ioi.mpr hz)
    have ht1 : Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Work.FTS.H2.HQ.tendsto_nhdsGT_zero_of_traces α hα0
        (by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using htrace.1)
    have ht2 : Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      Work.FTS.H2.HQ.tendsto_nhdsLT_zero_of_traces α hα0
        (by simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using htrace.2)
    have hint := pth_slice_integrable (α := α) (z := z) (f := f) hα0 hα1 hz hslot
    obtain ⟨hL1, hL2⟩ := hCH (Work.Spaces.gam α) (fun θ => f z θ) hγ1 hγ32 hcd ht1 ht2 hint
    have hcomm : (∫ θ in Work.Spaces.Iθ,
          (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2) :=
      MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ _ => by ring)
    have hbound : (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ CH / (Work.Spaces.gam α - 1) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      calc (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            epsSq_slice_eq α z f
        _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2 := by rw [hcomm]
        _ ≤ (Work.Spaces.w z) ^ 2 * (CH / (Work.Spaces.gam α - 1) ^ 2 *
              ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)
        _ = CH / (Work.Spaces.gam α - 1) ^ 2 * ((Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
            ring
        _ = CH / (Work.Spaces.gam α - 1) ^ 2 *
              (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
            rw [slot_slice_eq (α := α) (z := z) hα0 hα1 f]
    refine ⟨hbound, ?_⟩
    refine (hL1.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
    have h1 : (Work.FTS.StrongEps.epsW α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      epsW_sq_eq hθ
    simp only []
    rw [mul_pow, h1]
    ring
  -- the outer `z`-integral
  have hEint' : MeasureTheory.Integrable
      (fun z : ℝ => CH / (Work.Spaces.gam α - 1) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hEint.const_mul _
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ CH / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 4 f := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hEle (div_nonneg hCHpos.le (sq_nonneg _)))
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hEint' ?_
    filter_upwards [hpoint] with z hz using hz.1
  -- the arithmetic of the constant
  have hconst : CH / (Work.Spaces.gam α - 1) ^ 2
      ≤ max 1 (CH / 1000000) / (Work.Spaces.gam α - 1) ^ 8 := by
    have h1 : CH * (Work.Spaces.gam α - 1) ^ 6 ≤ CH / 1000000 := by
      calc CH * (Work.Spaces.gam α - 1) ^ 6 ≤ CH * (1 / 1000000) :=
            mul_le_mul_of_nonneg_left hγδ hCHpos.le
        _ = CH / 1000000 := by ring
    have h2 : CH / 1000000 ≤ max 1 (CH / 1000000) := le_max_right _ _
    have h3 : CH * (Work.Spaces.gam α - 1) ^ 6 / (Work.Spaces.gam α - 1) ^ 8
        ≤ max 1 (CH / 1000000) / (Work.Spaces.gam α - 1) ^ 8 :=
      div_le_div_of_nonneg_right (le_trans h1 h2) (by positivity)
    have h4 : CH / (Work.Spaces.gam α - 1) ^ 2
        = CH * (Work.Spaces.gam α - 1) ^ 6 / (Work.Spaces.gam α - 1) ^ 8 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [h4]
    exact h3
  refine ⟨?_, ?_⟩
  · -- `EpsMem α f`
    have hAESM : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (ContinuousOn.pow
          (ContinuousOn.mul (hf.reg.forall 0).continuousOn (continuousOn_epsW α)) 2)
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.HasFiniteIntegral
          (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      filter_upwards [hpoint] with z hz using hz.2.2
    have hzInt : MeasureTheory.HasFiniteIntegral
        (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        hAESM.norm.integral_prod_right'
      have hbdd : (fun z : ℝ => ‖∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => CH / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
        filter_upwards [hpoint] with z hz
        rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
        refine le_trans (le_of_eq ?_) hz.1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (sq_nonneg _))
      exact (MeasureTheory.Integrable.mono' hEint' haesm hbdd).2
    have hmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, (MeasureTheory.hasFiniteIntegral_prod_iff' hAESM).mpr ⟨hslice, hzInt⟩⟩
  · calc Work.FTS.StrongEps.EpsSq α f
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 := rfl
      _ ≤ CH / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 4 f := hmain
      _ ≤ max 1 (CH / 1000000) / (Work.Spaces.gam α - 1) ^ 8 * Work.Spaces.HkSq α 4 f :=
          mul_le_mul_of_nonneg_right hconst (Work.Spaces.HkSq_nonneg α 4 f)


end Work.FTS.StrongEps.EpsSqTools
