import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.Trunc.PassAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## The weights at the endpoints of `Iθ` -/

theorem sin_two_zero : Real.sin (2 * (0 : ℝ)) = 0 := by simp

theorem sin_two_pi_div_two : Real.sin (2 * (Real.pi / 2)) = 0 := by
  rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]

theorem neg_eta_ne_zero : -(Work.Spaces.eta) ≠ 0 := by
  rw [Work.Spaces.eta]; norm_num

theorem wE_zero : FlatFT.wE 0 = 0 := by
  rw [FlatFT.wE_def, sin_two_zero]
  exact Real.zero_rpow neg_eta_ne_zero

theorem wE_pi_div_two : FlatFT.wE (Real.pi / 2) = 0 := by
  rw [FlatFT.wE_def, sin_two_pi_div_two]
  exact Real.zero_rpow neg_eta_ne_zero




/-! ## The strip `univ ×ˢ Ioo 0 (π/2)` -/

theorem isOpen_strip : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  isOpen_univ.prod isOpen_Ioo


/-! ## Almost everywhere strong measurability of strip-continuous functions -/

/-- A function continuous on the open strip `ℝ × (0,π/2)` is a.e. strongly measurable for the
restriction of Lebesgue measure to `univ ×ˢ Iθ` (the strip and that set differ by a null set). -/
theorem aesm_strip {h : ℝ × ℝ → ℝ}
    (hh : ContinuousOn h ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable h (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : (Set.univ ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume] (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq EventuallyEq.rfl hθ
  have hmeas := MeasureTheory.Measure.restrict_congr_set hprod
  exact hmeas ▸ hh.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioo)


theorem continuousOn_uncurry_pth_pth {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth g)))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le isOpen_strip 0
    (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le isOpen_strip 1 hg)).continuousOn


theorem continuousOn_uncurry_pz {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz g))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pz_le isOpen_strip 1 hg).continuousOn

theorem continuousOn_uncurry_pth {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth g))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le isOpen_strip 1 hg).continuousOn

/-! ## Continuity of the angular weights on the strip -/

theorem continuousOn_sin_two :
    ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn

theorem sin_two_ne_zero_of_mem_strip {p : ℝ × ℝ}
    (hp : p ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    Real.sin (2 * p.2) ≠ 0 := by
  have h2 : 0 < 2 * p.2 := by linarith [hp.2.1]
  have h3 : 2 * p.2 < Real.pi := by linarith [hp.2.2]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2 h3)

theorem continuousOn_wE_comp :
    ContinuousOn (fun p : ℝ × ℝ => FlatFT.wE p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h := continuousOn_sin_two.rpow_const (p := -(Work.Spaces.eta))
    (fun p hp => Or.inl (sin_two_ne_zero_of_mem_strip hp))
  simpa only [FlatFT.wE_def] using h


/-! ## The bridge between iterated and product integrals -/

theorem setIntegral_univ_prod_Iθ_eq_iterated {f : ℝ → ℝ → ℝ}
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, f p.1 p.2)
      = ∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, f t θ := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.setIntegral_prod _ hf

/-! ## `NiceFlat` for the cutoff multiples -/


end

end Work.FTS.EllSol.Trunc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The `θ`-slice functionals -/

/-- `Rslice u z = ∫_θ σ θ · u z θ²`. -/
def Rslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2

/-- `Zslice u z = ∫_θ σ θ · (z ∂_z u z θ)²`. -/
def Zslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2

/-- `Gslice G z = ∫_θ σ θ · G z θ²`. -/
def Gslice (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2

/-- `Sslice G u z = ∫_θ σ θ · G z θ · u z θ`. -/
def Sslice (G u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)

/-- `Pslice α u z = ∫_θ σ θ · (α²z²∂_z²u + α(5+α)z∂_zu) z θ · u z θ`. -/
def Pslice (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
    ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)

/-- `Lslice u z = ∫_θ Lzero1 (u z ·) θ · u z θ · σ θ`. -/
def Lslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * Work.FTS.EllipticEst.sEta θ

/-- `Cslice u z = ∫_θ (u z θ / cos θ)² σ θ`. -/
def Cslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-! ## Elementary facts about the radial weight -/

/-- The square of the radial weight is nonnegative. -/
theorem w_sq_nonneg (z : ℝ) : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _

/-- On the open half-line the square of the radial weight is positive. -/
theorem w_sq_pos {z : ℝ} (hz : 0 < z) : 0 < (Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.w]
  exact pow_pos (div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)) 2

/-- The set integrals over `Ioi 0` and over `Iz = [0,∞)` agree. -/
theorem setIntegral_Ioi_eq_Iz (f : ℝ → ℝ) :
    (∫ z in Set.Ioi 0, f z) = ∫ z in Work.Spaces.Iz, f z := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.setIntegral_congr_set (f := f)
    (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))

/-- The square of the radial weight is measurable. -/
theorem measurable_w_sq : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  unfold Work.Spaces.w
  fun_prop

/-- `sEta` is nonnegative on `Iθ`. -/
theorem sig_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ

/-- `sEta` is continuous on the open interval. -/
theorem continuousOn_sEta : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
    (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))

/-! ## `HkSq` in the `w²σ`-weighted form -/

/-- `HkSq α 0` in the `w²σ`-weighted form. -/
theorem HkSq_zero_eq_phi_mul (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 f
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z

/-- The outer `w²`-weighted slice integral of an `ℋ⁰`-element is integrable. -/
theorem integrableOn_phi_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz :=
  hf.2.congr_fun
    (fun z _ => Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z)
    measurableSet_Ici

/-! ## Measurability of the slice integrals -/

/-- `AEStronglyMeasurable` of a function whose `w²`-weighted version is. -/
theorem aesm_div_phi {A : ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 * A z)
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hdiv : AEMeasurable
      (fun z => ((Work.Spaces.w z) ^ 2 * A z) / ((Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    h.aemeasurable.div measurable_w_sq.aemeasurable
  refine (aestronglyMeasurable_iff_aemeasurable.mpr hdiv).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  have hne : (Work.Spaces.w z) ^ 2 ≠ 0 := ne_of_gt (w_sq_pos hz)
  exact mul_div_cancel_left₀ (A z) hne

/-- Restricting an `AEStronglyMeasurable` function from `Iz = [0,∞)` to `(0,∞)`. -/
theorem aesm_restrict_Ioi_of_Iz {g : ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable g
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).restrict (Set.Ioi 0)) := h.restrict
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iz).restrict (Set.Ioi 0)
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun h => h.1, fun h => ⟨h, le_of_lt h⟩⟩
  rwa [h2] at h1

/-- The `w²`-weighted slice integral of an `ℋ⁰`-element is `AEStronglyMeasurable`. -/
theorem aesm_phi_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (aesm_restrict_Ioi_of_Iz hf.2.aestronglyMeasurable).congr
    (Filter.Eventually.of_forall fun z =>
      Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z)

/-- The slice integral `z ↦ ∫_θ f² σ` of an `ℋ⁰`-element is `AEStronglyMeasurable`. -/
theorem aesm_slice_sq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  aesm_div_phi (aesm_phi_mul_slice hf)

/-! ## Domination of truncated pairings -/

/-- A property holding for every `z > 0` holds a.e. on `Iz = [0,∞)`. -/
theorem ae_restrict_Iz_of_pos {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), p z := by
  have h1 : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))).symm
  rw [h1]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-- **Domination of a truncated pairing by the `w²`-weighted one.** -/
theorem integrableOn_omega_mul {ω A : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hωm : Measurable ω) (hω0 : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z => ω z * A z) (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (hint.mono_set Set.Ioi_subset_Ici_self)
    (hωm.aestronglyMeasurable.mul hA) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hω0 z) (hA0 z))]
  exact mul_le_mul_of_nonneg_right (hωle z) (hA0 z)

/-- The integral of a truncated pairing is dominated by the `w²`-weighted integral. -/
theorem integral_omega_mul_le {ω A : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hωm : Measurable ω) (hω0 : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∫ z in Set.Ioi 0, ω z * A z)
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z := by
  have h1 := integrableOn_omega_mul hint hωm hω0 hωle hA0 hA
  have h2 : (∫ z in Set.Ioi 0, ω z * A z)
      ≤ ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * A z := by
    refine MeasureTheory.integral_mono_ae h1 (hint.mono_set Set.Ioi_subset_Ici_self) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
    exact mul_le_mul_of_nonneg_right (hωle z) (hA0 z)
  exact h2.trans_eq (setIntegral_Ioi_eq_Iz _)

/-- **Domination of a pairing with a bounded coefficient.** -/
theorem integrableOn_coef_mul_le {c A : ℝ → ℝ} {C : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hC : 0 ≤ C) (hbound : ∀ z, 0 < z → |c z| ≤ C * (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z => c z * A z) (Set.Ioi 0) ∧
      |∫ z in Set.Ioi 0, c z * A z|
        ≤ C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z) := by
  have hmain : MeasureTheory.IntegrableOn (fun z => c z * A z) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono'
      ((hint.mono_set Set.Ioi_subset_Ici_self).const_mul C) (hc.mul hA) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have h := hbound z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 z)]
    calc |c z| * A z ≤ (C * (Work.Spaces.w z) ^ 2) * A z :=
          mul_le_mul_of_nonneg_right h (hA0 z)
      _ = C * ((Work.Spaces.w z) ^ 2 * A z) := by ring
  refine ⟨hmain, ?_⟩
  have h1 : |∫ z in Set.Ioi 0, c z * A z| ≤ ∫ z in Set.Ioi 0, |c z * A z| :=
    abs_integral_le_integral_abs
  have h2 : (∫ z in Set.Ioi 0, |c z * A z|)
      ≤ ∫ z in Set.Ioi 0, C * ((Work.Spaces.w z) ^ 2 * A z) := by
    refine MeasureTheory.integral_mono_ae hmain.abs ?_ ?_
    · exact (hint.mono_set Set.Ioi_subset_Ici_self).const_mul C
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have h := hbound z hz
      rw [abs_mul, abs_of_nonneg (hA0 z)]
      calc |c z| * A z ≤ (C * (Work.Spaces.w z) ^ 2) * A z :=
            mul_le_mul_of_nonneg_right h (hA0 z)
        _ = C * ((Work.Spaces.w z) ^ 2 * A z) := by ring
  have h3 : (∫ z in Set.Ioi 0, C * ((Work.Spaces.w z) ^ 2 * A z))
      = C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z) := by
    rw [MeasureTheory.integral_const_mul, setIntegral_Ioi_eq_Iz]
  linarith [h1, h2, h3]

/-! ## The slice functionals versus `HkSq` -/

/-- The commutation `∫_θ f g = ∫_θ g f` on the angular interval. -/
theorem setIntegral_mul_comm (f g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ * g θ) = ∫ θ in Work.Spaces.Iθ, g θ * f θ :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- `Rslice` written with the square first. -/
theorem Rslice_eq_integral (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Rslice u z = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [Rslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ) (fun θ => (u z θ) ^ 2)

/-- `Zslice` written with the square first. -/
theorem Zslice_eq_integral (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Zslice u z = ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ := by
  rw [Zslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ)
    (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)

/-- `Gslice` written with the square first. -/
theorem Gslice_eq_integral (G : ℝ → ℝ → ℝ) (z : ℝ) :
    Gslice G z = ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [Gslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ) (fun θ => (G z θ) ^ 2)

/-- `HkSq α 0 u` in terms of `Rslice`. -/
theorem HkSq_zero_eq_Rslice (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 u = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z := by
  rw [HkSq_zero_eq_phi_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [Rslice]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- `HkSq α 0 (grad u)` in terms of `Zslice`. -/
theorem HkSq_grad_eq_Zslice (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Zslice u z := by
  rw [HkSq_zero_eq_phi_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [Zslice]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-! ## Nonnegativity -/

theorem Rslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Rslice u z := by
  rw [Rslice]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (sig_nonneg_Iθ hθ) (sq_nonneg _)

theorem Gslice_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Gslice G z := by
  rw [Gslice]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (sig_nonneg_Iθ hθ) (sq_nonneg _)

theorem Zslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Zslice u z := by
  rw [Zslice]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (sig_nonneg_Iθ hθ) (sq_nonneg _)

theorem Cslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Cslice u z := by
  rw [Cslice]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (sq_nonneg _) (sig_nonneg_Iθ hθ)

/-! ## Slicewise `σ`-integrability on `Iθ` -/

/-- The `AeData`-slice of `Rslice` is `σ`-integrable. -/
theorem integrableOn_Rslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
      Work.Spaces.Iθ :=
  ((Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz).1).congr_fun
    (fun θ _ => by ring) measurableSet_Icc

/-- The `AeData`-slice of `Gslice` is `σ`-integrable. -/
theorem integrableOn_Gslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2)
      Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integrableOn_sq_mul_sEtaR_of_HkMem h.memG
    hz).congr_fun (fun θ _ => by ring) measurableSet_Icc

/-- The `AeData`-slice of `Pslice` is `σ`-integrable. -/
theorem integrableOn_Pslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ *
      ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ))
      Work.Spaces.Iθ := by
  obtain ⟨-, -, h3, h4, -⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz
  have ha : MeasureTheory.IntegrableOn (fun θ => (α ^ 2 * z ^ 2) *
      (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pzIter 2 u z θ * u z θ)))
      Work.Spaces.Iθ :=
    (h4.const_mul (α ^ 2 * z ^ 2)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  have hb : MeasureTheory.IntegrableOn (fun θ => (α * (5 + α) * z) *
      (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz u z θ * u z θ)))
      Work.Spaces.Iθ :=
    (h3.const_mul (α * (5 + α) * z)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  refine (ha.add hb).congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Pi.add_apply]
  ring

/-- The `AeData`-slice of `Sslice` is `σ`-integrable (AM–GM against `G² + u²`). -/
theorem integrableOn_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
      Work.Spaces.Iθ := by
  have hu2 := integrableOn_Rslice h hz
  have hg2 := integrableOn_Gslice h hz
  have hsum : MeasureTheory.IntegrableOn (fun θ =>
      (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
        + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) Work.Spaces.Iθ :=
    (hg2.add hu2).const_mul (1 / 2)
  have hsmG : MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aesm_slice_G h hz
  have hsmU : MeasureTheory.AEStronglyMeasurable (fun θ => u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aesm_of_contOn_Ioo
      (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.contOn_slice h hz)
  have hsmσ : MeasureTheory.AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.measurable_sEtaR.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hsum (hsmσ.mul (hsmG.mul hsmU)) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ := sig_nonneg_Iθ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσ, abs_mul]
  have h2 : 2 * (|G z θ| * |u z θ|) ≤ (G z θ) ^ 2 + (u z θ) ^ 2 := by
    nlinarith [sq_nonneg (|G z θ| - |u z θ|), sq_abs (G z θ), sq_abs (u z θ)]
  calc Work.FTS.EllipticEst.sEta θ * (|G z θ| * |u z θ|)
      = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (2 * (|G z θ| * |u z θ|))) := by ring
    _ ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ) (by norm_num)
    _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
          + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring

/-- The angular weight vanishes at `θ = 0`. -/
theorem sEta_zero : Work.FTS.EllipticEst.sEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

/-- The angular weight vanishes at `θ = π/2`. -/
theorem sEta_pi_div_two : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

/-- `Lslice` is the sum of `Pslice` and `Sslice` (the equation on the open quadrant). -/
theorem Lslice_eq_Pslice_add_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    Lslice u z = Pslice α u z + Sslice G u z := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
          * Work.FTS.EllipticEst.sEta θ
        = Work.FTS.EllipticEst.sEta θ *
            ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)
          + Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
      · have hbsl := h.eq z hz θ hθ0 hθ1
        have hL : Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ
            = Work.Elliptic.Lzero u z θ := by
          have h1 : Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ
              = Work.Elliptic.Lzero (fun _ θ' : ℝ => u z θ') z θ :=
            congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero (fun θ' => u z θ') z) θ
          have h2 : Work.Elliptic.Lzero (fun _ θ' : ℝ => u z θ') z θ
              = Work.Elliptic.Lzero u z θ := by
            rw [Work.Elliptic.Lzero_eq_deriv, Work.Elliptic.Lzero_eq_deriv]
          rw [h1, h2]
        rw [hL]
        have hkey : Work.Elliptic.Lzero u z θ
            = G z θ + (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
                + (α * (5 + α) * z) * Work.Spaces.pz u z θ) := by
          rw [Work.Elliptic.bslOp_apply] at hbsl
          linarith [hbsl]
        rw [hkey]; ring
      · subst hθ1
        rw [sEta_pi_div_two]; ring
    · subst hθ0
      rw [sEta_zero]; ring
  rw [Lslice, Pslice, Sslice, Work.Spaces.Iθ]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt]
  exact MeasureTheory.integral_add (integrableOn_Pslice h hz) (integrableOn_Sslice h hz)

end Work.FTS.EllipticEst.AeS1
end
end
