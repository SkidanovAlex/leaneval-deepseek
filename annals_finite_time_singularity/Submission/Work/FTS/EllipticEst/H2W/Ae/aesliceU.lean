import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.Ae.SliceSigmaHardyTwo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 800000

/-! ## Helper lemmas

The proof of `aesliceU` uses only the *first* solvability condition of `AeData`
(`Fstar u z = 0` for almost every `z`): for such a `z` the slice `θ ↦ u z θ` is, after
subtraction of `L · jumpProf` (`L` the left endpoint limit, which exists because
`∫_θ (∂_θθu)² σ < ∞`), a function with both endpoint limits `0`, to which the two-derivative
weighted Hardy inequality `SliceSigmaHardyTwo` applies; the moment condition then bounds `L`. -/

/-- The affine profile with the value `1` at `θ = 0` and `0` at `θ = π/2`: the profile of an
endpoint jump of size `1` at `θ = 0`. -/
def jumpProf (θ : ℝ) : ℝ := 1 - (2 / Real.pi) * θ

theorem jumpProf_zero : jumpProf 0 = 1 := by unfold jumpProf; norm_num

theorem jumpProf_pi : jumpProf (Real.pi / 2) = 0 := by
  unfold jumpProf
  field_simp
  ring

theorem continuous_jumpProf : Continuous jumpProf := by unfold jumpProf; fun_prop

theorem contDiff_jumpProf : ContDiff ℝ 2 jumpProf := by unfold jumpProf; fun_prop

theorem hasDerivAt_jumpProf (θ : ℝ) : HasDerivAt jumpProf (-(2 / Real.pi)) θ := by
  unfold jumpProf
  have h : HasDerivAt (fun t : ℝ => 1 - (2 / Real.pi) * t) (0 - (2 / Real.pi) * 1) θ :=
    (hasDerivAt_const (x := θ) (c := (1 : ℝ))).sub
      ((hasDerivAt_id θ).const_mul (2 / Real.pi))
  simpa using h

theorem deriv_jumpProf : deriv jumpProf = fun _ : ℝ => -(2 / Real.pi) := by
  funext θ; exact (hasDerivAt_jumpProf θ).deriv

theorem deriv_deriv_jumpProf : deriv (deriv jumpProf) = fun _ : ℝ => (0 : ℝ) := by
  rw [deriv_jumpProf]
  funext θ
  simp

theorem jumpProf_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |jumpProf θ| ≤ 1 := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have h2 : 0 ≤ (2 / Real.pi) * θ := mul_nonneg (by positivity) hθ.1
  have h3 : (2 / Real.pi) * θ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hθ.2 (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
    have h4 : (2 / Real.pi) * (Real.pi / 2) = 1 := by
      have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp
    linarith [h, h4]
  unfold jumpProf
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

theorem jumpProf_sq_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (jumpProf θ) ^ 2 ≤ 1 := by
  have h := jumpProf_mem_Iθ hθ
  nlinarith [h, abs_nonneg (jumpProf θ), sq_abs (jumpProf θ)]

/-! ### Elementary integrals of the angular profile `sin θ cos²θ` -/

theorem continuous_sinCos2 : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `θ ↦ -cos³θ/3` is a primitive of the angular profile `sin θ cos²θ`. -/
def psiPrim (θ : ℝ) : ℝ := -((Real.cos θ) ^ 3) / 3

theorem continuous_psiPrim : Continuous psiPrim := by unfold psiPrim; fun_prop

theorem psiPrim_zero : psiPrim 0 = -(1 / 3) := by
  unfold psiPrim; norm_num

theorem psiPrim_pi : psiPrim (Real.pi / 2) = 0 := by
  unfold psiPrim; simp

theorem hasDerivAt_psiPrim (θ : ℝ) : HasDerivAt psiPrim (Work.Elliptic.sinCos2 θ) θ := by
  have h4 : HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3) (Work.Elliptic.sinCos2 θ) θ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * (Real.cos θ) ^ 2) (Real.cos θ) := by
      simpa using hasDerivAt_pow 3 (Real.cos θ)
    exact ((h2.comp θ h1).neg.div_const 3).congr_deriv
      (by rw [Work.Elliptic.sinCos2]; ring)
  unfold psiPrim
  exact h4

theorem sinCos2_integral :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ) = 1 / 3 := by
  have hInt : IntervalIntegrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ) volume 0 (Real.pi / 2) :=
    continuous_sinCos2.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ))
    (b := Real.pi / 2) (f := psiPrim) (fun x _ => hasDerivAt_psiPrim x) hInt
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2),
    hFTC, psiPrim_pi, psiPrim_zero]
  norm_num

/-- `θ ↦ sin θ - sin³θ/3` is a primitive of `cos³θ`. -/
def cosCube (θ : ℝ) : ℝ := Real.sin θ - (Real.sin θ) ^ 3 / 3

theorem continuous_cosCube : Continuous cosCube := by unfold cosCube; fun_prop

theorem cosCube_zero : cosCube 0 = 0 := by unfold cosCube; simp

theorem cosCube_pi : cosCube (Real.pi / 2) = 2 / 3 := by
  unfold cosCube; norm_num

theorem hasDerivAt_cosCube (θ : ℝ) : HasDerivAt cosCube ((Real.cos θ) ^ 3) θ := by
  have h4 : HasDerivAt (fun t : ℝ => Real.sin t - (Real.sin t) ^ 3 / 3) ((Real.cos θ) ^ 3) θ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.sin t) (Real.cos θ) θ := Real.hasDerivAt_sin θ
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * (Real.sin θ) ^ 2) (Real.sin θ) := by
      simpa using hasDerivAt_pow 3 (Real.sin θ)
    refine (h1.sub ((h2.comp θ h1).div_const 3)).congr_deriv ?_
    rw [show 3 * Real.sin θ ^ 2 * Real.cos θ / 3 = Real.sin θ ^ 2 * Real.cos θ by ring]
    have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    rw [hs]; ring
  unfold cosCube
  exact h4

theorem psiPrim_integral : (∫ θ in Work.Spaces.Iθ, psiPrim θ) = -(2 / 9) := by
  have hInt : IntervalIntegrable (fun θ : ℝ => (Real.cos θ) ^ 3) volume 0 (Real.pi / 2) :=
    (Real.continuous_cos.pow 3).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ))
    (b := Real.pi / 2) (f := cosCube) (fun x _ => hasDerivAt_cosCube x) hInt
  have hkey : (∫ θ in Work.Spaces.Iθ, psiPrim θ)
      = -(1 / 3) * ∫ θ in Work.Spaces.Iθ, (Real.cos θ) ^ 3 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    unfold psiPrim; ring
  rw [hkey, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2),
    hFTC, cosCube_pi, cosCube_zero]
  norm_num

theorem theta_sinCos2_integral :
    (∫ θ in Work.Spaces.Iθ, θ * Work.Elliptic.sinCos2 θ) = 2 / 9 := by
  -- the product `θ * psiPrim θ` has derivative `psiPrim θ + θ * sinCos2 θ`
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => t * psiPrim t)
      (psiPrim θ + θ * Work.Elliptic.sinCos2 θ) θ := by
    intro θ
    have h := (hasDerivAt_psiPrim θ).mul (hasDerivAt_id θ)
    convert h using 1
    · ext t; simp only [Pi.mul_apply, id_eq]; ring
    · simp only [id_eq]; ring
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont : Continuous fun θ : ℝ => psiPrim θ + θ * Work.Elliptic.sinCos2 θ :=
    continuous_psiPrim.add (continuous_id.mul continuous_sinCos2)
  have hIntF : IntervalIntegrable (fun θ : ℝ => psiPrim θ + θ * Work.Elliptic.sinCos2 θ)
      volume 0 (Real.pi / 2) := hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ))
    (b := Real.pi / 2) (f := fun t : ℝ => t * psiPrim t) (fun x _ => hderiv x) hIntF
  have hA : (∫ θ in (0 : ℝ)..(Real.pi / 2), (psiPrim θ + θ * Work.Elliptic.sinCos2 θ)) = 0 := by
    rw [hFTC, psiPrim_pi]; ring
  have hint1 : IntervalIntegrable psiPrim volume 0 (Real.pi / 2) :=
    continuous_psiPrim.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ) volume 0
      (Real.pi / 2) :=
    (continuous_id.mul continuous_sinCos2).intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add (f := psiPrim)
    (g := fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ) hint1 hint2
  have hIθ1 : (∫ θ in (0 : ℝ)..(Real.pi / 2), psiPrim θ)
      = ∫ θ in Work.Spaces.Iθ, psiPrim θ := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hIθ2 : (∫ θ in (0 : ℝ)..(Real.pi / 2), θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, θ * Work.Elliptic.sinCos2 θ := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hA] at hsplit
  rw [hIθ1, hIθ2, psiPrim_integral] at hsplit
  linarith

theorem jumpProf_moment :
    (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ) = 1 / 3 - 4 / (9 * Real.pi) := by
  have hcontt : Continuous fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ :=
    continuous_id.mul continuous_sinCos2
  have hint1 : IntegrableOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    continuous_sinCos2.continuousOn.integrableOn_compact isCompact_Icc
  have hint2 : IntegrableOn (fun θ : ℝ => θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    hcontt.continuousOn.integrableOn_compact isCompact_Icc
  have hpt : ∀ θ : ℝ, jumpProf θ * Work.Elliptic.sinCos2 θ
      = Work.Elliptic.sinCos2 θ - (2 / Real.pi) * (θ * Work.Elliptic.sinCos2 θ) := by
    intro θ; unfold jumpProf; ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    MeasureTheory.integral_sub hint1 (hint2.const_mul (2 / Real.pi)),
    MeasureTheory.integral_const_mul, sinCos2_integral, theta_sinCos2_integral]
  ring

theorem jumpProf_moment_ge :
    (1 : ℝ) / 6 ≤ ∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ := by
  rw [jumpProf_moment]
  have h1 : 4 / (9 * Real.pi) ≤ 1 / 6 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 9 * Real.pi)]
    have hpi : (8 : ℝ) / 3 < Real.pi := by linarith [Real.pi_gt_three]
    linarith
  linarith

theorem sinCos2_sq_integral_le :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) ≤ Real.pi / 2 := by
  have hcont : Continuous fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 := continuous_sinCos2.pow 2
  have hint : IntegrableOn (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2) Work.Spaces.Iθ :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hle : ∀ θ ∈ Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 ≤ (1 : ℝ) := by
    intro θ hθ
    have hs : |Real.sin θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have hc : |Real.cos θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have h4 : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul, abs_pow]
      have hc2 : |Real.cos θ| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
      have hm : |Real.sin θ| * |Real.cos θ| ^ 2 ≤ 1 * 1 :=
        mul_le_mul hs (by simpa using hc2) (by positivity) (by norm_num)
      simpa using hm
    nlinarith [h4, abs_nonneg (Work.Elliptic.sinCos2 θ), sq_abs (Work.Elliptic.sinCos2 θ)]
  calc (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2)
      ≤ ∫ _θ in Work.Spaces.Iθ, (1 : ℝ) :=
        MeasureTheory.setIntegral_mono_on hint hconst measurableSet_Icc hle
    _ = Real.pi / 2 := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def,
          Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2 - 0),
          sub_zero]

end

/-! ## The main slice estimate -/

/-- The second derivative of `θ ↦ g θ - c * jumpProf θ` agrees with that of `g`. -/
theorem deriv2_sub_const_mul_jumpProf {g : ℝ → ℝ} {c : ℝ} {θ : ℝ}
    (hg : ∀ᶠ t in 𝓝 θ, DifferentiableAt ℝ g t)
    (hg' : DifferentiableAt ℝ (deriv g) θ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => g s - c * jumpProf s) t) θ = deriv (deriv g) θ := by
  have hpt : ∀ᶠ t in 𝓝 θ,
      deriv (fun s : ℝ => g s - c * jumpProf s) t = deriv g t + c * (2 / Real.pi) := by
    filter_upwards [hg] with t hgt
    rw [show (fun s : ℝ => g s - c * jumpProf s)
        = (fun s : ℝ => g s) - (fun s : ℝ => c * jumpProf s) from rfl,
      deriv_sub hgt (((hasDerivAt_jumpProf t).differentiableAt).const_mul c),
      deriv_const_mul c (hasDerivAt_jumpProf t).differentiableAt, deriv_jumpProf]
    ring
  have h2 : deriv (fun t : ℝ => deriv (fun s : ℝ => g s - c * jumpProf s) t) θ
      = deriv (fun t : ℝ => deriv g t + c * (2 / Real.pi)) θ :=
    Filter.EventuallyEq.deriv_eq hpt
  rw [h2, show (fun t : ℝ => deriv g t + c * (2 / Real.pi))
      = (fun t : ℝ => deriv g t) + (fun _ : ℝ => c * (2 / Real.pi)) from rfl,
    deriv_add hg' (differentiableAt_const _), deriv_const, add_zero]

section Main

variable {α : ℝ} {u G : ℝ → ℝ → ℝ}

/-- **The `z`-slicewise estimate.**  For almost every `z` (here: for every `z` at which the first
solvability condition holds), the `σ`-weighted `L²`-norm of the slice of `u` is controlled by the
`σ`-weighted `L²`-norm of its second `θ`-derivative. -/
theorem slice_le (CA : ℝ) (hCA : 0 < CA)
    (hA : ∀ g : ℝ → ℝ, ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal CA
          * ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ))
    (h : AeData α u G) {z : ℝ} (hz : 0 < z)
    (hRlim : Filter.Tendsto (fun θ => u z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hmom : Work.Elliptic.Fstar u z = 0) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal (10 ^ 7 * CA)
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
  have hIoo_ae : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  have hsEta_nonneg : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ)
  have hsEta_ge_one : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [← hIoo_ae]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact Work.FTS.EllipticEst.H2W.one_le_sEta hθ
  have hsEta_aemeas : AEMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have hcont : ContinuousOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      fun θ hθ => (Work.FTS.EllipticEst.H2W.continuousAt_sEta hθ).continuousWithinAt
    have h1 : AEMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hcont.aemeasurable measurableSet_Ioo
    rwa [hIoo_ae] at h1
  -- the slice of `u` and the finiteness of its `σ`-weighted second derivative
  have hsm_slice : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma h.memAng2 hz).congr_fun
      (fun θ _ => rfl) measurableSet_Icc
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  set D : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  have hDlin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = ENNReal.ofReal D := by
    have hcongr : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        = ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.lintegral_congr (fun θ => congrArg ENNReal.ofReal rfl)
    rw [hcongr, hD]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn2).symm
  -- boundedness of the slice and of its derivative
  obtain ⟨Mb, hMbpos, hMb⟩ := Work.FTS.EllipticEst.Honest.SliceBddSqSigma hsm_slice hInt2
  -- the left endpoint limit
  have hderiv_at : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      HasDerivAt (fun θ : ℝ => u z θ) (deriv (fun θ : ℝ => u z θ) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    exact ((hsm_slice.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt
      (by norm_num)).hasDerivAt
  have hint_deriv : MeasureTheory.IntegrableOn (deriv (fun θ : ℝ => u z θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo (0 : ℝ) (Real.pi / 4)) ?_ ?_ Mb ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (measurable_deriv _).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs]
      exact (hMb θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩).1
  obtain ⟨L₀, hL₀lim⟩ := Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    (f := fun θ : ℝ => u z θ) (f' := deriv (fun θ : ℝ => u z θ)) (δ := Real.pi / 4)
    (by linarith [Real.pi_pos]) hderiv_at hint_deriv
  -- the corrected slice
  set w : ℝ → ℝ := (fun θ : ℝ => u z θ) - (fun θ : ℝ => L₀ * jumpProf θ) with hw
  have hw_apply : ∀ θ : ℝ, w θ = u z θ - L₀ * jumpProf θ := fun θ => rfl
  have hsm_w : ContDiffOn ℝ 2 w (Set.Ioo 0 (Real.pi / 2)) := by
    rw [hw]
    exact hsm_slice.sub ((contDiff_const.mul contDiff_jumpProf).contDiffOn)
  have hlim0_w : Filter.Tendsto w (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => L₀ * jumpProf θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (L₀ * jumpProf 0)) :=
      (continuous_jumpProf.tendsto 0).const_mul L₀ |>.mono_left nhdsWithin_le_nhds
    have h2 := hL₀lim.sub h1
    have h3 : L₀ - L₀ * jumpProf 0 = 0 := by rw [jumpProf_zero]; ring
    rw [h3] at h2
    rw [hw]
    exact h2
  have hlimL_w : Filter.Tendsto w
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => L₀ * jumpProf θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (L₀ * jumpProf (Real.pi / 2))) :=
      (continuous_jumpProf.tendsto (Real.pi / 2)).const_mul L₀ |>.mono_left nhdsWithin_le_nhds
    have h2 := hRlim.sub h1
    have h3 : 0 - L₀ * jumpProf (Real.pi / 2) = 0 := by rw [jumpProf_pi]; ring
    rw [h3] at h2
    rw [hw]
    exact h2
  -- the second derivative of `w` agrees with that of the slice of `u`
  have hdw2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun t : ℝ => deriv w t) θ
        = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
    intro θ hθ
    have hgn : ∀ᶠ t in 𝓝 θ, DifferentiableAt ℝ (fun θ' : ℝ => u z θ') t := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact (hsm_slice.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)
    have hder1 : ContDiffOn ℝ 1 (deriv (fun θ' : ℝ => u z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
      hsm_slice.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hg' : DifferentiableAt ℝ (deriv (fun θ' : ℝ => u z θ')) θ :=
      (hder1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    rw [hw]
    exact deriv2_sub_const_mul_jumpProf hgn hg'
  have hInt2_w : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv w t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine hInt2.congr ?_
    rw [← hIoo_ae]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [hdw2 θ hθ]
  have haesm_w : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo hsm_slice).sub
      ((continuous_jumpProf.const_mul L₀).aestronglyMeasurable)
  have haesm_w2 : AEStronglyMeasurable (fun θ => (w θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    haesm_w.pow 2
  -- the piece `A` gives the bound for the corrected slice
  have hA_w := hA w hsm_w hInt2_w hlim0_w hlimL_w
  have hwlin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((deriv (fun t => deriv w t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = ENNReal.ofReal D := by
    have heq : (fun θ => ENNReal.ofReal ((deriv (fun t => deriv w t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ))
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => ENNReal.ofReal
            ((deriv (fun t => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
      rw [← hIoo_ae]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [hdw2 θ hθ]
    rw [MeasureTheory.lintegral_congr_ae heq, hD]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn2).symm
  have hA_w' : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal (CA * D) := by
    rw [hwlin] at hA_w
    rwa [← ENNReal.ofReal_mul hCA.le] at hA_w
  have hnn_w : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  have hnn_w2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ (w θ) ^ 2 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hw2sig_le : (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ CA * D := by
    calc (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)).toReal :=
          Work.FTS.EllipticEst.Honest.setIntegral_le_toReal_lintegral _ hnn_w
      _ ≤ (ENNReal.ofReal (CA * D)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hA_w'
      _ = CA * D := ENNReal.toReal_ofReal (mul_nonneg hCA.le hDnn)
  have hwlin_le : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((w θ) ^ 2))
      ≤ ENNReal.ofReal (CA * D) := by
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((w θ) ^ 2))
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hsEta_ge_one] with θ hθ
          rw [ENNReal.ofReal_le_ofReal_iff
            (mul_nonneg (sq_nonneg _) (le_trans zero_le_one hθ))]
          have hx := mul_le_mul_of_nonneg_left hθ (sq_nonneg (w θ))
          simpa only [mul_one] using hx
      _ ≤ ENNReal.ofReal (CA * D) := hA_w'
  have hw2_int : MeasureTheory.IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm_w2 hnn_w2).mp
      (ne_of_lt (lt_of_le_of_lt hwlin_le ENNReal.ofReal_lt_top))
  have hw2sig_int : MeasureTheory.IntegrableOn
      (fun θ => (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (haesm_w2.mul hsEta_aemeas.aestronglyMeasurable) hnn_w).mp
      (ne_of_lt (lt_of_le_of_lt hA_w' ENNReal.ofReal_lt_top))
  have hw2_le : (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) ≤ CA * D := by
    calc (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
        ≤ (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((w θ) ^ 2)).toReal :=
          Work.FTS.EllipticEst.Honest.setIntegral_le_toReal_lintegral _ hnn_w2
      _ ≤ (ENNReal.ofReal (CA * D)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hwlin_le
      _ = CA * D := ENNReal.toReal_ofReal (mul_nonneg hCA.le hDnn)
  -- the moment condition
  have hgψ_int : MeasureTheory.IntegrableOn
      (fun θ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound (s := Work.Spaces.Iθ) ?_ ?_ Mb ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · exact (Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo hsm_slice).mul
        continuous_sinCos2.aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have hb : |u z θ| ≤ Mb := by
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · rw [← h0, h.dirZero z, abs_zero]; exact hMbpos.le
        · rcases eq_or_lt_of_le hθ.2 with hpi | hpi
          · rw [hpi, h.dirPi z, abs_zero]; exact hMbpos.le
          · exact (hMb θ ⟨h0, hpi⟩).2
      have hs1 : |Real.sin θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
      have hc1 : |Real.cos θ| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
      have hψ1 : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
        rw [Work.Elliptic.sinCos2, abs_mul, abs_pow]
        have hc2 : |Real.cos θ| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc1 2
        have hm : |Real.sin θ| * |Real.cos θ| ^ 2 ≤ 1 * 1 :=
          mul_le_mul hs1 (by simpa using hc2) (by positivity) (by norm_num)
        simpa using hm
      rw [Real.norm_eq_abs, abs_mul]
      calc |u z θ| * |Work.Elliptic.sinCos2 θ| ≤ Mb * 1 :=
            mul_le_mul hb hψ1 (abs_nonneg _) hMbpos.le
        _ = Mb := mul_one _
  have hjψ_int : MeasureTheory.IntegrableOn
      (fun θ => jumpProf θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (continuous_jumpProf.mul continuous_sinCos2).continuousOn.integrableOn_compact isCompact_Icc
  have hwψ_int : MeasureTheory.IntegrableOn
      (fun θ => w θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have heq : (fun θ => w θ * Work.Elliptic.sinCos2 θ)
        = (fun θ => u z θ * Work.Elliptic.sinCos2 θ
            - L₀ * (jumpProf θ * Work.Elliptic.sinCos2 θ)) := by
      funext θ; rw [hw_apply θ]; ring
    rw [heq]
    exact hgψ_int.sub (hjψ_int.const_mul L₀)
  have hmomid : L₀ * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ)
      = -(∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) := by
    have hmom' : (∫ θ in Work.Spaces.Iθ, u z θ * Work.Elliptic.sinCos2 θ) = 0 := hmom
    have hsplit : (∫ θ in Work.Spaces.Iθ, u z θ * Work.Elliptic.sinCos2 θ)
        = L₀ * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ)
          + ∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ := by
      rw [← MeasureTheory.integral_const_mul L₀
          (fun θ => jumpProf θ * Work.Elliptic.sinCos2 θ),
        ← MeasureTheory.integral_add (hjψ_int.const_mul L₀) hwψ_int]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => ?_))
      show u z θ * Work.Elliptic.sinCos2 θ
        = L₀ * (jumpProf θ * Work.Elliptic.sinCos2 θ) + w θ * Work.Elliptic.sinCos2 θ
      rw [hw_apply θ]; ring
    linarith
  -- Cauchy--Schwarz and the bound on the jump
  have hw_memLp : MemLp w 2 (volume.restrict Work.Spaces.Iθ) := by
    rw [memLp_two_iff_integrable_sq haesm_w]
    exact hw2_int
  have hpsi_memLp : MemLp (fun θ : ℝ => Work.Elliptic.sinCos2 θ) 2
      (volume.restrict Work.Spaces.Iθ) := by
    rw [memLp_two_iff_integrable_sq continuous_sinCos2.aestronglyMeasurable]
    exact (continuous_sinCos2.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hcs : (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) :=
    Work.Spaces.cs_integral hw_memLp hpsi_memLp
  have hL0sq : L₀ ^ 2 ≤ 18 * Real.pi * (CA * D) := by
    have hc1 : (1 : ℝ) / 6 ≤ ∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ :=
      jumpProf_moment_ge
    have hsq : (L₀ * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ)) ^ 2
        = (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2 := by
      rw [hmomid]; ring
    have h1 : L₀ ^ 2 * ((1 : ℝ) / 6) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2 := by
      calc L₀ ^ 2 * ((1 : ℝ) / 6) ^ 2
          ≤ L₀ ^ 2 * (∫ θ in Work.Spaces.Iθ, jumpProf θ * Work.Elliptic.sinCos2 θ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hc1 2) (sq_nonneg L₀)
        _ = (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2 := by rw [← hsq]; ring
    have h2 : (∫ θ in Work.Spaces.Iθ, w θ * Work.Elliptic.sinCos2 θ) ^ 2
        ≤ (CA * D) * (Real.pi / 2) := by
      refine hcs.trans ?_
      exact mul_le_mul hw2_le sinCos2_sq_integral_le
        (integral_nonneg fun _ => sq_nonneg _) (mul_nonneg hCA.le hDnn)
    have hkey : L₀ ^ 2 ≤ 36 * ((CA * D) * (Real.pi / 2)) := by linarith
    calc L₀ ^ 2 ≤ 36 * ((CA * D) * (Real.pi / 2)) := hkey
      _ = 18 * Real.pi * (CA * D) := by ring
  -- the final real bound
  have hj2sig_int : MeasureTheory.IntegrableOn
      (fun θ => (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine Integrable.mono' Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.1 ?_ ?_
    · exact (continuous_jumpProf.pow 2).aestronglyMeasurable.mul
        hsEta_aemeas.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))]
      exact mul_le_of_le_one_left (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ)
        (jumpProf_sq_le_one hθ)
  have hj2sig_le : (∫ θ in Work.Spaces.Iθ, (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ 10 ^ 4 := by
    calc (∫ θ in Work.Spaces.Iθ, (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ :=
          MeasureTheory.setIntegral_mono_on hj2sig_int
            Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.1 measurableSet_Icc
            (fun θ hθ => mul_le_of_le_one_left
              (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ) (jumpProf_sq_le_one hθ))
      _ ≤ 10 ^ 4 := Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.2
  have hdom_int : MeasureTheory.IntegrableOn
      (fun θ => (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h1 : (fun θ => (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
          * Work.FTS.EllipticEst.sEta θ)
        = fun θ => (2 * L₀ ^ 2) * ((jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + 2 * ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      funext θ; ring
    rw [h1]
    exact (hj2sig_int.const_mul (2 * L₀ ^ 2)).add (hw2sig_int.const_mul 2)
  have hpt_ub : ∀ θ ∈ Work.Spaces.Iθ,
      (u z θ) ^ 2 ≤ 2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2 := by
    intro θ _
    rw [hw_apply θ]
    nlinarith [sq_nonneg (u z θ - 2 * (L₀ * jumpProf θ))]
  have hu_int : MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine Integrable.mono' hdom_int ?_ ?_
    · exact ((Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo hsm_slice).pow 2).mul
        hsEta_aemeas.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact mul_le_mul_of_nonneg_right (hpt_ub θ hθ) hσ
  have hreal : (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ 10 ^ 7 * CA * D := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
            * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_mono_ae hu_int hdom_int ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ
      exact mul_le_mul_of_nonneg_right (hpt_ub θ hθ) hσ
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2) * Work.FTS.EllipticEst.sEta θ)
        = (2 * L₀ ^ 2) * (∫ θ in Work.Spaces.Iθ,
              (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      rw [show (fun θ => (2 * L₀ ^ 2 * (jumpProf θ) ^ 2 + 2 * (w θ) ^ 2)
            * Work.FTS.EllipticEst.sEta θ)
          = fun θ => (2 * L₀ ^ 2) * ((jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + 2 * ((w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by funext θ; ring]
      rw [MeasureTheory.integral_add (hj2sig_int.const_mul (2 * L₀ ^ 2))
          (hw2sig_int.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hCADnn : 0 ≤ CA * D := mul_nonneg hCA.le hDnn
    have h3 : (2 * L₀ ^ 2) * (∫ θ in Work.Spaces.Iθ,
          (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ 2 * (18 * Real.pi * (CA * D)) * 10 ^ 4 := by
      have h4 : (2 * L₀ ^ 2) ≤ 2 * (18 * Real.pi * (CA * D)) := by linarith
      have h4b : (0 : ℝ) ≤ 2 * (18 * Real.pi * (CA * D)) := by
        have := Real.pi_pos; nlinarith [mul_nonneg hCA.le hDnn]
      have h4c : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
          (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
          mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
      calc (2 * L₀ ^ 2) * (∫ θ in Work.Spaces.Iθ,
              (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ (2 * (18 * Real.pi * (CA * D))) * (∫ θ in Work.Spaces.Iθ,
              (jumpProf θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
            mul_le_mul_of_nonneg_right h4 h4c
        _ ≤ (2 * (18 * Real.pi * (CA * D))) * 10 ^ 4 :=
            mul_le_mul_of_nonneg_left hj2sig_le h4b
    have h5 : 2 * (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ 2 * (CA * D) := mul_le_mul_of_nonneg_left hw2sig_le (by norm_num)
    have h6 : 2 * (18 * Real.pi * (CA * D)) * 10 ^ 4 + 2 * (CA * D)
        ≤ 10 ^ 7 * CA * D := by
      have hcoeff : (2 * (18 * Real.pi) * 10 ^ 4 + 2 : ℝ) ≤ 10 ^ 7 := by
        nlinarith [Real.pi_lt_four]
      calc 2 * (18 * Real.pi * (CA * D)) * 10 ^ 4 + 2 * (CA * D)
          = (2 * (18 * Real.pi) * 10 ^ 4 + 2) * (CA * D) := by ring
        _ ≤ 10 ^ 7 * (CA * D) := mul_le_mul_of_nonneg_right hcoeff hCADnn
        _ = 10 ^ 7 * CA * D := by ring
    refine h1.trans ?_
    rw [hsplit]
    linarith [h3, h5, h6]
  have hgoal : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal (10 ^ 7 * CA * D) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu_int
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ)))]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [hDlin, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 10 ^ 7 * CA)]
  exact hgoal


/-- **The two-derivative weighted slice inequality from a pointwise Green bound.**  If every
`C²`-function on `(0, π/2)` with vanishing endpoint limits satisfies the Green bound
`|g θ| ≤ (π/8) ∫_{Ioc 0 (π/2)} |g''|`, then `∫⁻_θ g² σ ≤ C ∫⁻_θ (g'')² σ`. -/
theorem sliceHardy_of_pointwise
    (hgreen : ∀ g : ℝ → ℝ, ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun t => |deriv (fun s => deriv g s) t|)
        (Set.Ioc 0 (Real.pi / 2)) →
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |g θ| ≤ (Real.pi / 8) * ∫ t in Set.Ioc 0 (Real.pi / 2),
          |deriv (fun s => deriv g s) t|) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ,
      ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal ((Real.pi / 8) ^ 2 * (Real.pi / 2) * 10 ^ 4)
          * ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨(Real.pi / 8) ^ 2 * (Real.pi / 2) * 10 ^ 4, by positivity, ?_⟩
  intro g hsmooth hInt2 h0 hL
  have hIoo_ae : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
  have hsEta_ge_one : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [← hIoo_ae]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact Work.FTS.EllipticEst.H2W.one_le_sEta hθ
  have hsEta_aemeas : AEMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have hcont : ContinuousOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      fun θ hθ => (Work.FTS.EllipticEst.H2W.continuousAt_sEta hθ).continuousWithinAt
    have h1 : AEMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hcont.aemeasurable measurableSet_Ioo
    rwa [hIoo_ae] at h1
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  set D : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  have hDlin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = ENNReal.ofReal D := by
    rw [hD]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn2).symm
  have hsEta_int : MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.1
  -- integrability of `(g'')²`, of `|g''|` on `Iθ`, and hence on `Ioc 0 (π/2)`
  have hsq_int : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv g t) θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono'
      (f := fun θ => (deriv (fun t => deriv g t) θ) ^ 2)
      (g := fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      hInt2 ?_ ?_
    · have hfun : (fun θ => (deriv (fun t => deriv g t) θ) ^ 2)
          = fun θ => deriv (fun t => deriv g t) θ * deriv (fun t => deriv g t) θ := by
        funext θ; ring
      rw [hfun]
      exact ((measurable_deriv (fun t => deriv g t)).mul
        (measurable_deriv (fun t => deriv g t))).aestronglyMeasurable
    · filter_upwards [hsEta_ge_one] with θ hθ
      have h0' : (0 : ℝ) ≤ (deriv (fun t => deriv g t) θ) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0']
      exact le_mul_of_one_le_right h0' hθ
  have habs_int_Iθ : MeasureTheory.IntegrableOn
      (fun t => |deriv (fun s => deriv g s) t|) Work.Spaces.Iθ := by
    refine Integrable.mono' (hsq_int.add hsEta_int)
      (measurable_deriv (fun s => deriv g s)).abs.aestronglyMeasurable ?_
    filter_upwards [hsEta_ge_one] with t ht
    have hx1 : deriv (fun s => deriv g s) t
        ≤ (deriv (fun s => deriv g s) t) ^ 2 + Work.FTS.EllipticEst.sEta t := by
      nlinarith [sq_nonneg (deriv (fun s => deriv g s) t - 1 / 2)]
    have hx2 : -(deriv (fun s => deriv g s) t)
        ≤ (deriv (fun s => deriv g s) t) ^ 2 + Work.FTS.EllipticEst.sEta t := by
      nlinarith [sq_nonneg (deriv (fun s => deriv g s) t + 1 / 2)]
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    simp only [Pi.add_apply] at hx1 hx2 ⊢
    exact ⟨by linarith, hx1⟩
  have habs_int : MeasureTheory.IntegrableOn (fun t => |deriv (fun s => deriv g s) t|)
      (Set.Ioc 0 (Real.pi / 2)) :=
    habs_int_Iθ.mono_set (fun t ht => ⟨le_of_lt ht.1, ht.2⟩)
  set G : ℝ := ∫ t in Set.Ioc 0 (Real.pi / 2), |deriv (fun s => deriv g s) t| with hGdef
  have hGnn : 0 ≤ G := by
    rw [hGdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => abs_nonneg _)
  have hgb := hgreen g hsmooth habs_int h0 hL
  have hGle : G ≤ ∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t| := by
    rw [hGdef]
    refine MeasureTheory.setIntegral_mono_set habs_int_Iθ
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun t _ => abs_nonneg _)) ?_
    exact Filter.Eventually.of_forall (fun t ht => ⟨le_of_lt ht.1, ht.2⟩)
  -- Cauchy--Schwarz and the comparison with `D`
  have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def,
      Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0), sub_zero]
  have h1_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
    rw [memLp_two_iff_integrable_sq aestronglyMeasurable_const]
    simpa using integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have habs_memLp : MemLp (fun t => |deriv (fun s => deriv g s) t|) 2
      (volume.restrict Work.Spaces.Iθ) := by
    rw [memLp_two_iff_integrable_sq
      (measurable_deriv (fun s => deriv g s)).abs.aestronglyMeasurable]
    have h2 : (fun t => |deriv (fun s => deriv g s) t| ^ 2)
        = fun t => (deriv (fun s => deriv g s) t) ^ 2 := by
      funext t; rw [sq_abs]
    rw [h2]
    exact hsq_int
  have hcs := Work.Spaces.cs_integral (s := Work.Spaces.Iθ) (u := fun _ : ℝ => (1 : ℝ))
    (v := fun t => |deriv (fun s => deriv g s) t|) h1_memLp habs_memLp
  have hsq_le_D : (∫ t in Work.Spaces.Iθ, (deriv (fun s => deriv g s) t) ^ 2) ≤ D := by
    calc (∫ t in Work.Spaces.Iθ, (deriv (fun s => deriv g s) t) ^ 2)
        ≤ (∫⁻ t in Work.Spaces.Iθ,
            ENNReal.ofReal ((deriv (fun s => deriv g s) t) ^ 2)).toReal :=
          Work.FTS.EllipticEst.Honest.setIntegral_le_toReal_lintegral _
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun t _ => sq_nonneg _))
      _ ≤ (∫⁻ t in Work.Spaces.Iθ, ENNReal.ofReal
            ((deriv (fun s => deriv g s) t) ^ 2 * Work.FTS.EllipticEst.sEta t)).toReal := by
          refine ENNReal.toReal_mono ?_ ?_
          · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn2]
            exact ENNReal.ofReal_ne_top
          · refine MeasureTheory.lintegral_mono_ae ?_
            filter_upwards [hsEta_ge_one] with t ht
            rw [ENNReal.ofReal_le_ofReal_iff
              (mul_nonneg (sq_nonneg _) (le_trans zero_le_one ht))]
            have hx := mul_le_mul_of_nonneg_left ht (sq_nonneg (deriv (fun s => deriv g s) t))
            simpa only [mul_one] using hx
      _ = D := by rw [hDlin, ENNReal.toReal_ofReal hDnn]
  have hG'2 : (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2
      ≤ (Real.pi / 2) * D := by
    have h1 : (∫ t in Work.Spaces.Iθ, (|deriv (fun s => deriv g s) t|) ^ 2)
        = ∫ t in Work.Spaces.Iθ, (deriv (fun s => deriv g s) t) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun t _ => sq_abs _)
    simp only [one_mul, one_pow] at hcs
    rw [hvol, h1] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left hsq_le_D (by positivity))
  -- the pointwise bound for the slice and its integrability
  have haeIoo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [← hIoo_ae]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ ((Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2)
          * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [haeIoo] with θ hθ
    have h1 : |g θ| ≤ (Real.pi / 8) * G := hgb θ hθ
    have h4 : G ^ 2 ≤ (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2 := by
      nlinarith [hGnn, hGle, sq_nonneg (∫ t in Work.Spaces.Iθ,
        |deriv (fun s => deriv g s) t|)]
    have hsq : (g θ) ^ 2 ≤ (Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ,
        |deriv (fun s => deriv g s) t|) ^ 2 := by
      have h5 : ((Real.pi / 8) * G) ^ 2 ≤ (Real.pi / 8) ^ 2
          * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2 := by
        nlinarith [h4, sq_nonneg (Real.pi / 8)]
      calc (g θ) ^ 2 = |g θ| ^ 2 := (sq_abs _).symm
        _ ≤ ((Real.pi / 8) * G) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ ≤ (Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ,
              |deriv (fun s => deriv g s) t|) ^ 2 := h5
    have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
      Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    exact mul_le_mul_of_nonneg_right hsq hσ
  have hg2_int : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine Integrable.mono'
      (hsEta_int.const_mul ((Real.pi / 8) ^ 2
        * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2)) ?_ ?_
    · refine ((Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo hsmooth).pow 2).mul
        hsEta_aemeas.aestronglyMeasurable
    · filter_upwards [hpt, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ hmem
      have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hmem
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
      exact hθ
  have hreal : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ((Real.pi / 8) ^ 2 * (Real.pi / 2) * 10 ^ 4) * D := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            ((Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2)
              * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.integral_mono_ae hg2_int (hsEta_int.const_mul _) hpt
    have h2 : (∫ θ in Work.Spaces.Iθ,
          ((Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2)
            * Work.FTS.EllipticEst.sEta θ)
        = ((Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) := by
      rw [MeasureTheory.integral_const_mul]
    have h3 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10 ^ 4 :=
      Work.FTS.EllipticEst.H2W.integrableOn_sEta_and_integral_le.2
    have h4 : 0 ≤ (Real.pi / 8) ^ 2
        * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2 := by positivity
    have h5 : (Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2
          * 10 ^ 4
        ≤ ((Real.pi / 8) ^ 2 * (Real.pi / 2) * 10 ^ 4) * D := by
      nlinarith [hG'2, hDnn, h4, sq_nonneg (Real.pi / 8)]
    rw [h2] at h1
    refine h1.trans ?_
    calc (Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
        ≤ (Real.pi / 8) ^ 2 * (∫ t in Work.Spaces.Iθ, |deriv (fun s => deriv g s) t|) ^ 2
          * 10 ^ 4 := mul_le_mul_of_nonneg_left h3 h4
      _ ≤ ((Real.pi / 8) ^ 2 * (Real.pi / 2) * 10 ^ 4) * D := h5
  have hnn_g : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.sEta_nonneg_of_mem_Iθ hθ))
  have hgoal : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal ((Real.pi / 8) ^ 2 * (Real.pi / 2) * 10 ^ 4) * ENNReal.ofReal D := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg2_int hnn_g,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Real.pi / 8) ^ 2 * (Real.pi / 2) * 10 ^ 4)]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [hDlin]
  exact hgoal

end Main

/-- **Assembly.**  The target follows from the two pieces: the right-endpoint limit vanishing for
the class `AeData`, and the two-derivative weighted Hardy inequality. -/
theorem aesliceU_of
    (hB : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → ∀ z, 0 < z →
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ,
      ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal C
          * ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
          ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            ≤ ENNReal.ofReal C
              * ∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨CA, hCApos, hA'⟩ := hA
  refine ⟨10 ^ 7 * CA, by positivity, ?_⟩
  intro α u G h
  filter_upwards [h.momU, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hmom hz
  exact slice_le CA hCApos hA' h hz (hB α u G h z hz) hmom

theorem aesliceU : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ENNReal.ofReal C
            * ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ) :=
  aesliceU_of AeSliceRightTendsto SliceSigmaHardyTwo

end Work.FTS.EllipticEst.H2W.Ae
