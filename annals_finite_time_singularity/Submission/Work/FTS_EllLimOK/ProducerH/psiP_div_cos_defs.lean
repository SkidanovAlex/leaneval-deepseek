import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StreamBdryIface.Producers
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS_EllLimOK.L2Mem_of_HkMem_zero
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `psiP/cos θ` chain: definitions

This module fixes the vocabulary of the estimate `psiP_div_cos` (the `U`-slot part
`Φ = psiP α Φ` of a stream function, divided by `cos θ`, is `ℋ⁰` with quantitative bounds).

* `beta α = 3/α - 1` is the exponent of the kernel in the representation
  `psiP α Φ z θ = -(sin(2θ)/α) ∫₀¹ v^{3/α-1} U'(zv,θ) dv`.
* `mom U z = ∫_θ U z θ² sin(2θ)^{-η}` is the angular moment `M₁(z)` of the `U`-slot.
* `mass α U z = ∫_θ HkIntegrand α 0 U z θ` is the level-`0` angular slice mass; the two are
  related by `mass α U z = w(z)² · mom U z` (`mass_eq_w2_mom`), because at level `0` the
  `ℋ⁰`-integrand is `(U z θ · w z / sin(2θ)^{η/2})²`.
* `Gf α U z = w(z)² ∫₀¹ v^β mom U (zv) dv` is the radial density dominating the `ℋ⁰`-slices of
  `Φ/cos θ`.
* `Xf Φ z θ = Φ z θ / cos θ`.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- The exponent `β = 3/α - 1` of the kernel in the `psiP` representation. -/
def beta (α : ℝ) : ℝ := 3 / α - 1

/-- `M₁(z) = ∫_θ U(z,θ)² sin(2θ)^{-η}`: the angular moment of the `U`-slot. -/
def mom (U : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ

/-- `A(z) = ∫_θ HkIntegrand α 0 U z θ`: the level-`0` angular slice mass of `U`. -/
def mass (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 U z θ

/-- The radial density `G(z) = w(z)² ∫₀¹ v^β M₁(zv) dv` dominating the `ℋ⁰`-slices of `Φ/cos θ`. -/
def Gf (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * ∫ v in (0 : ℝ)..1, v ^ (beta α) * mom U (z * v)

/-- The quotient `Φ / cos θ`. -/
def Xf (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Φ z θ / Real.cos θ

/-! ## Elementary properties of `mom` and `mass` -/

theorem mom_nonneg (U : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ mom U z :=
  setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)

theorem mass_nonneg (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ mass α U z :=
  setIntegral_nonneg measurableSet_Icc fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 U z θ

/-- At level `0` the `ℋ⁰`-integrand is exactly `(U·w/sin(2θ)^{η/2})²`. -/
theorem HkIntegrand_zero_eq' (α : ℝ) (U : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 U z θ
      = (U z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.DzIter]

/-- At level `0` the `ℋ⁰`-integrand is `U²·w²·σ` on the angular interval. -/
theorem HkIntegrand_eq_w2_sig (α : ℝ) (U : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 U z θ
      = (Work.Spaces.w z) ^ 2 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  rw [HkIntegrand_zero_eq', Work.FTS.EllipticEst.AngSecond.sq_mul_W U hθ]
  simp only [Work.FTS.EllipticEst.AngSecond.w2]
  ring

/-- The slice mass is the radial weight times the angular moment. -/
theorem mass_eq_w2_mom (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) :
    mass α U z = (Work.Spaces.w z) ^ 2 * mom U z := by
  have hEq : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 U z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) :=
    setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
      (fun θ hθ => HkIntegrand_eq_w2_sig α U hθ)
  rw [mass, mom, hEq, integral_const_mul]

/-- The slice mass vanishes at `z = 0`. -/
theorem mass_zero (α : ℝ) (U : ℝ → ℝ → ℝ) : mass α U 0 = 0 := by
  rw [mass]
  have h : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 U 0 θ) = fun _ => (0 : ℝ) := by
    funext θ
    rw [HkIntegrand_zero_eq']
    simp [Work.Spaces.w]
  rw [h, integral_zero]

/-- `w(z)² z⁴ = (1+z)⁴` for `z ≠ 0`. -/
theorem w_sq_mul_z4 {z : ℝ} (hz : z ≠ 0) : (Work.Spaces.w z) ^ 2 * z ^ 4 = (1 + z) ^ 4 := by
  have h : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 (pow_ne_zero 2 hz))]
  ring

/-- `1 ≤ w(z)² z⁴` for `z > 0`. -/
theorem one_le_w2_mul_z4 {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 * z ^ 4 := by
  rw [w_sq_mul_z4 (ne_of_gt hz)]
  exact one_le_pow₀ (by linarith)

/-- `mom U z = mass α U z / w(z)²` for `z > 0`. -/
theorem mom_eq_mass_div (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    mom U z = mass α U z / (Work.Spaces.w z) ^ 2 := by
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  rw [mass_eq_w2_mom, eq_div_iff (pow_ne_zero 2 hw)]
  ring

/-- `M₁(z) ≤ z⁴ A(z)` for `z > 0`. -/
theorem mom_le_mass_mul_z4 (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    mom U z ≤ z ^ 4 * mass α U z := by
  have hw : 0 < (Work.Spaces.w z) ^ 2 := by rw [Work.Spaces.w]; positivity
  rw [mom_eq_mass_div α U hz, div_le_iff₀ hw]
  have h1 : 1 ≤ (Work.Spaces.w z) ^ 2 * z ^ 4 := one_le_w2_mul_z4 hz
  have h2 := mul_le_mul_of_nonneg_left h1 (mass_nonneg α U z)
  nlinarith [h2]

/-- `M₁(z) ≤ A(z)` for `z ≥ 1`. -/
theorem mom_le_mass_of_one_le (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 1 ≤ z) :
    mom U z ≤ mass α U z := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 :=
    one_le_pow₀ (Work.FTS_EllLimOK.one_le_w z hz0)
  have hwpos : 0 < (Work.Spaces.w z) ^ 2 := lt_of_lt_of_le zero_lt_one hw
  rw [mom_eq_mass_div α U hz0, div_le_iff₀ hwpos]
  nlinarith [mass_nonneg α U z]


/-! ## Integrability and measurability of `mass` and `mom` -/

/-- `A = mass α U` is integrable on `(0,∞)` whenever `U ∈ ℋ⁰`. -/
theorem mass_integrableOn (α : ℝ) (U : ℝ → ℝ → ℝ) (hU : Work.Spaces.HkMem α 0 U) :
    IntegrableOn (mass α U) (Set.Ioi 0) := by
  have h : IntegrableOn (mass α U) Work.Spaces.Iz := hU.2
  have hmeas : MeasureTheory.Measure.restrict volume (Set.Ioi (0 : ℝ))
      = MeasureTheory.Measure.restrict volume (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  rw [Work.Spaces.Iz] at h
  unfold MeasureTheory.IntegrableOn at h ⊢
  rw [hmeas]
  exact h

/-- `∫_{(0,∞)} A = HkSq α 0 U`. -/
theorem mass_Ioi_eq_HkSq (α : ℝ) (U : ℝ → ℝ → ℝ) :
    ∫ z in Set.Ioi (0 : ℝ), mass α U z = Work.Spaces.HkSq α 0 U := by
  rw [Work.Spaces.HkSq, Work.Spaces.Iz]
  exact (MeasureTheory.integral_Ici_eq_integral_Ioi (f := mass α U) (x := (0 : ℝ))).symm

theorem mass_aesm (α : ℝ) (U : ℝ → ℝ → ℝ) (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.AEStronglyMeasurable (mass α U)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (mass_integrableOn α U hU).aestronglyMeasurable

theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
    exact ContinuousOn.div ((continuous_const.add continuous_id).pow 2).continuousOn
      (continuous_id.pow 2).continuousOn
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact h.pow 2

theorem mom_aesm (α : ℝ) (U : ℝ → ℝ → ℝ) (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.AEStronglyMeasurable (mom U)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z => ((Work.Spaces.w z) ^ 2)⁻¹) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (continuousOn_w_sq.inv₀ (fun z hz => by
      have hz0 : (0 : ℝ) < z := hz
      rw [Work.Spaces.w]
      positivity)).aestronglyMeasurable measurableSet_Ioi
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => mass α U z * ((Work.Spaces.w z) ^ 2)⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (mass_aesm α U hU).mul h2
  have hH : (fun z => mass α U z * ((Work.Spaces.w z) ^ 2)⁻¹)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] mom U := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [mom_eq_mass_div α U hz, div_eq_mul_inv]
  exact h1.congr hH

/-! ## The moment bound -/

/-- `∫_θ sin(2θ)^{-η} ≤ 10⁴`. -/
theorem integral_sin_rpow_le :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10 ^ 4 := by
  have hp : (-1 : ℝ) < -(Work.Spaces.eta) := by norm_num [Work.Spaces.eta]
  have hp0 : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hp hp0).2
  refine le_trans h (le_of_eq ?_)
  norm_num [Work.Spaces.eta]

theorem integrableOn_sin_rpow_neg :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hp : (-1 : ℝ) < -(Work.Spaces.eta) := by norm_num [Work.Spaces.eta]
  have hp0 : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
  exact (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hp hp0).1

/-- The angular moment is bounded by `M²·10⁴` when `|U| ≤ M` on the open angular interval. -/
theorem mom_le_of_bound (U : ℝ → ℝ → ℝ) {M z : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo 0 (π / 2), |U z θ| ≤ M) :
    mom U z ≤ M ^ 2 * 10 ^ 4 := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIoo : MeasurableSet (Set.Ioo (0 : ℝ) (π / 2)) := measurableSet_Ioo
  -- the comparison is a.e. on `Iθ`: the endpoints do not matter
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have heq : volume.restrict (Set.Ioo (0 : ℝ) (π / 2))
        = volume.restrict Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.restrict_Ioo_eq_restrict_Icc
    rw [← heq]
    exact MeasureTheory.ae_restrict_of_forall_mem hIoo (fun θ hθ => hθ)
  have hsig : IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using integrableOn_sin_rpow_neg
  have hsigint : ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ ≤ 10 ^ 4 := by
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using integral_sin_rpow_le
  have hmono : ∫ θ in Work.Spaces.Iθ,
        (U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ ∫ θ in Work.Spaces.Iθ, M ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hsig.const_mul (M ^ 2)) ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem hIθ
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
    · filter_upwards [hae] with θ hθ
      have h1 : (U z θ) ^ 2 ≤ M ^ 2 := by
        have := h θ hθ
        nlinarith [abs_nonneg (U z θ), sq_abs (U z θ), hM0]
      exact mul_le_mul_of_nonneg_right h1 (Work.FTS.EllipticEst.AngSecond.sig_nonneg
        (by rw [Work.Spaces.Iθ]; exact Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  have hval : ∫ θ in Work.Spaces.Iθ, M ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = M ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ :=
    integral_const_mul _ _
  rw [mom]
  refine le_trans hmono (le_trans (le_of_eq hval) ?_)
  nlinarith [hsigint, sq_nonneg M]

/-- Substitution `t = zv` in the defining integral of `Gf`'s inner part. -/
theorem mom_subst (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ v in (0 : ℝ)..1, v ^ (beta α) * mom U (z * v)
      = z ^ (-(beta α + 1)) * ∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t := by
  simpa only [mul_comm] using
    Work.FTS.PhiStar.RadialWAux.integral_zero_one_rpow (mom U) (beta α) hz

end Work.FTS_EllLimOK.ProducerH
