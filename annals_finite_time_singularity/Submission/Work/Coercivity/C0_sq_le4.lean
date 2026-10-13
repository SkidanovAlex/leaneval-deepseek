import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.C0Defs
import Submission.Work.Coercivity.C0thetaIBP
import Submission.Work.Coercivity.SmoothNbhd_pth_slice
import Submission.Work.Coercivity.sq_integral_mul_le
import Submission.Work.Coercivity.L2CoercivityTransport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- Pointwise reduction of the angular density: with `c = cos θ`,
`(C0g θ)² = 324 (1-c²) c⁴ (5c²-3)²`. -/
private lemma C0g_sq_eq (θ : ℝ) :
    (C0g θ) ^ 2
      = 324 * (9 * (Real.cos θ)^4 + (-39) * (Real.cos θ)^6 + 55 * (Real.cos θ)^8
          + (-25) * (Real.cos θ)^10) := by
  have hs : Real.sin θ ^ 2 = 1 - (Real.cos θ) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  have h1 : C0g θ = 18 * Real.sin θ * (Real.cos θ) ^ 2 * (5 * (Real.cos θ) ^ 2 - 3) := by
    simp only [C0g]
    rw [hs]
    ring
  calc (C0g θ) ^ 2
      = 324 * (Real.sin θ)^2 * (Real.cos θ)^4 * (5 * (Real.cos θ)^2 - 3)^2 := by
        rw [h1]; ring
    _ = 324 * (9 * (Real.cos θ)^4 + (-39) * (Real.cos θ)^6 + 55 * (Real.cos θ)^8
          + (-25) * (Real.cos θ)^10) := by
        rw [hs]; ring

private lemma E2 : ∫ θ in (0:ℝ)..(π/2), (Real.cos θ)^4 = 3*π/16 := by
  rw [integral_cos_pow (n := 2)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero,
    integral_cos_sq]
  ring

private lemma E3 : ∫ θ in (0:ℝ)..(π/2), (Real.cos θ)^6 = 5*π/32 := by
  rw [integral_cos_pow (n := 4)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  rw [E2]; ring

private lemma E4 : ∫ θ in (0:ℝ)..(π/2), (Real.cos θ)^8 = 35*π/256 := by
  rw [integral_cos_pow (n := 6)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  rw [E3]; ring

private lemma E5 : ∫ θ in (0:ℝ)..(π/2), (Real.cos θ)^10 = 63*π/512 := by
  rw [integral_cos_pow (n := 8)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  rw [E4]; ring

private lemma E_lin :
    ∫ θ in (0:ℝ)..(π/2), (9*(Real.cos θ)^4 + (-39)*(Real.cos θ)^6 + 55*(Real.cos θ)^8 + (-25)*(Real.cos θ)^10)
      = 9*(3*π/16) + (-39)*(5*π/32) + 55*(35*π/256) + (-25)*(63*π/512) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [E2, E3, E4, E5]
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- `C0Ih = ∫_{Iθ} (C0g θ)² dθ = 1539 π/128 ≤ 64`. -/
private lemma C0Ih_le64 : C0Ih ≤ 64 := by
  have h0 : (0:ℝ) ≤ π/2 := by positivity
  have hIθ : ∫ θ in Spaces.Iθ, (C0g θ)^2 = ∫ θ in (0:ℝ)..(π/2), (C0g θ)^2 := by
    rw [Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le h0]
  have hpt : (fun θ : ℝ => (C0g θ)^2)
      = fun θ => 324 * (9 * (Real.cos θ)^4 + (-39) * (Real.cos θ)^6 + 55 * (Real.cos θ)^8
          + (-25) * (Real.cos θ)^10) := by
    funext θ; exact C0g_sq_eq θ
  calc C0Ih = ∫ θ in Spaces.Iθ, (C0g θ)^2 := rfl
    _ = ∫ θ in (0:ℝ)..(π/2), (C0g θ)^2 := hIθ
    _ = ∫ θ in (0:ℝ)..(π/2), 324 * (9*(Real.cos θ)^4 + (-39)*(Real.cos θ)^6 + 55*(Real.cos θ)^8 + (-25)*(Real.cos θ)^10) := by
        rw [hpt]
    _ = 324 * ∫ θ in (0:ℝ)..(π/2), (9*(Real.cos θ)^4 + (-39)*(Real.cos θ)^6 + 55*(Real.cos θ)^8 + (-25)*(Real.cos θ)^10) := by
        rw [intervalIntegral.integral_const_mul]
    _ = 324 * (9*(3*π/16) + (-39)*(5*π/32) + 55*(35*π/256) + (-25)*(63*π/512)) := by rw [E_lin]
    _ = 1539 * π / 128 := by ring
    _ ≤ 64 := by nlinarith [Real.pi_lt_d2]

/-- The integrand of `C0D` is `z²/(1+z)⁶` (everywhere, using Lean's totalised division). -/
private lemma C0D_integrand_eq (s : ℝ) :
    (1 / (s * (1 + s) * Spaces.w s)) ^ 2 = s ^ 2 / (1 + s) ^ 6 := by
  rcases eq_or_ne s 0 with rfl | hs
  · norm_num [Spaces.w]
  rcases eq_or_ne (1 + s) 0 with h1 | h1
  · rw [h1]; norm_num [Spaces.w]
  · simp only [Spaces.w]
    field_simp

/-- `C0D = ∫_0^∞ (z(1+z)w(z))⁻² dz = 1/30`. -/
private lemma C0D_eq : C0D = 1 / 30 := by
  rw [C0D]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => C0D_integrand_eq s)]
  rw [setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact integral_Iz_zsq_div_six

private lemma continuous_C0g : Continuous C0g := by
  unfold C0g
  fun_prop

private lemma continuousOn_w_Ioi : ContinuousOn Spaces.w (Set.Ioi (0 : ℝ)) := by
  unfold Spaces.w
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn (fun x hx => pow_ne_zero 2 (ne_of_gt hx))

private lemma integrableOn_inv_w_sq :
    IntegrableOn (fun s : ℝ => (1 / (s * (1 + s) * Spaces.w s)) ^ 2) Spaces.Iz :=
  integrable_Iz_zsq_div_six.congr (Eventually.of_forall (fun s => (C0D_integrand_eq s).symm))

theorem C0_sq_le4 (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (C0 f) ^ 2 ≤ 4 * Ef f := by
  -- ## The measure on the quadrant and the three test functions.
  set μ : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hμdef
  set J : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ with hJdef
  set A : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Spaces.w p.1 with hAdef
  set B : ℝ × ℝ → ℝ := fun p => C0g p.2 * (1 / (p.1 * (1 + p.1) * Spaces.w p.1)) with hBdef
  set H : ℝ × ℝ → ℝ := fun p => C0g p.2 * f p.1 p.2 / (p.1 * (1 + p.1)) with hHdef
  have hJmeas : MeasurableSet J := by
    rw [hJdef]; exact measurableSet_Ioi.prod measurableSet_Icc
  have hμJ : μ = (volume.prod volume).restrict J := by
    rw [hμdef, hJdef]
    have h1 : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
      (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h1, Measure.prod_restrict]
  have hmemJ : ∀ᵐ p ∂μ, p ∈ J := by
    rw [hμJ]; exact ae_restrict_mem hJmeas
  -- ## Continuity of `A`, `B`, `H` on `J`.
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) :=
    Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
      (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hfcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ) :=
    hsm.continuousOn.mono hsub
  have hwcont : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) (Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ) :=
    continuousOn_w_Ioi.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hAcont : ContinuousOn A J := by rw [hAdef, hJdef]; exact hfcont.mul hwcont
  have hBcont : ContinuousOn B J := by
    rw [hBdef, hJdef]
    refine ContinuousOn.mul (continuous_C0g.comp_continuousOn continuous_snd.continuousOn) ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((continuous_fst.mul (continuous_const.add continuous_fst)).continuousOn).mul hwcont
    · intro p hp
      have hp1 : 0 < p.1 := hp.1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      have hw : Spaces.w p.1 ≠ 0 := by unfold Spaces.w; positivity
      exact mul_ne_zero (mul_ne_zero (ne_of_gt hp1) (ne_of_gt h1p1)) hw
  have hHcont : ContinuousOn H J := by
    rw [hHdef, hJdef]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_C0g.comp_continuousOn continuous_snd.continuousOn).mul hfcont
    · exact (continuous_fst.mul (continuous_const.add continuous_fst)).continuousOn
    · intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      exact mul_ne_zero (ne_of_gt hp1) (ne_of_gt h1p1)
  have hA_aesm : AEStronglyMeasurable A μ := by
    rw [hμJ]; exact hAcont.aestronglyMeasurable hJmeas
  have hB_aesm : AEStronglyMeasurable B μ := by
    rw [hμJ]; exact hBcont.aestronglyMeasurable hJmeas
  have hH_aesm : AEStronglyMeasurable H μ := by
    rw [hμJ]; exact hHcont.aestronglyMeasurable hJmeas
  -- ## Integrability.
  have hA2int : Integrable (fun p : ℝ × ℝ => A p ^ 2) μ := by
    rw [hAdef]
    have h := hint
    rw [IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at h
    rw [hμdef]
    exact h
  have hC0g2_int : IntegrableOn (fun θ : ℝ => (C0g θ) ^ 2) Spaces.Iθ :=
    (continuous_C0g.pow 2).continuousOn.integrableOn_Icc
  have hB2int : Integrable (fun p : ℝ × ℝ => B p ^ 2) μ := by
    rw [hBdef]
    have h1 : (fun p : ℝ × ℝ => (C0g p.2 * (1 / (p.1 * (1 + p.1) * Spaces.w p.1))) ^ 2)
        = fun p : ℝ × ℝ => (1 / (p.1 * (1 + p.1) * Spaces.w p.1)) ^ 2 * (C0g p.2) ^ 2 := by
      funext p; rw [mul_pow]; ring
    rw [h1, hμdef]
    exact integrableOn_inv_w_sq.mul_prod hC0g2_int
  have hHdom : Integrable (fun p : ℝ × ℝ => (1 / 2) * (A p ^ 2 + B p ^ 2)) μ :=
    (hA2int.add hB2int).const_mul (1 / 2)
  have hHint : Integrable H μ := by
    refine Integrable.mono' hHdom hH_aesm ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwpos : 0 < Spaces.w p.1 := by unfold Spaces.w; positivity
    have hden : 0 < p.1 * (1 + p.1) := by positivity
    have hAeq : A p ^ 2 = (|f p.1 p.2| * Spaces.w p.1) ^ 2 := by
      rw [hAdef, mul_pow, mul_pow, sq_abs]
    have hBeq : B p ^ 2 = (|C0g p.2| * (1 / (p.1 * (1 + p.1) * Spaces.w p.1))) ^ 2 := by
      rw [hBdef, mul_pow, mul_pow, sq_abs]
    have hHeq : ‖H p‖ = (|f p.1 p.2| * Spaces.w p.1) *
        (|C0g p.2| * (1 / (p.1 * (1 + p.1) * Spaces.w p.1))) := by
      simp only [hHdef]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hden]
      have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
      have hwne : Spaces.w p.1 ≠ 0 := ne_of_gt hwpos
      field_simp
    rw [hHeq, hAeq, hBeq]
    nlinarith [two_mul_le_add_sq (|f p.1 p.2| * Spaces.w p.1)
      (|C0g p.2| * (1 / (p.1 * (1 + p.1) * Spaces.w p.1)))]
  -- ## Fubini and the identification with the double integral.
  have hH_fub : (∫ s in Spaces.Iz, ∫ θ in Spaces.Iθ, H (s, θ)) = ∫ p, H p ∂μ := by
    have hint := hHint
    rw [hμdef] at hint ⊢
    exact (integral_prod H hint).symm
  have hX : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)))
      = ∫ p, A p * B p ∂μ := by
    have hfill : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)))
        = ∫ s in Spaces.Iz, ∫ θ in Spaces.Iθ, H (s, θ) := by
      rw [hHdef]
      exact setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))
    rw [hfill, hH_fub]
    refine integral_congr_ae ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwne : Spaces.w p.1 ≠ 0 := by unfold Spaces.w; positivity
    have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
    have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
    have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
    rw [hHdef, hAdef, hBdef]
    field_simp
  -- ## Cauchy–Schwarz and the two integrals.
  have hcs : (∫ p, A p * B p ∂μ) ^ 2 ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) :=
    sq_integral_mul_le μ A B hA_aesm hB_aesm hA2int hB2int
  have hA2eq : ∫ p, A p ^ 2 ∂μ = Ef f := by
    have hint := hA2int
    rw [hAdef] at hint ⊢
    rw [hμdef] at hint ⊢
    rw [integral_prod (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) hint]
    rfl
  have hB2eq : ∫ p, B p ^ 2 ∂μ = C0Ih * C0D := by
    have h1 : (fun p : ℝ × ℝ => B p ^ 2)
        = fun p : ℝ × ℝ => (1 / (p.1 * (1 + p.1) * Spaces.w p.1)) ^ 2 * (C0g p.2) ^ 2 := by
      funext p; rw [hBdef, mul_pow]; ring
    rw [h1, hμdef]
    rw [integral_prod_mul (f := fun s : ℝ => (1 / (s * (1 + s) * Spaces.w s)) ^ 2)
      (g := fun θ : ℝ => (C0g θ) ^ 2)]
    have hC0D' : (∫ s in Spaces.Iz, (1 / (s * (1 + s) * Spaces.w s)) ^ 2) = C0D :=
      (setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [show C0Ih = ∫ θ in Spaces.Iθ, (C0g θ) ^ 2 from rfl, hC0D']
    ring
  -- ## The numeric bounds.
  have hnum : C0Ih * C0D ≤ 4 := by
    rw [C0D_eq]
    have h3 : 0 ≤ C0Ih := by rw [C0Ih]; exact integral_nonneg (fun θ => sq_nonneg _)
    nlinarith [C0Ih_le64, h3]
  have hEf : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- ## The angular integration by parts giving `C0 f` as an explicit double integral.
  have hC0 : C0 f = -∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)) := by
    have step1 : C0 f = ∫ s in Set.Ioi (0 : ℝ), FM.L12dens Spaces.K (Transport f) s := by
      rw [C0, L12f, FM.L12]
    rw [step1]
    have step2 : (∫ s in Set.Ioi (0 : ℝ), FM.L12dens Spaces.K (Transport f) s)
        = ∫ s in Set.Ioi (0 : ℝ),
            (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0h θ * Spaces.pth f s θ := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      have hs0 : s ≠ 0 := ne_of_gt hs'
      have hs1 : (1 : ℝ) + s ≠ 0 := by
        have hs0' : (0 : ℝ) < s := hs'
        have : (0 : ℝ) < 1 + s := by linarith
        exact ne_of_gt this
      rw [FM.L12dens]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall (fun θ => ?_))
      simp only [Transport, Spaces.Dth, C0h, Spaces.K]
      field_simp
    rw [step2]
    have step3 : (∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0h θ * Spaces.pth f s θ)
        = -∫ s in Set.Ioi (0 : ℝ),
            (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0g θ * f s θ := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      obtain ⟨hgd, hgi⟩ := SmoothNbhd_pth_slice f hsm s (le_of_lt hs')
      rw [C0thetaIBP (fun θ => f s θ) (Spaces.pth f s) hgd hgi]
      ring
    rw [step3]
    have step4 : (∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0g θ * f s θ)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      rw [integral_div]
      ring
    rw [step4]
  calc (C0 f) ^ 2
      = (∫ p, A p * B p ∂μ) ^ 2 := by rw [hC0, hX]; ring
    _ ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) := hcs
    _ = Ef f * (C0Ih * C0D) := by rw [hA2eq, hB2eq]
    _ ≤ Ef f * 4 := by nlinarith [hnum, hEf]
    _ = 4 * Ef f := by ring


end Work.Coercivity
