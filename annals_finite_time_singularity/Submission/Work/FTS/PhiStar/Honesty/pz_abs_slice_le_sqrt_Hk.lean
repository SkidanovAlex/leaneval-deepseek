import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable
import Submission.Work.PhiStar.Honesty.sq_integral_sqrt_mul_le
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slice of `∂_zF` is bounded by the square root of the `H^1` integrand

For a source `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` and honest in the
weighted space `ℋ^1` (`Work.Spaces.HkMem α 1 F`), the angular slice of the radial derivative
at radius `t > 0` satisfies

  `∫_{Iθ} |∂_zF(t,θ)| dθ ≤ √(π/2) · t/(1+t)² · √(∫_{Iθ} HkIntegrand α 1 F t θ dθ)`.

**Route.**  The `i = 1` summand of the `ℋ^1`-integrand is

  `(D_z ∂_zF · w(t)/sin(2θ)^{η/2})² = (t·∂_zF(t,θ)·w(t)/sin(2θ)^{η/2})²`,

and `t·w(t) = (1+t)²/t`, so on the interior of `Iθ` (where `sin(2θ) > 0` and hence
`sin(2θ)^{η/2} ≤ 1`) that summand dominates `((1+t)²/t · ∂_zF)²`.  Inverting the factor
`(1+t)²/t = 1/c` with `c = t/(1+t)²` gives the *pointwise* bound

  `|∂_zF(t,θ)|² ≤ c² · HkIntegrand α 1 F t θ`,

hence `|∂_zF(t,θ)| ≤ c · √(HkIntegrand α 1 F t θ)`.  The two endpoints `0, π/2` are null.
Integrating this a.e. inequality (both sides are integrable: the left one by
`slice_abs_integrable`, the right one since `√x ≤ x + 1`) and applying Cauchy–Schwarz
(`sq_integral_sqrt_mul_le` with the constant function `1`, whose integral over `Iθ` is
`π/2`) gives the claim.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **Pointwise bound.**  On the interior of the angular interval the square of the radial
derivative of the slice is dominated by the `ℋ^1`-integrand, with the constant
`(t/(1+t)²)²` coming from the radial weight `w(t) = (1+t)²/t²` and the `t` of `D_z`. -/
private lemma pz_sq_le_HkIntegrand {α : ℝ} {F : ℝ → ℝ → ℝ} {t θ : ℝ} (ht : 0 < t)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.pz F t θ) ^ 2
      ≤ (t / (1 + t) ^ 2) ^ 2 * Work.Spaces.HkIntegrand α 1 F t θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hse : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs _
  have hse1 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hs.le (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
  -- the `i = 1` summand of the integrand
  have hterm := Work.Spaces.sq_le_HkIntegrand_z α 1 F t θ 1 le_rfl
  have hDz : Work.Spaces.DzIter 1 F t θ = t * Work.Spaces.pz F t θ := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  rw [hDz] at hterm
  set A : ℝ := t * (Work.Spaces.w t / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) with hA
  have hterm' : (Work.Spaces.pz F t θ * A) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ := by
    have heq : Work.Spaces.pz F t θ * A
        = t * Work.Spaces.pz F t θ
          * (Work.Spaces.w t / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) := by
      rw [hA]; ring
    rwa [heq]
  have hpz_sq : (Work.Spaces.pz F t θ) ^ 2 * A ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ := by
    have : (Work.Spaces.pz F t θ * A) ^ 2 = (Work.Spaces.pz F t θ) ^ 2 * A ^ 2 := mul_pow _ _ 2
    rwa [this] at hterm'
  -- `A = u/sin(2θ)^{η/2}` with `u = (1+t)²/t ≥ 4`, and `sin(2θ)^{η/2} ≤ 1`, so `A ≥ u`
  set u : ℝ := (1 + t) ^ 2 / t with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hAw : A = u / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [hA, hu, Work.Spaces.w]
    field_simp
  have hAge : u ≤ A := by
    rw [hAw, le_div_iff₀ hse]
    exact mul_le_of_le_one_right hu0.le hse1
  have hAge2 : u ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hu0.le hAge 2
  have hpu : (Work.Spaces.pz F t θ) ^ 2 * u ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ :=
    le_trans (mul_le_mul_of_nonneg_left hAge2 (sq_nonneg _)) hpz_sq
  have h1 : (Work.Spaces.pz F t θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 F t θ / u ^ 2 :=
    (le_div_iff₀ (pow_pos hu0 2)).mpr hpu
  -- `t/(1+t)² = 1/u`
  have hcu : t / (1 + t) ^ 2 = 1 / u := by rw [hu]; field_simp
  calc (Work.Spaces.pz F t θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 F t θ / u ^ 2 := h1
    _ = (t / (1 + t) ^ 2) ^ 2 * Work.Spaces.HkIntegrand α 1 F t θ := by
        rw [hcu, one_div, inv_pow, div_eq_mul_inv]
        ring

/-- **Pointwise square-root bound**: the absolute value of the radial derivative of the slice
is dominated by `t/(1+t)²` times the square root of the `ℋ^1`-integrand. -/
private lemma pz_abs_le_sqrt_HkIntegrand {α : ℝ} {F : ℝ → ℝ → ℝ} {t θ : ℝ} (ht : 0 < t)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Work.Spaces.pz F t θ|
      ≤ (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := by
  have hsq := pz_sq_le_HkIntegrand (α := α) (F := F) ht hθ
  rw [← sq_abs (Work.Spaces.pz F t θ)] at hsq
  have hc : 0 ≤ t / (1 + t) ^ 2 := by positivity
  have h1 : Real.sqrt ((|Work.Spaces.pz F t θ|) ^ 2) = |Work.Spaces.pz F t θ| := by
    rw [Real.sqrt_sq_eq_abs, abs_abs]
  have h2 : Real.sqrt ((t / (1 + t) ^ 2) ^ 2 * Work.Spaces.HkIntegrand α 1 F t θ)
      = (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
  have := Real.sqrt_le_sqrt hsq
  rwa [h1, h2] at this

theorem pz_abs_slice_le_sqrt_Hk {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {t : ℝ} (ht : 0 < t) :
    (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
      ≤ Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by
  have hcpos : 0 < t / (1 + t) ^ 2 := by positivity
  have hHk : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ) Work.Spaces.Iθ :=
    hF.1 t (Set.mem_Ici.mpr ht.le)
  have hcone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- `√(HkIntegrand)` is integrable on the slice, by `√x ≤ x + 1`
  have hsqrt_int : IntegrableOn (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ))
      Work.Spaces.Iθ := by
    have hdom : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ + 1)
        Work.Spaces.Iθ := hHk.add hcone
    refine Integrable.mono' hdom ?_ ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hHk.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun θ => ?_)
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hnn := Work.Spaces.HkIntegrand_nonneg α 1 F t θ
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
  -- the two endpoints of `Iθ` are null
  have hmeq : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))).symm
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.pz F t θ|
        ≤ (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := by
    rw [hmeq]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => pz_abs_le_sqrt_HkIntegrand (α := α) (F := F) ht hθ)
  have hint1 : IntegrableOn (fun θ : ℝ => |Work.Spaces.pz F t θ|) Work.Spaces.Iθ :=
    (Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hF ht).2
  have hint2 : IntegrableOn
      (fun θ : ℝ => (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ))
      Work.Spaces.Iθ := hsqrt_int.const_mul _
  have hmono : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) :=
    integral_mono_ae hint1 hint2 hpt
  -- Cauchy–Schwarz with the constant function `1`
  have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le (s := Work.Spaces.Iθ) measurableSet_Icc
    (A := fun _ : ℝ => (1 : ℝ))
    (B := fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ)
    hcone hHk (fun _ _ => zero_le_one) (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 1 F t θ)
  have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Work.Spaces.Iθ]
    simp only [Measure.real, Real.volume_Icc, sub_zero]
    exact ENNReal.toReal_ofReal (by positivity)
  have hsqrt_cs : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ))
      ≤ Real.sqrt (Real.pi / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by
    have hsq_le : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ)) ^ 2
        ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by
      have h := hcs
      simp only [Real.sqrt_one, one_mul] at h
      rwa [hvol] at h
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) :=
      integral_nonneg (fun θ => Real.sqrt_nonneg _)
    have hstep := Real.sqrt_le_sqrt hsq_le
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hstep
    exact hstep
  calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (t / (1 + t) ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) := hmono
    _ = (t / (1 + t) ^ 2)
          * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 1 F t θ) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (t / (1 + t) ^ 2) * (Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ)) :=
        mul_le_mul_of_nonneg_left hsqrt_cs hcpos.le
    _ = Real.sqrt (Real.pi / 2) * (t / (1 + t) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) := by ring

end Work.FTS.PhiStar.Honesty
