/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted first-order Poincaré inequality on the angular slice `[0, π/2]`

`Work.FTS.EllipticEst.TanTheta.slice_poincare_eta`: there is `K > 0` such that every `C²` function
`u` on a neighbourhood of `[0, π/2]` with `u 0 = u (π/2) = 0` satisfies

  `∫_{Iθ} (u')² · sin(2θ)^{-η} ≤ K · ∫_{Iθ} (u'')² · sin(2θ)^{-η}`,  `η = 99/100`.

Route (the one described in the docstring of the statement).  Since `u 0 = u (π/2) = 0`, Rolle's
theorem gives a zero `θ₀ ∈ (0, π/2)` of `u'`; the fundamental theorem of calculus gives
`u' θ = ∫_{θ₀}^{θ} u''` for every `θ ∈ Iθ`, hence, by Cauchy–Schwarz on the interval
(`sq_integral_le` below),

  `(u' θ)² ≤ |θ - θ₀| · ∫_{θ₀}^{θ} (u'')² ≤ (π/2) · A`,   `A = ∫_{Iθ} (u'')²`.

Multiplying by the weight `w θ = sin(2θ)^{-η} ≥ 0` and integrating over `Iθ` gives
`∫_{Iθ} (u')² w ≤ (π/2) · A · W` with `W = ∫_{Iθ} w`.  On `(0, π/2)` one has `w ≥ 1`, so
`A ≤ ∫_{Iθ} (u'')² w`, and `W ≤ 100/(1 - η) = 10000` is the quantitative integrability bound for
`sin(2θ)^{-η}` (proved in `Work.FTS.LocData.integral_sin_two_rpow_neg`).  Since `π < 4`, the
constant `K = 20000` works (as would anything at least `(π/2)·10000 = 5000π`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false

/-- **Cauchy–Schwarz on an interval.**  For a continuous real function `f` on `[a,b]` with
`a ≤ b`, the square of the integral of `f` is at most the length of the interval times the
integral of `f²`:

  `(∫_a^b f)² ≤ (b - a) · ∫_a^b f²`.

This is Cauchy–Schwarz applied to `f` and the constant function `1`.  The proof below is the
elementary one: with `c = (∫_a^b f)/(b-a)` one has
`0 ≤ ∫_a^b (f - c)² = ∫_a^b f² - 2c ∫_a^b f + c²(b-a)`, and substituting `c` yields
`c²(b-a) ≤ ∫_a^b f²`, i.e. `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
theorem sq_integral_le (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  · have hba : 0 < b - a := sub_pos.mpr h
    have hfI : IntervalIntegrable f volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]
      exact hf
    set c : ℝ := (∫ t in a..b, f t) / (b - a) with hc
    have hcba : c * (b - a) = ∫ t in a..b, f t := by
      rw [hc]
      exact div_mul_cancel₀ _ (ne_of_gt hba)
    have h1 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]
      exact hf.pow 2
    have h2 : IntervalIntegrable (fun t => 2 * c * f t) volume a b := hfI.const_mul (2 * c)
    have h3 : IntervalIntegrable (fun t : ℝ => c ^ 2) volume a b := intervalIntegrable_const
    have hnn : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun t => sq_nonneg _)
    have hexp : (∫ t in a..b, (f t - c) ^ 2)
        = (∫ t in a..b, (f t) ^ 2) - 2 * c * (∫ t in a..b, f t) + c ^ 2 * (b - a) := by
      have e : (∫ t in a..b, (f t - c) ^ 2)
          = ∫ t in a..b, ((f t) ^ 2 - 2 * c * f t + c ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      rw [e, intervalIntegral.integral_add (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hexp] at hnn
    have hkey : c ^ 2 * (b - a) ≤ ∫ t in a..b, (f t) ^ 2 := by
      have hh := hnn
      rw [← hcba] at hh
      nlinarith [hh]
    calc (∫ t in a..b, f t) ^ 2 = (c * (b - a)) ^ 2 := by rw [← hcba]
      _ = (c ^ 2 * (b - a)) * (b - a) := by ring
      _ ≤ (∫ t in a..b, (f t) ^ 2) * (b - a) := mul_le_mul_of_nonneg_right hkey hba.le
      _ = (b - a) * ∫ t in a..b, (f t) ^ 2 := by ring

/-- Weighted first-order Poincare inequality with the `sin(2θ)^{-η}` weight (`η = 99/100`):
there is `K > 0` such that every `C²` function `u` on a neighbourhood of `[0, π/2]` with
`u 0 = 0` and `u (π/2) = 0` satisfies
`∫_0^{π/2} (u')² · sin(2θ)^{-η} ≤ K · ∫_0^{π/2} (u'')² · sin(2θ)^{-η}`.
Since `∫_0^{π/2} u' = u(π/2) - u(0) = 0`, the continuous `u'` has a zero `θ₀`; then
`u' θ = ∫_{θ₀}^{θ} u''`, so `|u' θ|² ≤ (π/2) ∫_0^{π/2} (u'')²` and it suffices to multiply by
`sin(2θ)^{-η} ≥ 1` (a.e.) and integrate, with `K = (π/2)·∫_0^{π/2} sin(2θ)^{-η} dθ`. -/
theorem slice_poincare_eta : ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ → ℝ,
    ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)) → u 0 = 0 → u (Real.pi / 2) = 0 →
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ K * (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  refine ⟨20000, by norm_num, ?_⟩
  intro u hu hu0 hu1
  have hpi2pos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hη : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  set w : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hwdef
  change (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * w θ)
      ≤ 20000 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * w θ)
  -- integrability and the quantitative bound for the weight `w`
  have hηpos : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have hηlt : Work.Spaces.eta < 1 := by norm_num [Work.Spaces.eta]
  obtain ⟨hw_int0, hw_le0⟩ :=
    Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta hηpos hηlt
  have hw_int : IntegrableOn w Work.Spaces.Iθ := hw_int0
  have hW_le : (∫ θ in Work.Spaces.Iθ, w θ) ≤ 10000 := by
    have hval : (100 : ℝ) / (1 - Work.Spaces.eta) = 10000 := by
      norm_num [Work.Spaces.eta]
    rw [hval] at hw_le0
    exact hw_le0
  -- smoothness of the two derivatives on the open strip
  have hder1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hu.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv u)) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    (hder1.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn
  have hdiff1 : DifferentiableOn ℝ (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hder1.differentiableOn (by norm_num)
  have hcontdu : ContinuousOn (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) := hder1.continuousOn
  have hw_nonneg_on : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w θ := by
    intro θ hθ
    apply Real.rpow_nonneg
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  -- the unweighted second-derivative integral `A`
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 with hAdef
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  -- the pointwise bound `(u' θ)² ≤ (π/2) A`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 ≤ (Real.pi / 2) * A := by
    have hAint : A = ∫ x in (0 : ℝ)..(Real.pi / 2), (deriv (deriv u) x) ^ 2 := by
      rw [hAdef, Work.Spaces.Iθ, intervalIntegral.integral_of_le hpi2pos.le,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hv2int : IntervalIntegrable (fun x => (deriv (deriv u) x) ^ 2) volume 0 (Real.pi / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hpi2pos.le]
      exact (hcont2.mono hsub).pow 2
    obtain ⟨θ₀, hθ₀, hdθ₀⟩ : ∃ θ₀ ∈ Set.Ioo 0 (Real.pi / 2), deriv u θ₀ = 0 := by
      have hcont : ContinuousOn u Work.Spaces.Iθ := hu.continuousOn.mono hsub
      have h := exists_deriv_eq_zero hpi2pos hcont (by rw [hu0, hu1])
      simpa [Work.Spaces.Iθ] using h
    intro θ hθ
    have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
    have hθ₀I : θ₀ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ₀.1, le_of_lt hθ₀.2⟩
    have huIcc_sub : Set.uIcc θ₀ θ ⊆ Work.Spaces.Iθ := by
      intro x hx
      rcases le_total θ₀ θ with h | h
      · rw [Set.uIcc_of_le h] at hx
        exact ⟨le_trans hθ₀I.1 hx.1, le_trans hx.2 hθI.2⟩
      · rw [Set.uIcc_of_ge h] at hx
        exact ⟨le_trans hθI.1 hx.1, le_trans hx.2 hθ₀I.2⟩
    have hcontv : ContinuousOn (deriv (deriv u)) (Set.uIcc θ₀ θ) :=
      hcont2.mono (huIcc_sub.trans hsub)
    have hint : IntervalIntegrable (deriv (deriv u)) volume θ₀ θ := hcontv.intervalIntegrable
    have hderiv_at : ∀ x ∈ Set.uIcc θ₀ θ, DifferentiableAt ℝ (deriv u) x := fun x hx =>
      hdiff1.differentiableAt (isOpen_Ioo.mem_nhds (hsub (huIcc_sub hx)))
    have hFTC : deriv u θ = ∫ t in θ₀..θ, deriv (deriv u) t := by
      have h := intervalIntegral.integral_deriv_eq_sub (a := θ₀) (b := θ) hderiv_at hint
      rw [h, hdθ₀, sub_zero]
    rw [hFTC]
    rcases le_total θ₀ θ with hle | hle
    · have hcontIcc : ContinuousOn (deriv (deriv u)) (Set.Icc θ₀ θ) := by
        simpa [Set.uIcc_of_le hle] using hcontv
      have hcs := sq_integral_le (fun t => deriv (deriv u) t) θ₀ θ hle hcontIcc
      have hmono : (∫ t in θ₀..θ, (deriv (deriv u) t) ^ 2) ≤ A := by
        rw [hAint]
        refine intervalIntegral.integral_mono_interval hθ₀I.1 hle hθI.2 ?_ hv2int
        exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      have hlen : θ - θ₀ ≤ Real.pi / 2 := by linarith [hθ₀.1, hθI.2]
      have hnn : 0 ≤ (∫ t in θ₀..θ, (deriv (deriv u) t) ^ 2) :=
        intervalIntegral.integral_nonneg_of_forall hle (fun t => sq_nonneg _)
      nlinarith [hcs, hmono, hlen, hnn, hpi2pos]
    · have hsym : (∫ t in θ₀..θ, deriv (deriv u) t) = - ∫ t in θ..θ₀, deriv (deriv u) t :=
        intervalIntegral.integral_symm θ θ₀
      rw [hsym, neg_sq]
      have hcontIcc : ContinuousOn (deriv (deriv u)) (Set.Icc θ θ₀) := by
        simpa [Set.uIcc_of_ge hle] using hcontv
      have hcs := sq_integral_le (fun t => deriv (deriv u) t) θ θ₀ hle hcontIcc
      have hmono : (∫ t in θ..θ₀, (deriv (deriv u) t) ^ 2) ≤ A := by
        rw [hAint]
        refine intervalIntegral.integral_mono_interval hθI.1 hle hθ₀I.2 ?_ hv2int
        exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      have hlen : θ₀ - θ ≤ Real.pi / 2 := by linarith [hθ₀.2, hθI.1]
      have hnn : 0 ≤ (∫ t in θ..θ₀, (deriv (deriv u) t) ^ 2) :=
        intervalIntegral.integral_nonneg_of_forall hle (fun t => sq_nonneg _)
      nlinarith [hcs, hmono, hlen, hnn, hpi2pos]
  -- integrability of the four integrands occurring below
  have hcontv2 : ContinuousOn (fun θ => (deriv (deriv u) θ) ^ 2) Work.Spaces.Iθ :=
    (hcont2.mono hsub).pow 2
  have hcontu2 : ContinuousOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ :=
    (hcontdu.mono hsub).pow 2
  have hv2_int : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2) Work.Spaces.Iθ :=
    hcontv2.integrableOn_compact isCompact_Icc
  have hconstw_int : IntegrableOn (fun θ => ((Real.pi / 2) * A) * w θ) Work.Spaces.Iθ := by
    have h := hw_int.mul_continuousOn (continuousOn_const (c := (Real.pi / 2) * A)) isCompact_Icc
    simpa [mul_comm] using h
  have hv2w_int_aux : IntegrableOn (fun θ => w θ * (deriv (deriv u) θ) ^ 2) Work.Spaces.Iθ :=
    hw_int.mul_continuousOn hcontv2 isCompact_Icc
  have hv2w_int : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * w θ) Work.Spaces.Iθ := by
    simpa [mul_comm] using hv2w_int_aux
  have hdu2w_int : IntegrableOn (fun θ => (deriv u θ) ^ 2 * w θ) Work.Spaces.Iθ := by
    have h := hw_int.mul_continuousOn hcontu2 isCompact_Icc
    simpa [mul_comm] using h
  -- step 1: integrate the pointwise bound against the weight
  have hLHS_le : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * w θ)
      ≤ ((Real.pi / 2) * A) * (∫ θ in Work.Spaces.Iθ, w θ) := by
    calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * w θ)
        ≤ (∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) * A) * w θ) := by
          refine MeasureTheory.setIntegral_mono_on hdu2w_int hconstw_int measurableSet_Icc ?_
          intro θ hθ
          exact mul_le_mul_of_nonneg_right (hpt θ hθ) (hw_nonneg_on θ hθ)
      _ = ((Real.pi / 2) * A) * (∫ θ in Work.Spaces.Iθ, w θ) := by
          rw [MeasureTheory.integral_const_mul]
  -- step 2: `w ≥ 1` on `(0, π/2)`, so the unweighted integral is at most the weighted one
  have hA_le : A ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * w θ := by
    have hI1 : A = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv u) θ) ^ 2 := by
      rw [hAdef]
      exact (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
    have hI2 : (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * w θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * w θ :=
      (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
    rw [hI1, hI2]
    refine MeasureTheory.setIntegral_mono_on (hv2_int.mono_set Set.Ioo_subset_Icc_self)
      (hv2w_int.mono_set Set.Ioo_subset_Icc_self) measurableSet_Ioo ?_
    intro θ hθ
    have h1 : (1 : ℝ) ≤ w θ := by
      have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have h2 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have h3 := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta)) hs h2 (by linarith [hη])
      simpa [Real.one_rpow] using h3
    calc (deriv (deriv u) θ) ^ 2 = (deriv (deriv u) θ) ^ 2 * 1 := by ring
      _ ≤ (deriv (deriv u) θ) ^ 2 * w θ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- step 3: arithmetic
  have harith : ((Real.pi / 2) * A) * 10000 ≤ 20000 * A := by
    have h1 : (Real.pi / 2) * 10000 ≤ 20000 := by nlinarith [Real.pi_le_four]
    calc ((Real.pi / 2) * A) * 10000 = ((Real.pi / 2) * 10000) * A := by ring
      _ ≤ 20000 * A := mul_le_mul_of_nonneg_right h1 hA_nonneg
  calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * w θ)
      ≤ ((Real.pi / 2) * A) * (∫ θ in Work.Spaces.Iθ, w θ) := hLHS_le
    _ ≤ ((Real.pi / 2) * A) * 10000 :=
        mul_le_mul_of_nonneg_left hW_le (mul_nonneg (by positivity) hA_nonneg)
    _ ≤ 20000 * A := harith
    _ ≤ 20000 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * w θ) :=
        mul_le_mul_of_nonneg_left hA_le (by norm_num)

end Work.FTS.EllipticEst.TanTheta
