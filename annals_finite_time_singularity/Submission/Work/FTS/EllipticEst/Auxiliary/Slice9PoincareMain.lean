import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.ang_integrals
import Submission.Work.FTS.EllipticEst.Auxiliary.pIBP_fts
import Submission.Work.FTS.EllipticEst.Auxiliary.Slice9PoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.P9

set_option autoImplicit false

/-- **The reduction of the constrained slice Poincaré inequality to the gap inequality.**

Let `f` be `C²` on `[0,π/2]`, vanishing at `0` and `π/2`, with `∫_{Iθ} f · sinθcos²θ = 0`.
Write `f = a·sin 2θ + g` with `a = coeffA f` and `g = residG f` orthogonal to `sin 2θ`; then

* `∫ f² = (π/4) a² + ∫ g²` and `∫ (f')² = π a² + ∫ (g')²`;
* the constraint gives `∫ g · sinθcos²θ = -(4/15) a`, and Cauchy–Schwarz against
  `∫ sin²θcos⁴θ = π/32` gives `a² ≤ (225π/512) ∫ g²`;
* the gap inequality `16 ∫ g² ≤ ∫ (g')²` (hypothesis `hgap`) closes, because
  `(5π/4)·(225π/512) < 7 < 16 - 9`.

Consequently `9 ∫ f² ≤ ∫ (f')²`. -/
theorem slicePoincare9_of_gap
    (hgap : ∀ h : ℝ → ℝ, ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)) → h 0 = 0 → h (π / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, h θ * Real.sin (2 * θ)) = 0 →
      16 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0) (h1 : f (π / 2) = 0)
    (horth : (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0) :
    9 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Real.isFiniteMeasure_restrict_Icc 0 (π / 2)
  set a : ℝ := coeffA f with hadef
  set g : ℝ → ℝ := residG f with hgdef
  have hgfun : g = fun θ : ℝ => f θ - a * s2 θ := by rw [hgdef, hadef]; rfl
  -- ## basic facts about `g`
  have hfCO : ContinuousOn f (Set.Icc 0 (π / 2)) := hf.continuousOn
  have hgCO : ContinuousOn g (Set.Icc 0 (π / 2)) := by
    rw [hgfun]
    exact hfCO.sub (continuous_s2.continuousOn.const_mul a)
  have hgC2 : ContDiffOn ℝ 2 g (Set.Icc 0 (π / 2)) := by
    have hlin : ContDiffOn ℝ 2 (fun θ : ℝ => a * s2 θ) (Set.Icc 0 (π / 2)) :=
      (contDiff_const.mul contDiff_s2).contDiffOn
    rw [hgfun]
    exact hf.sub hlin
  have hg0 : g 0 = 0 := by rw [hgfun]; simp [h0, s2]
  have hg1 : g (π / 2) = 0 := by
    rw [hgfun]
    show f (π / 2) - a * s2 (π / 2) = 0
    rw [h1]
    simp only [s2]
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    ring
  -- ## `∫ g · sin 2θ = 0`
  have hcoeff : (∫ θ in Work.Spaces.Iθ, f θ * s2 θ) = (π / 4) * a := by
    rw [hadef, coeffA]
    have hcancel : (π / 4 : ℝ) * (4 / π) = 1 := by field_simp
    rw [← mul_assoc, hcancel, one_mul]
  have hgs2 : (∫ θ in Work.Spaces.Iθ, g θ * s2 θ) = 0 := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, g θ * s2 θ)
        = ∫ θ in Work.Spaces.Iθ, (f θ * s2 θ - a * (s2 θ) ^ 2) :=
      setIntegral_Iθ_congr (fun θ _ => by rw [hgfun]; ring)
    rw [hcongr]
    have hi1 : IntegrableOn (fun θ : ℝ => f θ * s2 θ) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hfCO.mul continuous_s2.continuousOn)
    have hi2 : IntegrableOn (fun θ : ℝ => a * (s2 θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (continuousOn_const.mul (continuous_s2.continuousOn.pow 2))
    rw [MeasureTheory.integral_sub (f := fun θ : ℝ => f θ * s2 θ)
        (g := fun θ : ℝ => a * (s2 θ) ^ 2) hi1 hi2,
      MeasureTheory.integral_const_mul, hcoeff, integral_s2_sq]
    ring
  -- ## the decomposition of `∫ f²`
  have hF2 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      = (π / 4) * a ^ 2 + ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)) + (g θ) ^ 2 :=
      setIntegral_Iθ_congr (fun θ _ => by rw [hgfun]; ring)
    rw [hcongr]
    have hA : IntegrableOn (fun θ : ℝ => (a * s2 θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn ((continuous_s2.continuousOn.const_mul a).pow 2)
    have hB : IntegrableOn (fun θ : ℝ => 2 * a * (s2 θ * g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn
        (continuousOn_const.mul (continuous_s2.continuousOn.mul hgCO))
    have hC : IntegrableOn (fun θ : ℝ => (g θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hgCO.pow 2)
    have hAB : IntegrableOn
        (fun θ : ℝ => (a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn
        (((continuous_s2.continuousOn.const_mul a).pow 2).add
          (continuousOn_const.mul (continuous_s2.continuousOn.mul hgCO)))
    have h1' : (∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)) + (g θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)))
          + ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => (a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ))
        (g := fun θ : ℝ => (g θ) ^ 2) hAB hC
    have h2' : (∫ θ in Work.Spaces.Iθ, ((a * s2 θ) ^ 2 + 2 * a * (s2 θ * g θ)))
        = (∫ θ in Work.Spaces.Iθ, (a * s2 θ) ^ 2)
          + ∫ θ in Work.Spaces.Iθ, 2 * a * (s2 θ * g θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (a * s2 θ) ^ 2)
        (g := fun θ : ℝ => 2 * a * (s2 θ * g θ)) hA hB
    have h3' : (∫ θ in Work.Spaces.Iθ, (a * s2 θ) ^ 2) = a ^ 2 * (π / 4) := by
      rw [setIntegral_Iθ_congr (fun θ _ => by ring :
        ∀ θ ∈ Work.Spaces.Iθ, (a * s2 θ) ^ 2 = a ^ 2 * (s2 θ) ^ 2)]
      rw [MeasureTheory.integral_const_mul, integral_s2_sq]
    have h4' : (∫ θ in Work.Spaces.Iθ, 2 * a * (s2 θ * g θ)) = 0 := by
      rw [MeasureTheory.integral_const_mul]
      have hz : (∫ θ in Work.Spaces.Iθ, s2 θ * g θ) = 0 := by
        rw [show (∫ θ in Work.Spaces.Iθ, s2 θ * g θ)
            = ∫ θ in Work.Spaces.Iθ, g θ * s2 θ from
          setIntegral_Iθ_congr (fun θ _ => mul_comm _ _)]
        exact hgs2
      rw [hz]; ring
    rw [h1', h2', h3', h4']
    ring
  -- ## the decomposition of `∫ (f')²`
  have hwg : ∀ θ ∈ Set.Icc 0 (π / 2), w g θ = w f θ - a * w s2 θ := by
    intro θ hθ
    rw [hgfun]
    exact w_sub_const_mul hf a θ hθ
  have hwpt : ∀ θ ∈ Work.Spaces.Iθ,
      (w f θ) ^ 2 = (a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ) + (w g θ) ^ 2 := by
    intro θ hθ
    rw [hwg θ hθ]
    ring
  have hws2 : ContinuousOn (w s2) (Set.Icc 0 (π / 2)) :=
    continuousOn_w contDiff_s2.contDiffOn
  have hwg' : ContinuousOn (w g) (Set.Icc 0 (π / 2)) := continuousOn_w hgC2
  have hF1 : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
      = π * a ^ 2 + ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 := by
    rw [← integral_w_sq_eq_integral_deriv_sq f, ← integral_w_sq_eq_integral_deriv_sq g,
      setIntegral_Iθ_congr hwpt]
    have hA : IntegrableOn (fun θ : ℝ => (a * w s2 θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn ((hws2.const_mul a).pow 2)
    have hB : IntegrableOn (fun θ : ℝ => 2 * a * (w s2 θ * w g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (continuousOn_const.mul (hws2.mul hwg'))
    have hC : IntegrableOn (fun θ : ℝ => (w g θ) ^ 2) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hwg'.pow 2)
    have hAB : IntegrableOn
        (fun θ : ℝ => (a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (((hws2.const_mul a).pow 2).add
        (continuousOn_const.mul (hws2.mul hwg')))
    have h1' : (∫ θ in Work.Spaces.Iθ, ((a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ))
          + (w g θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, ((a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ)))
          + ∫ θ in Work.Spaces.Iθ, (w g θ) ^ 2 :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => (a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ))
        (g := fun θ : ℝ => (w g θ) ^ 2) hAB hC
    have h2' : (∫ θ in Work.Spaces.Iθ, ((a * w s2 θ) ^ 2 + 2 * a * (w s2 θ * w g θ)))
        = (∫ θ in Work.Spaces.Iθ, (a * w s2 θ) ^ 2)
          + ∫ θ in Work.Spaces.Iθ, 2 * a * (w s2 θ * w g θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => (a * w s2 θ) ^ 2)
        (g := fun θ : ℝ => 2 * a * (w s2 θ * w g θ)) hA hB
    have h3' : (∫ θ in Work.Spaces.Iθ, (a * w s2 θ) ^ 2) = a ^ 2 * π := by
      rw [setIntegral_Iθ_congr (fun θ _ => by ring :
        ∀ θ ∈ Work.Spaces.Iθ, (a * w s2 θ) ^ 2 = a ^ 2 * (w s2 θ) ^ 2)]
      rw [MeasureTheory.integral_const_mul, integral_w_sq_eq_integral_deriv_sq s2,
        integral_deriv_s2_sq]
    have h4' : (∫ θ in Work.Spaces.Iθ, 2 * a * (w s2 θ * w g θ)) = 0 := by
      rw [MeasureTheory.integral_const_mul]
      have hz : (∫ θ in Work.Spaces.Iθ, w s2 θ * w g θ) = 0 := by
        rw [integral_w_mul_eq s2 g]
        rw [show (∫ θ in Work.Spaces.Iθ, deriv s2 θ * deriv g θ)
            = ∫ θ in Work.Spaces.Iθ, deriv g θ * deriv s2 θ from
          setIntegral_Iθ_congr (fun θ _ => mul_comm _ _)]
        rw [show (∫ θ in Work.Spaces.Iθ, deriv g θ * deriv s2 θ)
            = 4 * (∫ θ in Work.Spaces.Iθ, g θ * s2 θ) from
          Work.FTS.EllipticEst.Auxiliary.pIBP_fts g hgC2 hg0 hg1]
        rw [hgs2]; ring
      rw [hz]; ring
    have h5' : (∫ θ in Work.Spaces.Iθ, (w g θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 := integral_w_sq_eq_integral_deriv_sq g
    rw [h1', h2', h3', h4', h5']
    ring
  -- ## the gap inequality on the residual
  have hgapg : 16 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 :=
    hgap g hgC2 hg0 hg1 (by simpa [s2] using hgs2)
  -- ## the constraint bounds the coefficient by the residual
  have hmom_g : (∫ θ in Work.Spaces.Iθ, g θ * Work.Elliptic.sinCos2 θ) = -(4 / 15) * a := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, g θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (f θ * Work.Elliptic.sinCos2 θ
            - a * (s2 θ * Work.Elliptic.sinCos2 θ)) :=
      setIntegral_Iθ_congr (fun θ _ => by rw [hgfun]; ring)
    rw [hcongr]
    have hi1 : IntegrableOn (fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn (hfCO.mul continuous_sinCos2.continuousOn)
    have hi2 : IntegrableOn
        (fun θ : ℝ => a * (s2 θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
      integrableOn_Iθ_of_continuousOn
        (continuousOn_const.mul (continuous_s2.continuousOn.mul continuous_sinCos2.continuousOn))
    rw [MeasureTheory.integral_sub (f := fun θ : ℝ => f θ * Work.Elliptic.sinCos2 θ)
        (g := fun θ : ℝ => a * (s2 θ * Work.Elliptic.sinCos2 θ)) hi1 hi2,
      MeasureTheory.integral_const_mul, horth]
    have hs2φ : (∫ θ in Work.Spaces.Iθ, s2 θ * Work.Elliptic.sinCos2 θ) = 4 / 15 := by
      rw [show (∫ θ in Work.Spaces.Iθ, s2 θ * Work.Elliptic.sinCos2 θ)
          = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * s2 θ from
        setIntegral_Iθ_congr (fun θ _ => mul_comm _ _)]
      exact integral_sinCos2_mul_s2
    rw [hs2φ]
    ring
  have hgm : MemLp g 2 (volume.restrict Work.Spaces.Iθ) := by
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hgCO
    exact MemLp.of_bound (hgCO.aestronglyMeasurable measurableSet_Icc) C
      (ae_restrict_of_forall_mem measurableSet_Icc hC)
  have hφm : MemLp Work.Elliptic.sinCos2 2 (volume.restrict Work.Spaces.Iθ) :=
    MemLp.of_bound (continuous_sinCos2.continuousOn.aestronglyMeasurable measurableSet_Icc) 1
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => by
        simpa [Real.norm_eq_abs] using abs_sinCos2_le_one θ))
  have hcs := Work.Spaces.cs_integral (u := g) (v := Work.Elliptic.sinCos2)
    (s := Work.Spaces.Iθ) hgm hφm
  have ha2 : a ^ 2 ≤ (225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by
    have h1' : (-(4 / 15) * a) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) * (π / 32) := by
      rw [← hmom_g]
      simpa [integral_sinCos2_sq] using hcs
    nlinarith [h1']
  -- ## arithmetic
  have hSnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 := integral_nonneg (fun θ => sq_nonneg _)
  have hpi : 1125 * π ^ 2 ≤ 14336 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [hF2, hF1]
  have h5π7 : (5 * π / 4) * a ^ 2 ≤ 7 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by
    have h1 : (5 * π / 4) * a ^ 2
        ≤ (5 * π / 4) * ((225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2)) :=
      mul_le_mul_of_nonneg_left ha2 (by linarith [Real.pi_pos])
    have h2 : (5 * π / 4) * ((225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2))
        ≤ 7 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by
      have h3 : (5 * π / 4) * ((225 * π / 512) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2))
          = (1125 * π ^ 2 / 2048) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) := by ring
      rw [h3]
      have h4 : (1125 * π ^ 2 / 2048 : ℝ) ≤ 7 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2048)]
        linarith [hpi]
      exact mul_le_mul_of_nonneg_right h4 hSnn
    linarith [h1, h2]
  nlinarith [h5π7, hgapg, hSnn]

end Work.FTS.EllipticEst.P9
