import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.L12Q

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Pointwise form of the Hardy-weight comparison.**  For `r > 0` and `θ ∈ (0,π/2)`
the single weighted `D_z`-term `i = 0` of `HkIntegrand` dominates `(f r θ)² · w r`:
`sin(2θ)^{η/2} ≤ 1 ≤ w r` makes the weight factor in the squared derivative at least `w r`. -/
private lemma slice_pointwise (α : ℝ) (f : ℝ → ℝ → ℝ) (r θ : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (f r θ) ^ 2 * ((1 + r) / r) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (le_of_lt Work.Spaces.eta_pos)
  have hsinpow : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [Real.rpow_neg (le_of_lt hs0), one_le_inv₀ (Real.rpow_pos_of_pos hs0 _)]
    exact hsle
  have hwr : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
  rw [← hwr]
  have hw1 : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hr]
  have hkey : Work.Spaces.w r
      ≤ (Work.Spaces.w r) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h2 : Work.Spaces.w r ≤ (Work.Spaces.w r) ^ 2 := by nlinarith
    have h3 : (Work.Spaces.w r) ^ 2
        ≤ (Work.Spaces.w r) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      simpa using mul_le_mul_of_nonneg_left hsinpow (sq_nonneg (Work.Spaces.w r))
    linarith
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α 4 f r θ 0 (by norm_num))
  simp only [Work.Spaces.DzIter_zero]
  rw [Work.Spaces.sq_mul_div_rpow (f r θ) (Work.Spaces.w r) (Real.sin (2 * θ))
        Work.Spaces.eta (le_of_lt hs0) (ne_of_gt Work.Spaces.eta_pos)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg (f r θ))]

/-- **The Hardy-weight comparison of a single radial slice, with no smoothness hypothesis.**
For `f ∈ ℋ⁴` (i.e. `HkMem α 4 f`) and `r > 0`:
`(∫_θ f(r,θ)²) · ((1+r)/r)² ≤ ∫_θ HkIntegrand α 4 f r θ`.

This is the first step of `|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}` (Elgindi, Proposition `muestimate`,
tex 1516), in the interior class where `Work.Spaces.SmoothNbhd` is unavailable.

Read `Submission/Work/Spaces/Defs.lean` and `Submission/Work/Spaces/HkSq_terms.lean` first.
Declare the result in `namespace Work.FTS.H2.L12Q` inside the module
`Submission/Work/FTS/H2/L12Q/phiWeight_slice_le.lean`, so that its full name is
`Work.FTS.H2.L12Q.phiWeight_slice_le`.

ROUTE (no smoothness needed).  For `θ ∈ Ioo 0 (π/2)` one has `0 < sin(2θ) ≤ 1`, so
`sin(2θ)^η ≤ 1`, and `w r = ((1+r)/r)^2 ≥ 1` for `r > 0`; hence
`(f r θ)^2 * w r ≤ (f r θ * (w r / sin(2θ)^(η/2)))^2 ≤ Work.Spaces.HkIntegrand α 4 f r θ`,
the last step being `Work.Spaces.sq_le_HkIntegrand_z α 4 f r θ 0 (by norm_num)` and the middle
identity `(w/s^(η/2))^2 = w^2/s^η` (`Real.rpow_mul`, `η = (η/2)*2`).  Rewrite
`(∫_θ f²) * w r = ∫_θ f² * w r` (`MeasureTheory.integral_mul_const`) and apply
`MeasureTheory.integral_mono_of_nonneg` with the (integrable) majorant
`θ ↦ HkIntegrand α 4 f r θ` obtained from `hmem.1 r (le_of_lt hr)`; only the a.e. bound is
needed, the two endpoints being null (`MeasureTheory.Ioo_ae_eq_Icc`). -/
theorem phiWeight_slice_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ r : ℝ, 0 < r →
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
  intro r hr
  -- The pointwise bound only holds off the two endpoints, which are null sets.
  have hae : (fun θ => (f r θ) ^ 2 * ((1 + r) / r) ^ 2)
      ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => Work.Spaces.HkIntegrand α 4 f r θ) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => slice_pointwise α f r θ hr hθ)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iθ)
    (f := fun θ => (f r θ) ^ 2 * ((1 + r) / r) ^ 2)
    (g := fun θ => Work.Spaces.HkIntegrand α 4 f r θ)
    (Eventually.of_forall (fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (hmem.1 r (le_of_lt hr)) hae
  rwa [MeasureTheory.integral_mul_const] at hmono

end Work.FTS.H2.L12Q
