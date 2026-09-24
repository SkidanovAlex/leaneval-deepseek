import Mathlib

open MeasureTheory

-- `hD : 0 ≤ D` is part of the requested statement but is not needed for the argument (the
-- bound `‖φ u t‖ ≤ D` is what does the work), and the finiteness of
-- `volume.restrict (Set.uIoc 0 1)` has to be introduced as a local instance for
-- `MeasureTheory.Integrable.comp_snd`; neither warning indicates a problem.
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.GM.Affine

/-- Almost every point of the product measure `volume.restrict (uIoc a b) ⊗ volume.restrict S`
has its first coordinate in `uIoc a b` (the restriction of a measure to a measurable set
concentrates on that set, and it does so also after taking a product). -/
lemma pair_swap_ae_fst_mem_uIoc {S : Set ℝ} (hS : MeasurableSet S) (a b : ℝ) :
    ∀ᵐ p ∂((volume.restrict (Set.uIoc a b)).prod (volume.restrict S)), p.1 ∈ Set.uIoc a b := by
  rw [Measure.prod_restrict]
  exact (ae_restrict_mem (measurableSet_uIoc.prod hS)).mono (fun p hp => hp.1)

/-- Integrability of `(u, t) ↦ φ u t * w t` for the product of `volume.restrict (uIoc 0 1)` and
`volume.restrict S`: joint continuity gives a.e. strong measurability, `‖φ u t‖ ≤ D` for
`u ∈ [0,1]` bounds the modulus by the integrable (on a finite measure space) function
`(u, t) ↦ D * ‖w t‖`.  This is exactly the `Integrable` hypothesis of
`MeasureTheory.intervalIntegral_integral_swap` needed in `Work.GM.Affine.pair_swap`. -/
lemma pair_swap_integrable_uncurry {S : Set ℝ} (hS : MeasurableSet S) {φ : ℝ → ℝ → ℝ}
    {w : ℝ → ℝ} {D : ℝ}
    (hcont : Continuous (Function.uncurry (fun u t : ℝ => φ u t * w t)))
    (hwint : IntegrableOn w S volume)
    (hbdd : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t, ‖φ u t‖ ≤ D) :
    Integrable (Function.uncurry (fun u t : ℝ => φ u t * w t))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict S)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    rw [isFiniteMeasure_restrict]
    simp [Real.volume_Ioc]
  have hg : Integrable (fun p : ℝ × ℝ => D * ‖w p.2‖)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict S)) :=
    (hwint.norm.const_mul D).comp_snd _
  refine hg.mono' hcont.aestronglyMeasurable ?_
  filter_upwards [pair_swap_ae_fst_mem_uIoc hS 0 1] with p hp
  have hpI : p.1 ∈ Set.Icc (0:ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hp
    exact ⟨le_of_lt hp.1, hp.2⟩
  show ‖φ p.1 p.2 * w p.2‖ ≤ D * ‖w p.2‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbdd p.1 hpI p.2) (norm_nonneg _)

/-- Fubini swap for the assembly `Work.GM.Affine.winmass_reduction`: exchanging the `u`-integral
over the unit interval with the `t`-integral over an arbitrary measurable set `S`.  The integrand is
`φ u t * w t`, with `φ` jointly continuous and bounded by `D` on `[0,1] × ℝ`, and `w` integrable on
`S`.  Under these hypotheses every integral occurring is finite, so the degenerate behaviour of the
Bochner integral (an integral of a non-integrable function is `0`) does not arise and the two
iterated integrals are genuinely equal. -/
theorem pair_swap {S : Set ℝ} (hS : MeasurableSet S) {φ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {D : ℝ}
    (hD : 0 ≤ D)
    (hcont : Continuous (fun p : ℝ × ℝ => φ p.1 p.2 * w p.2))
    (hwint : MeasureTheory.IntegrableOn w S volume)
    (hbdd : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t, ‖φ u t‖ ≤ D) :
    (∫ t in S, (∫ u in (0 : ℝ)..1, φ u t) * w t)
      = ∫ u in (0 : ℝ)..1, ∫ t in S, φ u t * w t := by
  have h_int : Integrable (Function.uncurry (fun u t : ℝ => φ u t * w t))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict S)) :=
    pair_swap_integrable_uncurry hS hcont hwint hbdd
  -- Fubini over the product of the two restricted measures.
  rw [MeasureTheory.intervalIntegral_integral_swap (μ := volume.restrict S) (a := 0) (b := 1) h_int]
  -- The constant `w t` may be pulled out of the inner `u`-integral.
  refine setIntegral_congr_fun hS (fun t _ => ?_)
  exact (intervalIntegral.integral_mul_const (w t) (fun u => φ u t)).symm

end Work.GM.Affine
