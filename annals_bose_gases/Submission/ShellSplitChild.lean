import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.ShellMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Task: prove a one-dimensional domain-splitting identity

GOAL (`shell_max_split`): for `f : ℝ → ℝ`, `r > 0`,
`hrad : IntegrableOn (fun s => s ^ 2 * |f s|) (Set.Ioi 0) volume`, and
`hfae : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0))`:

    (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * f s) / max r s)
      = (1 / r) * (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * f s)
        + (∫ s in Set.Ioi r, s * f s)

This is the elementary rearrangement used in Newton's shell theorem: on
`{0 < s ≤ r}` we have `max r s = r`, hence `s²·f/max r s = (s²·f)/r`; on
`{s > r}` we have `max r s = s`, hence `s²·f/max = s·f`.

HOW TO PROVE (suggested):
1. `Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) r ∪ Set.Ioi r` (disjoint union, both
   measurable), so the integral over `Ioi 0` splits by
   `MeasureTheory.setIntegral_union (hst : Disjoint s t) (ht) (hfs) (hft)`:
   you need integrability of `fun s => (s² f s)/max r s` on each of the two
   pieces.  Prove each with `MeasureTheory.Integrable.mono'` using the
   pointwise bounds
   - on `{0 < s ≤ r}`: `|(s² f s)/max r s| = |(s² f s)/r| ≤ (s²|f s|)/r`
     (dominated by an integrable function derived from `hrad` restricted to
     the subset), and
   - on `{s > r}`: `|(s² f s)/max r s| = |s·f s| ≤ s·|f s| ≤ (s²|f s|)/r`
     (since `s ≥ r`).
2. Then rewrite the integrand on each piece with
   `MeasureTheory.setIntegral_congr_fun` and pull the scalar `1/r` out using
   `MeasureTheory.integral_const_mul` (applied with the measure
   `volume.restrict (Set.Ioc 0 r)`).

All standard measure facts are in mathlib.  Some names: `max_eq_left`,
`max_eq_right`, `div_le_div_iff₀`, `abs_div`, `Real.norm_eq_abs`,
`MeasureTheory.Integrable.mono'`, `IntegrableOn.mono`, `.const_mul`,
`MeasureTheory.Integrable.mono'`.

Do NOT change the statement.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

/-- Pointwise domination of the `max r s`-denominator integrand: since
`max r s ≥ r > 0` we have `|s²·f s / max r s| ≤ (1/r)·s²·|f s|` for every `s`. -/
lemma shell_g_bound {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (s : ℝ) :
    |(s ^ 2 * f s) / max r s| ≤ (1 / r) * (s ^ 2 * |f s|) := by
  have hmaxpos : 0 < max r s := lt_of_lt_of_le hr (le_max_left r s)
  have ha : 0 ≤ s ^ 2 * |f s| := mul_nonneg (sq_nonneg s) (abs_nonneg (f s))
  calc
    |(s ^ 2 * f s) / max r s| = (s ^ 2 * |f s|) / max r s := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s), abs_of_pos hmaxpos]
    _ ≤ (s ^ 2 * |f s|) / r := by
      rw [div_le_div_iff₀ hmaxpos hr]
      exact mul_le_mul_of_nonneg_left (le_max_left r s) ha
    _ = (1 / r) * (s ^ 2 * |f s|) := by ring

/-- Split `∫_{s>0} s²·f s / max r s` into inside (`s ≤ r`) and outside (`s > r`) pieces. -/
lemma shell_max_split {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hrad : IntegrableOn (fun s : ℝ => s ^ 2 * |f s|) (Set.Ioi (0 : ℝ)) volume)
    (hfae : AEStronglyMeasurable f (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * f s) / max r s) =
      (1 / r) * (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * f s) +
        (∫ s in Set.Ioi r, s * f s) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let g : ℝ → ℝ := fun s => (s ^ 2 * f s) / max r s
  have hcH : Integrable (fun s : ℝ => (1 / r) * (s ^ 2 * |f s|)) μ := by
    simpa [μ] using hrad.const_mul (1 / r)
  have hsm_g : AEStronglyMeasurable g μ := by
    have hs2m : AEStronglyMeasurable (fun s : ℝ => s ^ 2) μ :=
      (by fun_prop : Continuous (fun s : ℝ => s ^ 2)).aestronglyMeasurable
    have hsm1 : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * f s) μ := hs2m.mul hfae
    have hinv : Measurable (fun s : ℝ => (max r s)⁻¹) :=
      (by fun_prop : Measurable (fun s : ℝ => max r s)).inv
    have hsm2 : AEStronglyMeasurable (fun s : ℝ => (max r s)⁻¹) μ := hinv.aestronglyMeasurable
    convert hsm1.mul hsm2 using 1
    funext s
    simp [g, div_eq_mul_inv, mul_assoc]
  have hg_int : Integrable g μ := by
    refine Integrable.mono' hcH hsm_g ?_
    refine Eventually.of_forall ?_
    intro s
    simpa [Real.norm_eq_abs] using shell_g_bound (f := f) hr s
  have hgIoi0 : IntegrableOn g (Set.Ioi (0 : ℝ)) volume := by
    change Integrable g (volume.restrict (Set.Ioi (0 : ℝ)))
    simpa [μ] using hg_int
  have hgIoc : IntegrableOn g (Set.Ioc (0 : ℝ) r) volume :=
    hgIoi0.mono_set (by intro s hs; exact hs.1)
  have hgIoir : IntegrableOn g (Set.Ioi r) volume :=
    hgIoi0.mono_set (by intro s hs; exact lt_trans hr hs)
  have hset : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) r ∪ Set.Ioi r := by
    ext x
    constructor
    · intro hx
      by_cases hxr : x ≤ r
      · exact Or.inl ⟨hx, hxr⟩
      · exact Or.inr (lt_of_not_ge hxr)
    · intro hx
      rcases hx with ⟨hx0, _⟩ | hxr
      · exact hx0
      · exact lt_trans hr hxr
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) r) (Set.Ioi r) := by
    rw [Set.disjoint_left]
    intro s hsIoc hsIoi
    exact (not_lt_of_ge hsIoc.2) hsIoi
  have hsplit0 : (∫ s in Set.Ioi (0 : ℝ), g s) =
      (∫ s in Set.Ioc (0 : ℝ) r, g s) + (∫ s in Set.Ioi r, g s) := by
    rw [hset]
    exact setIntegral_union hdisj measurableSet_Ioi hgIoc hgIoir
  have hconvIoc : (∫ s in Set.Ioc (0 : ℝ) r, g s) =
      (∫ s in Set.Ioc (0 : ℝ) r, (s ^ 2 * f s) / r) := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro s hs
    have hmax : max r s = r := max_eq_left hs.2
    simp [g, hmax]
  have hconvIoir : (∫ s in Set.Ioi r, g s) = (∫ s in Set.Ioi r, s * f s) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    have hmax : max r s = s := max_eq_right (le_of_lt hs)
    have hsne : s ≠ 0 := ne_of_gt (lt_trans hr hs)
    dsimp [g]
    rw [hmax]
    field_simp [hsne]
  have hscalar : (∫ s in Set.Ioc (0 : ℝ) r, (s ^ 2 * f s) / r) =
      (1 / r) * (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * f s) := by
    have hcong : (∫ s in Set.Ioc (0 : ℝ) r, (s ^ 2 * f s) / r) =
        (∫ s in Set.Ioc (0 : ℝ) r, (1 / r) * (s ^ 2 * f s)) := by
      refine setIntegral_congr_fun measurableSet_Ioc ?_
      intro s hs
      ring
    rw [hcong]
    simpa using (integral_const_mul (1 / r) (fun s : ℝ => s ^ 2 * f s) :
      (∫ s : ℝ, (1 / r) * (s ^ 2 * f s) ∂ (volume.restrict (Set.Ioc (0 : ℝ) r)) =
        (1 / r) * (∫ s : ℝ, (s ^ 2 * f s) ∂ (volume.restrict (Set.Ioc (0 : ℝ) r)))))
  change (∫ s in Set.Ioi (0 : ℝ), g s) =
      (1 / r) * (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * f s) +
        (∫ s in Set.Ioi r, s * f s)
  calc
    (∫ s in Set.Ioi (0 : ℝ), g s)
        = (∫ s in Set.Ioc (0 : ℝ) r, g s) + (∫ s in Set.Ioi r, g s) := hsplit0
    _ = (∫ s in Set.Ioc (0 : ℝ) r, (s ^ 2 * f s) / r) + (∫ s in Set.Ioi r, s * f s) := by
      rw [hconvIoc, hconvIoir]
    _ = (1 / r) * (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * f s) + (∫ s in Set.Ioi r, s * f s) := by
      rw [hscalar]

end Submission.BoseGases
