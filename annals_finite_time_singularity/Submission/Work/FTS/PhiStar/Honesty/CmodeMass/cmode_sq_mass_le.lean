/-
Work module for the Elgindi finite-time singularity project.

# `L²`-mass bound for a mode coefficient with compact support and a sup bound

If `c` is (a.e. strongly) measurable on `Ioi 0`, vanishes past `b` and is bounded by `M`,
then `c ^ 2` is integrable on `Ioi 0` and its integral is at most `M ^ 2 * b` -- the trivial
measure-theoretic estimate behind every "the tail contributes nothing" step in the honesty
layer: `c ^ 2` is dominated by the constant `M ^ 2` on the finite-measure set `Ioc 0 b` and
vanishes on the rest of `Ioi 0`.

The route is: reduce `IntegrableOn (· ^ 2) (Ioi 0)` to `IntegrableOn (· ^ 2) (Ioc 0 b)`
(bounded measurable on a finite-measure set, `Integrable.mono'` against the constant), then
transport it back with the indicator identity `integrable_indicator_iff` (both indicators
coincide because `c` vanishes off `Ioc 0 b` inside `Ioi 0`); the value of the integral is
computed with `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`, the bound with
`setIntegral_mono_on` and `setIntegral_const` (`volume.real (Ioc 0 b) = b`).

The hypothesis `0 ≤ M` is not needed for this estimate (only `|c t| ≤ M` is used).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Series.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.CmodeMass

theorem cmode_sq_mass_le {c : ℝ → ℝ} {b M : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hmeas : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hsupp : ∀ t : ℝ, b < t → c t = 0) (hbd : ∀ t : ℝ, |c t| ≤ M) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi 0, c t ^ 2) ≤ M ^ 2 * b := by
  have hsub : Set.Ioc (0 : ℝ) b ⊆ Set.Ioi 0 := Set.Ioc_subset_Ioi_self
  -- `c ^ 2` vanishes on the part of `Ioi 0` which is not in `Ioc 0 b`
  have hvanish : ∀ x ∈ Set.Ioi (0 : ℝ) \ Set.Ioc 0 b, c x ^ 2 = 0 := by
    rintro x ⟨hx, hx'⟩
    have hxb : b < x := lt_of_not_ge fun h => hx' ⟨hx, h⟩
    simp [hsupp x hxb]
  -- the set carrying the whole mass has finite measure
  have hfin : MeasureTheory.volume (Set.Ioc (0 : ℝ) b) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  -- bounded measurable on a finite-measure set
  have hIntSmall : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioc 0 b)
      MeasureTheory.volume := by
    have hgm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
      (hmeas.mono_measure (Measure.restrict_mono hsub le_rfl)).pow 2
    have hg : MeasureTheory.Integrable (fun _ : ℝ => M ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
      MeasureTheory.integrableOn_const (C := M ^ 2) hfin
    refine hg.mono' hgm ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    change |c x ^ 2| ≤ M ^ 2
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2
  -- transport the integrability back to `Ioi 0` through the indicator
  have hIntBig : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0)
      MeasureTheory.volume := by
    have h1 : MeasureTheory.Integrable ((Set.Ioc 0 b).indicator (fun t : ℝ => c t ^ 2))
        MeasureTheory.volume :=
      hIntSmall.integrable_indicator measurableSet_Ioc
    have hid : (Set.Ioi (0 : ℝ)).indicator (fun t : ℝ => c t ^ 2)
        = (Set.Ioc 0 b).indicator (fun t : ℝ => c t ^ 2) := by
      funext x
      rcases em (x ∈ Set.Ioi (0 : ℝ)) with hx | hx
      · rcases em (x ∈ Set.Ioc 0 b) with hx' | hx'
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
        · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hx']
          exact hvanish x ⟨hx, hx'⟩
      · have hx'' : x ∉ Set.Ioc 0 b := fun h => hx (hsub h)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx'']
    rw [← hid] at h1
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).1 h1
  refine ⟨hIntBig, ?_⟩
  -- the integral over `Ioi 0` is the integral over `Ioc 0 b`
  have hIeq : (∫ x in Set.Ioi (0 : ℝ), c x ^ 2) = ∫ x in Set.Ioc 0 b, c x ^ 2 :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hvanish
  rw [hIeq]
  calc ∫ x in Set.Ioc 0 b, c x ^ 2
      ≤ ∫ x in Set.Ioc 0 b, M ^ 2 :=
        MeasureTheory.setIntegral_mono_on hIntSmall
          (MeasureTheory.integrableOn_const (C := M ^ 2) hfin) measurableSet_Ioc
          (fun x _ => by
            rw [show c x ^ 2 = |c x| ^ 2 from by rw [sq_abs]]
            exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2)
    _ = M ^ 2 * b := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hb, sub_zero,
          smul_eq_mul, mul_comm]

end Work.FTS.PhiStar.Honesty.CmodeMass
