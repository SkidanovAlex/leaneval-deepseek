import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.RadGreenModeEnergy
import Submission.Work.FTS.ClassC.HonestCut.radGreen_compact_source
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_integrableOn
import Submission.Work.FTS.PhiStar.Honesty.zDeriv_radGreen_sq_w_sq_integrableOn
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Honesty.radGreen_mul_deriv_atTop_zero_meas
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_mul_self_atTop_zero
import Submission.Work.FTS.ClassC.flux_radGreen_zero
import Submission.Work.FTS.ClassC.flux_radGreen_atTop
import Submission.Work.FTS.ClassC.HonestCut.radGreen_modeEnergy_of_compactSupport
import Submission.Work.FTS.ClassC.HonestCut.radGreen_near_pointwise_bound
import Submission.Work.FTS.ClassC.HonestCut.radGreen_far_pointwise_bound
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.PhiStar.Honesty.radGreen_source_facts_of_compactSupport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-!
# `Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_compactSource`

The sharp per-mode weighted `L²` bound for the mode-`m` radial Green function

  `a := radGreen α m c`,   `−α²z²a'' − α(5+α)z a' + λ_m a = c`,   `λ_m = lamR m = 2m(2m+5)`,

for a source `c` which is only *continuous* on `(0,∞)` and *compactly supported away from `0`*
(`c ≡ 0` off some `[a,b]` with `a > 0`):

  `(λ_m − 3α² − 3α(5+α)/2)² · ∫_0^∞ a² w²  ≤  ∫_0^∞ c² w²`,   `w(z) = (1+z)²/z²`.

The hypothesis set is the honest one: no smoothness of `c` beyond continuity, no explicit
boundedness, no positioned support interval.  Everything the abstract per-mode theorem
`Work.FTS.ClassC.radGreen_modeEnergy` asks for is *deduced*:

* the global bound `∃ M, ∀ t, |c t| ≤ M` and the two-sided rate conditions `hdec`, `hvy` come
  from compact support plus continuity (`radGreen_source_facts_of_compactSupport`, the sibling
  lemma of this directory);
* the three Green-formula integrability conditions and the `c²w²`-slot likewise;
* the two derivative slots of `a` come from `Series.radGreenI_differentiableAt`, which needs
  only continuity of `c` (not smoothness);
* the two weighted `L²` slots `(z a')²w²` and `a²w²` come from the near-`0`/far-`∞` pointwise
  bounds of `a` (`ClassC.HonestCut.radGreen_near_pointwise_bound` /
  `..._far_pointwise_bound`) through `ClassC.HonestCut.radGreen_w2_slots_of_pointwise_bounds`,
  and the pairing slot `c·a·w²` from AM–GM against those two squares.
-/

/-- **The sharp per-mode weighted `L²` bound for `radGreen` with a continuous, compactly
supported (away from `0`) source.** -/
theorem radGreen_modeEnergy_of_compactSource {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : ContinuousOn c (Set.Ioi 0))
    (hsupp : ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
            * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  -- ## the source-side facts: decay at `∞`, vanishing at `0`, the three kernel-integrability
  --    conditions and the weighted square of the source
  obtain ⟨hdec, hvy, hg0, hg0', hginf, hint4⟩ :=
    Work.FTS.PhiStar.Honesty.radGreen_source_facts_of_compactSupport (α := α) (m := m) hc hsupp
  -- ## the two derivative slots of the Green function, from continuity of `c` alone
  have hd := Work.FTS.PhiStar.Series.radGreenI_differentiableAt (α := α) (m := m) hα hc
    hg0 hg0' hginf
  have hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) z :=
    fun z hz => ((hd z hz).1).hasDerivAt
  have hderiv2 : ∀ z : ℝ, 0 < z →
      HasDerivAt (deriv (Work.FTS.PhiStar.Radial.radGreen α m c))
        (deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z) z :=
    fun z hz => ((hd z hz).2).hasDerivAt
  -- ## the two weighted `L²` slots of the solution, from the near-`0`/far-`∞` pointwise bounds
  obtain ⟨hint1, hint2⟩ := Work.FTS.ClassC.HonestCut.radGreen_w2_slots_of_pointwise_bounds
    (α := α) m hderiv hderiv2
    (Work.FTS.ClassC.HonestCut.radGreen_near_pointwise_bound (α := α) hα hα4 m hm hc hvy
      hg0 hg0' hginf)
    (Work.FTS.ClassC.HonestCut.radGreen_far_pointwise_bound (α := α) hα hα4 m hc hdec
      hg0 hg0' hginf)
  -- ## the pairing slot `c·a·w²`, by AM–GM against the two squares
  have ha : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) :=
    fun z hz => (hderiv z hz).continuousAt.continuousWithinAt
  have hint3 : MeasureTheory.IntegrableOn
      (fun z : ℝ => c z * Work.FTS.PhiStar.Radial.radGreen α m c z * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
    have hdom : MeasureTheory.Integrable
        (fun z : ℝ => ((c z) ^ 2 * (Work.Spaces.w z) ^ 2
          + (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) / 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      simpa only [Pi.add_apply] using (hint4.add hint2).div_const 2
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
        unfold Work.Spaces.w
        refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
          (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
        exact pow_ne_zero 2 (ne_of_gt hz)
      exact ((hc.mul ha).mul hw).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs]
      refine abs_le.mpr ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (c z * Work.Spaces.w z
            + Work.FTS.PhiStar.Radial.radGreen α m c z * Work.Spaces.w z)]
      · nlinarith [sq_nonneg (c z * Work.Spaces.w z
            - Work.FTS.PhiStar.Radial.radGreen α m c z * Work.Spaces.w z)]
  -- ## the sharp per-mode energy bound, with all eight side conditions in place
  exact Work.FTS.ClassC.radGreen_modeEnergy hα hα4 m hm hc hdec hvy hg0 hg0' hginf
    hderiv hderiv2 hint1 hint2 hint3 hint4

end Work.FTS.PhiStar.Honesty
