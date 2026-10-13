import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.EllExist.Honesty.G1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

/-- `G1f α m c` is interval integrable on `1..z` for every `1 ≤ z`: it is continuous on the
open half line `(0,∞)`, and `[1,z] ⊆ (0,∞)`. -/
theorem G1f_intervalIntegrable_one {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0)) {z : ℝ} (hz : (1 : ℝ) ≤ z) :
    IntervalIntegrable (G1f α m c) volume 1 z :=
  ContinuousOn.intervalIntegrable_of_Icc hz
    ((G1f_continuousOn hc).mono fun _ ht => lt_of_lt_of_le zero_lt_one ht.1)

/-- On `Set.Ioi 1` the map `z ↦ ∫ t in 1..z, G1f α m c t` is a primitive of the continuous
function `G1f α m c`, hence differentiable there. -/
theorem G1f_hasDerivAt_primitive {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun u : ℝ => ∫ t in (1 : ℝ)..u, G1f α m c t) (G1f α m c z) z := by
  intro z hz
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hf : ContinuousOn (G1f α m c) (Set.Ioi 0) := G1f_continuousOn hc
  exact intervalIntegral.integral_hasDerivAt_right (G1f_intervalIntegrable_one m hc hz1)
    (hf.stronglyMeasurableAtFilter isOpen_Ioi z hz0)
    (hf.continuousAt (Ioi_mem_nhds hz0))

/-- If the integrand `G1f α m c` fails to be integrable on `(0,1]`, then `G1 α m c` vanishes on
`Set.Ioi 1`: for such `z` the integrand cannot be interval integrable on `0..z` either (otherwise
`IntegrableOn.mono_set` with `(0,1] ⊆ (0,z]` would give the forbidden integrability on `(0,1]`),
and the interval integral of a non-integrable function is `0`. -/
theorem G1_eq_zero_of_not_integrableOn {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (h : ¬ IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) 1)) {z : ℝ} (hz : (1 : ℝ) < z) :
    G1 α m c z = 0 := by
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have hnot : ¬ IntervalIntegrable (G1f α m c) volume 0 z := by
    intro hint
    have hInt : IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) z) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ z)).1 hint
    exact h (hInt.mono_set fun t ht => ⟨ht.1, le_trans ht.2 hz1⟩)
  rw [G1_eq_zpow_mul_G1A]
  have hzero : G1A α m c z = 0 := intervalIntegral.integral_undef hnot
  rw [hzero, mul_zero]

-- Measurability on the far field of the `z^{s⁻}` Green term `G1 α m c`
-- (`s⁻ = -(2m+5)/α`):
-- `G1 α m c z = z ^ (-(2*(m:ℝ)+5)/α) * ∫ t in (0:ℝ)..z, c t * t ^ ((2*(m:ℝ)+5)/α - 1)`.
-- Route: `a := (2*(m:ℝ)+5)/α`, `f t := c t * t ^ (a - 1)`, case-split on
-- `Good := MeasureTheory.IntegrableOn f (Set.Icc 0 1)`.
-- * If `Good`, then for every `z ≥ 1` the integral splits as `∫_0^z f = ∫_0^1 f + ∫_1^z f`
--   (`intervalIntegral.integral_add_adjacent_intervals`), and `z ↦ ∫_1^z f` is a primitive of
--   the continuous (on `Set.Ioi 0`) function `f`; so `G1 α m c` agrees on `Set.Ioi 1` with a
--   continuous function and is `MeasureTheory.AEStronglyMeasurable`
--   (`MeasureTheory.AEStronglyMeasurable.congr` + `ContinuousOn.aestronglyMeasurable`).
-- * If `¬ Good`, `MeasureTheory.IntegrableOn.mono_set` shows `f` is not interval integrable on
--   `0..z` for any `z ≥ 1`, so `intervalIntegral.integral_undef` gives `G1 α m c z = 0` for
--   all `z ∈ Set.Ioi 1`, and `MeasureTheory.AEStronglyMeasurable.congr` with the (a.e. equal)
--   zero function finishes.  (Recall that `∫` of a non-integrable function is `0`.)
theorem G1_far_measurable (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0)) :
    MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllExist.Honesty.G1 α m c z)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
  by_cases hGood : IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) 1)
  · -- Case 1: `G1f` is integrable on `(0,1]`.
    -- On `Set.Ioi 1`, `G1 α m c` agrees with the continuous function
    -- `z ↦ z^{s⁻}·(∫_0^1 G1f + ∫_1^z G1f)`.
    have hpow : ContinuousOn (fun z : ℝ => z ^ (G1s α m)) (Set.Ioi (1 : ℝ)) :=
      continuousOn_id.rpow_const fun x hx => Or.inl (by
        simp only [id_eq, mem_Ioi] at hx ⊢
        exact ne_of_gt (by linarith))
    have hprim : ContinuousOn (fun z : ℝ => ∫ t in (1 : ℝ)..z, G1f α m c t)
        (Set.Ioi (1 : ℝ)) :=
      fun z hz => (G1f_hasDerivAt_primitive m hc z hz).continuousAt.continuousWithinAt
    have hcont : ContinuousOn
        (fun z : ℝ => z ^ (G1s α m) *
          ((∫ t in (0 : ℝ)..1, G1f α m c t) + ∫ t in (1 : ℝ)..z, G1f α m c t))
        (Set.Ioi (1 : ℝ)) :=
      hpow.mul (ContinuousOn.add continuousOn_const hprim)
    refine (hcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
    have h01 : IntervalIntegrable (G1f α m c) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hGood
    have h1z : IntervalIntegrable (G1f α m c) volume 1 z :=
      G1f_intervalIntegrable_one m hc hz1
    have hsplit : G1A α m c z =
        (∫ t in (0 : ℝ)..1, G1f α m c t) + ∫ t in (1 : ℝ)..z, G1f α m c t := by
      show (∫ t in (0 : ℝ)..z, G1f α m c t) = _
      exact (intervalIntegral.integral_add_adjacent_intervals h01 h1z).symm
    rw [G1_eq_zpow_mul_G1A, hsplit]
  · -- Case 2: `G1f` is not integrable on `(0,1]`; then `G1 α m c` vanishes on `Set.Ioi 1`.
    have hconst : MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        (MeasureTheory.volume.restrict (Set.Ioi 1)) := MeasureTheory.aestronglyMeasurable_const
    refine hconst.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact (G1_eq_zero_of_not_integrableOn m hGood hz).symm

end Work.FTS.EllExist.Honesty
