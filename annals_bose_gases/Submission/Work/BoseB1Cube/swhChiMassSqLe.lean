import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `χ`-mass is bounded by (the pointwise sup of `χ²`) times the box volume

The sliding small-box cutoff

    χ_{B(u)}(x) = χ(x/ℓ) · χ_M(x/(ℓd) − u)

is the product of the corpus bump at the big-box scale and the cosine-`M`-th-power bump at the
small-box scale.  Its support lies in the sliding box `B(u) = dlBox ℓ d u`
(`SlotWord.chiSmallB_support_mem_dlBox`: the ball support of the first factor gives
`|x_j| ≤ ℓ/2`, the cube support of the second gives `x − (ℓd)•u ∈ acube (ℓd)`).

Consequently, **any** pointwise bound `χ_{B(u)}(x)² ≤ Dd` upgrades to the integral bound

    chiMass M ℓ d u = ∫_x χ_{B(u)}(x)² dx ≤ Dd · |B(u)| = Dd · boxMass ℓ d u ,

because `χ_{B(u)}(x)² ≤ Dd · 1_{B(u)}(x)` pointwise (on `B(u)` by hypothesis, off `B(u)` since
there `χ_{B(u)} ≡ 0`, hence the left side vanishes and the right side is `≥ 0` because `Dd ≥ 0`),
and `1_{B(u)}` is the indicator of a measurable set of finite volume.

This is the sharpened (`Dd`-parametrised) version of
`Work.BoseFixB1S.chiMass_le_const_mul_boxMass`, which takes `Dd` to be the explicit sup
`(chiSupAbs · chiSmallDecay M)²`; here the pointwise bound is supplied by the caller — typically
the "thin-window" hypothesis of the cube chapter, where `Dd` is a small diluteness-dependent
constant.
-/

namespace Work.BoseB1Cube

open MeasureTheory

theorem swhChiMassSqLe {M : ℕ} (hM : 1 ≤ M) {ℓ d Dd : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hDd : 0 ≤ Dd) (u : EuclideanSpace ℝ (Fin 3))
    (hthin : ∀ x : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2 ≤ Dd) :
    Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ Dd * Work.SmallBoxSliding.boxMass ℓ d u := by
  -- the box indicator is nonnegative
  have hboxnn : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.SmallBoxSliding.boxInd ℓ d u x := by
    intro x
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx]
      norm_num
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx]
  -- pointwise domination by `Dd · 1_{B(u)}`
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
        ≤ Dd * Work.SmallBoxSliding.boxInd ℓ d u x := by
    intro x
    by_cases hx : Submission.BoseGases.chiSmallB M ℓ d u x = 0
    · rw [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg hDd (hboxnn x)
    · have hmem : x ∈ Submission.BoseGases.dlBox ℓ d u :=
        Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hx
      have hbi : Work.SmallBoxSliding.boxInd ℓ d u x = 1 := by
        rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hmem]
      rw [hbi, mul_one]
      exact hthin x
  -- the indicator of the (measurable, finite-volume) box is integrable
  have hboxint : Integrable (Work.SmallBoxSliding.boxInd ℓ d u) := by
    show Integrable ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)))
    rw [MeasureTheory.integrable_indicator_iff
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
    refine MeasureTheory.integrableOn_const (C := (1 : ℝ)) ?_ ?_
    · exact (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u).ne
    · simp
  have hintg : Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Dd * Work.SmallBoxSliding.boxInd ℓ d u x) := hboxint.const_mul Dd
  rw [Work.SmallBoxSliding.chiMass_def]
  calc (∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Dd * Work.SmallBoxSliding.boxInd ℓ d u x :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hintg
          (Filter.Eventually.of_forall hpt)
    _ = Dd * Work.SmallBoxSliding.boxMass ℓ d u := by
        rw [Work.SmallBoxSliding.boxMass, MeasureTheory.integral_const_mul]

end Work.BoseB1Cube
