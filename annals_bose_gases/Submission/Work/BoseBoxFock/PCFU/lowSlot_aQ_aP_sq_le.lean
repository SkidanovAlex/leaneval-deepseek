import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.aQ_aP_sq_le
import Submission.Work.BoseBoxFock.PCFU.lowSlot_L2_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.lowSlot_aQ_aP_sq_le`

The slot-`j` low-momentum fibre of the pair operator `aQ ℓ j ∘ aP ℓ i` (`i ≠ j`) applied to the
box restriction of a continuous state is bounded in `L²(abox n ℓ)` by the box restriction itself:

    ∫_{abox n ℓ} (Q_L,j (Qⱼ Pᵢ (Φ·1_{abox})))² ≤ 4 ∫_{abox n ℓ} (Φ·1_{abox})² .

The constant `4` is the (generous) constant of the frozen statement; the proof below in fact gives
the sharp chain with constant `1`:

    ∫ (Q_L,j (Qⱼ Pᵢ Θ))² ≤ ∫ (Qⱼ Pᵢ Θ)² ≤ ∫ Θ² ,      Θ = boxRestrictR ℓ Φ ,

both factors being `L²`-contractions on the centred box:

* `PCFU.aQ_aP_sq_le` — the pair `Qⱼ Pᵢ` is an `L²`-contraction on `abox n ℓ` (it is `Pᵢ` followed
  by the fluctuation of the coordinate mean `Pⱼ`; only `MemLp Θ 2` is needed);
* `PCFU.lowSlot_L2_le` — the low-momentum fibre `Q_L,j` is an `L²`-contraction on `abox n ℓ` for
  any state that is **measurable and bounded on the box** (the fibre is the compression of the
  multiplier `f(‖p‖/κ)`, which is bounded by `1`).

The state entering the second step is `Qⱼ Pᵢ Θ`, which is *not* assumed continuous: it is a slot
mean of a merely measurable state.  What is used instead is the weak slot algebra
`Work.BoseBoxFock.Weak` (`aP_measurable`, `aQ_measurable`, `aP_abs_le`, `aQ_abs_le`), valid for
measurable, globally bounded states.

The only analytic input about `Φ` is continuity, used twice:
`boxRestrictR_measurable_bounded'` below records that `Θ = Φ·1_{abox n ℓ}` is measurable and
globally bounded (the bound is `max C 0` with `C` a bound of `Φ` on the compact box), which yields
`MemLp Θ 2 (volume ↾ abox)` by `MemLp.of_bound` on the finite measure `volume ↾ abox`.

Everything in this file is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## 1. The box restriction of a continuous state is measurable and globally bounded -/

/-- **`boxRestrictR ℓ Φ` is measurable and globally bounded** for a continuous `Φ`: it is the
product of `Φ` with the indicator of the (measurable) box, and any bound of `|Φ|` on the compact
box bounds the restriction everywhere (the indicator is `0` outside). -/
private lemma boxRestrictR_measurable_bounded' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Measurable (Work.BoseBoxFock.boxRestrictR ℓ Φ)
      ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |Work.BoseBoxFock.boxRestrictR ℓ Φ x| ≤ C := by
  constructor
  · unfold Work.BoseBoxFock.boxRestrictR
    exact hΦ.measurable.mul
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ))
  · obtain ⟨C, hC⟩ :=
      (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hΦ.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    rw [Work.BoseBoxFock.boxRestrictR]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, mul_one]
      exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact le_max_right _ _

/-! ## 2. The target -/

theorem lowSlot_aQ_aP_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
            (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x) ^ 2)
      ≤ 4 * ∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2 := by
  obtain ⟨hΘm, C, hC0, hΘb⟩ := boxRestrictR_measurable_bounded' hℓ hΦ
  -- the box restriction is `L²` on the (finite) box
  haveI : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    Work.BoseBoxFock.Weak.abox_isFiniteMeasure n hℓ.le
  have hmem : MeasureTheory.MemLp (Work.BoseBoxFock.boxRestrictR ℓ Φ) 2
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    MeasureTheory.MemLp.of_bound hΘm.aestronglyMeasurable.restrict C (by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hΘb x)
  -- the pair `Qⱼ Pᵢ` is an `L²`-contraction on the box
  have h1 := aQ_aP_sq_le (ℓ := ℓ) hℓ (i := i) (j := j) hij hmem
  -- the low-momentum fibre is an `L²`-contraction on the box
  have hΨm : Measurable (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
      (Work.BoseBoxFock.boxRestrictR ℓ Φ))) :=
    Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)
  have hΨb : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ)) x| ≤ 2 * C := fun x _ =>
    Work.BoseBoxFock.Weak.aQ_abs_le hℓ j hC0
      (Work.BoseBoxFock.Weak.aP_abs_le hℓ i hC0 hΘb) x
  have h2 := lowSlot_L2_le j fc hκ hℓ (by linarith) hΨm hΨb
  -- the constant `4` is free: the box second moment is nonnegative
  have h3 : (0 : ℝ) ≤
      ∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  linarith

end Work.BoseBoxFock.PCFU
