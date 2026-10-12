import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.Gen

open MeasureTheory

/-- The clamp `w ↦ max (-B) (min w B)` fixes every `w` in `[-C, C]` when `B = max C 0`. -/
private lemma clip_eq_self_of_abs_le {C w : ℝ} (hw : |w| ≤ C) :
    max (-(max C 0)) (min w (max C 0)) = w := by
  have hBC : C ≤ max C 0 := le_max_left _ _
  have hwC : w ≤ C := (abs_le.mp hw).2
  have hCw : -C ≤ w := (abs_le.mp hw).1
  rw [min_eq_left (le_trans hwC hBC), max_eq_right (le_trans (neg_le_neg hBC) hCw)]

/-- The clamp `w ↦ max (-B) (min w B)` takes values in `[-B, B]` for `B ≥ 0`. -/
private lemma abs_clip_le {B w : ℝ} (hB : 0 ≤ B) :
    |max (-B) (min w B)| ≤ B := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (neg_le_self hB) (min_le_right _ _)⟩

theorem exists_measurable_clip_ae_eq {ℓ : ℝ} {fib : EuclideanSpace ℝ (Fin 3) → ℝ} {C : ℝ}
    (hfibm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C) :
    ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ, Measurable g
      ∧ (∀ z, |g z| ≤ max C 0)
      ∧ fib =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)] g := by
  have hA : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  refine ⟨fun z => max (-(max C 0)) (min (hfibm.mk fib z) (max C 0)), ?_, ?_, ?_⟩
  · have hmk : Measurable (hfibm.mk fib) := hfibm.measurable_mk
    fun_prop
  · intro z
    exact abs_clip_le (le_max_right C 0)
  · filter_upwards [ae_restrict_mem hA, hfibm.ae_eq_mk] with z hz heq
    calc fib z = max (-(max C 0)) (min (fib z) (max C 0)) :=
          (clip_eq_self_of_abs_le (hfibb z hz)).symm
      _ = max (-(max C 0)) (min (hfibm.mk fib z) (max C 0)) := by rw [heq]

end Work.BoseFixB1S.Gen
