import Mathlib

namespace Work.A3

theorem setIntegral_le_sum_of_subset {A B C D : Set ℝ} (hsub : A ⊆ B ∪ (C ∪ D))
    {g : ℝ → ℝ} (hgnn : ∀ x, 0 ≤ g x)
    (hIntB : MeasureTheory.IntegrableOn g B) (hIntC : MeasureTheory.IntegrableOn g C)
    (hIntD : MeasureTheory.IntegrableOn g D) :
    ∫ x in A, g x ≤ (∫ x in B, g x) + (∫ x in C, g x) + (∫ x in D, g x) := by
  -- Compare the measures `volume.restrict A` and `volume.restrict B + volume.restrict C +
  -- volume.restrict D`.  The latter dominates the former because `A ⊆ B ∪ (C ∪ D)`; the
  -- integrability hypotheses then give finiteness, so `integral_mono_measure` applies.
  have hle : MeasureTheory.volume.restrict A ≤
      MeasureTheory.volume.restrict B + MeasureTheory.volume.restrict C +
        MeasureTheory.volume.restrict D := by
    calc MeasureTheory.volume.restrict A ≤
          MeasureTheory.volume.restrict (B ∪ (C ∪ D)) :=
          MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsub
      _ ≤ MeasureTheory.volume.restrict B + MeasureTheory.volume.restrict (C ∪ D) :=
          MeasureTheory.Measure.restrict_union_le B (C ∪ D)
      _ ≤ MeasureTheory.volume.restrict B + MeasureTheory.volume.restrict C +
            MeasureTheory.volume.restrict D := by
          rw [add_assoc]
          exact add_le_add le_rfl (MeasureTheory.Measure.restrict_union_le C D)
  have hBC : MeasureTheory.Integrable g (MeasureTheory.volume.restrict B +
      MeasureTheory.volume.restrict C) :=
    MeasureTheory.Integrable.add_measure hIntB hIntC
  have hBCD : MeasureTheory.Integrable g
      ((MeasureTheory.volume.restrict B + MeasureTheory.volume.restrict C) +
        MeasureTheory.volume.restrict D) :=
    MeasureTheory.Integrable.add_measure hBC hIntD
  calc ∫ x in A, g x
      ≤ ∫ x, g x ∂(MeasureTheory.volume.restrict B + MeasureTheory.volume.restrict C +
          MeasureTheory.volume.restrict D) :=
        MeasureTheory.integral_mono_measure hle (Filter.Eventually.of_forall hgnn) hBCD
    _ = (∫ x in B, g x) + (∫ x in C, g x) + (∫ x in D, g x) := by
        rw [MeasureTheory.integral_add_measure hBC hIntD,
          MeasureTheory.integral_add_measure hIntB hIntC]

end Work.A3
