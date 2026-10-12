import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

/-- The set `{(z₁, z₂) | z₁ - z₂ ∈ N}` is null for the product measure whenever `N` is null.

Enlarge `N` to a *measurable* null set `N' ⊇ N`; the corresponding set is measurable
(`(z₁,z₂) ↦ z₁ - z₂` is continuous), and slicing along the second coordinate gives, for every `z₂`,
the translate `{z₁ | z₁ - z₂ ∈ N'} = (-z₂) + N'`, whose measure is `volume N' = 0` by translation
invariance. Tonelli/Fubini (`Measure.prod_apply_symm`) then yields a zero lintegral. -/
theorem null_prod_preimage_sub {N : Set (EuclideanSpace ℝ (Fin 3))}
    (hN : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) N = 0) :
    (MeasureTheory.volume.prod MeasureTheory.volume)
      {z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | z.1 - z.2 ∈ N} = 0 := by
  obtain ⟨N', hN'N, hN'm, hN'0⟩ := MeasureTheory.exists_measurable_superset_of_null hN
  have hS : MeasurableSet
      {z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | z.1 - z.2 ∈ N'} := by
    measurability
  have hmain : (MeasureTheory.volume.prod MeasureTheory.volume)
      {z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | z.1 - z.2 ∈ N'} = 0 := by
    rw [MeasureTheory.Measure.prod_apply_symm (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume) hS]
    have hz : ∀ y : EuclideanSpace ℝ (Fin 3),
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          {a : EuclideanSpace ℝ (Fin 3) | a - y ∈ N'} = 0 := by
      intro y
      have hset : {a : EuclideanSpace ℝ (Fin 3) | a - y ∈ N'}
          = (fun x : EuclideanSpace ℝ (Fin 3) => (-y) + x) ⁻¹' N' := by
        ext x; simp [sub_eq_add_neg, add_comm]
      rw [hset, MeasureTheory.measure_preimage_add]
      exact hN'0
    simp [hz]
  exact MeasureTheory.measure_mono_null (fun z hz => hN'N hz) hmain

end Work.BoseFixB3.CS.Pieces
