import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.PeriodicTiling

open Filter Bornology MeasureTheory
open scoped Pointwise

theorem bounded_measurable_pos_of_finite_lift
    {d : ℕ} {F : Set (Fin d → ℤ)} (hFfin : F.Finite) (hFne : F.Nonempty)
    {R : Set (Fin d → ℝ)} (hRb : IsBounded R) (hRm : MeasurableSet R) (hRp : 0 < volume R) :
    IsBounded ((fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F + R) ∧
      MeasurableSet ((fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F + R) ∧
      0 < volume ((fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F + R) := by
  let L : Set (Fin d → ℝ) := (fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F
  have hLfin : L.Finite := hFfin.image _
  have hLne : L.Nonempty := hFne.image _
  have h_union : L + R = ⋃ z ∈ L, z +ᵥ R := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_add] at hx
      rcases hx with ⟨z, hz, r, hr, hx⟩
      refine Set.mem_biUnion hz ?_
      rw [Set.mem_vadd_set]
      exact ⟨r, hr, hx⟩
    · intro hx
      rw [Set.mem_iUnion₂] at hx
      rcases hx with ⟨z, hz, hx⟩
      rw [Set.mem_vadd_set] at hx
      rcases hx with ⟨r, hr, hx⟩
      rw [Set.mem_add]
      exact ⟨z, hz, r, hr, hx⟩
  refine ⟨?_, ?_, ?_⟩
  · exact Bornology.IsBounded.add (Set.Finite.isBounded hLfin) hRb
  · rw [h_union]
    exact MeasurableSet.biUnion hLfin.countable
      (fun z _ => MeasurableSet.const_vadd hRm z)
  · rcases hLne with ⟨z, hz⟩
    have hsub : z +ᵥ R ⊆ L + R := by
      intro x hx
      rw [Set.mem_vadd_set] at hx
      rcases hx with ⟨r, hr, hx⟩
      rw [Set.mem_add]
      exact ⟨z, hz, r, hr, hx⟩
    have hvol_z : 0 < volume (z +ᵥ R) := by
      rw [MeasureTheory.measure_vadd volume z R]
      exact hRp
    exact lt_of_lt_of_le hvol_z (measure_mono hsub)

end Commons.PeriodicTiling