import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The volume of a slice of a negation-symmetric set is even in the slice coordinate.

For `D ⊆ ℝ^{n+1}` with `D = -D` and a fixed coordinate `k`, the `L¹`-volume of the slice
`{x | insertNth k s x ∈ D}` does not depend on the sign of `s`: the coordinatewise negation
`x ↦ -x` on `ℝⁿ` is a measure-preserving bijection carrying the slice at `-s` onto the slice
at `s`. -/
theorem sliceVolume_neg {n : ℕ} {D : Set (Fin (n + 1) → ℝ)} (hsym : D = -D) (k : Fin (n + 1))
    (s : ℝ) :
    MeasureTheory.volume {x : Fin n → ℝ | Fin.insertNth k (-s) x ∈ D}
      = MeasureTheory.volume {x : Fin n → ℝ | Fin.insertNth k s x ∈ D} := by
  -- `D` is negation invariant.
  have hmem : ∀ y : Fin (n + 1) → ℝ, (y ∈ D) ↔ (-y ∈ D) := fun y =>
    ⟨fun h => Set.mem_neg.mp (hsym ▸ h), fun h => hsym.symm ▸ Set.mem_neg.mpr h⟩
  -- Inserting `s` into the negated tuple equals negating the tuple with `-s` inserted.
  have hneg : ∀ x : Fin n → ℝ,
      Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) k s (-x)
        = -Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) k (-s) x := by
    intro x
    have h := Fin.insertNth_sub (α := fun _ : Fin (n + 1) => ℝ) k (0 : ℝ) (-s)
      (0 : Fin n → ℝ) x
    simpa using h
  -- The slice at `-s` is the preimage of the slice at `s` under `x ↦ -x`.
  have hpre : (fun x : Fin n → ℝ => -x) ⁻¹'
        {x : Fin n → ℝ | Fin.insertNth k s x ∈ D}
      = {x : Fin n → ℝ | Fin.insertNth k (-s) x ∈ D} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hneg x]
    exact (hmem (Fin.insertNth k (-s) x)).symm
  -- `x ↦ -x` preserves `volume`.
  have hmp : ∀ S : Set (Fin n → ℝ),
      MeasureTheory.volume ((fun x : Fin n → ℝ => -x) ⁻¹' S) = MeasureTheory.volume S := by
    intro S
    have h1 := MeasureTheory.Measure.le_map_apply (μ := MeasureTheory.volume)
      (f := fun x : Fin n → ℝ => -x) measurable_neg.aemeasurable S
    rw [MeasureTheory.Measure.map_neg_eq_self MeasureTheory.volume] at h1
    have h2 := MeasureTheory.Measure.le_map_apply (μ := MeasureTheory.volume)
      (f := fun x : Fin n → ℝ => -x) measurable_neg.aemeasurable
      ((fun x : Fin n → ℝ => -x) ⁻¹' S)
    rw [MeasureTheory.Measure.map_neg_eq_self MeasureTheory.volume] at h2
    have hTT : (fun x : Fin n → ℝ => -x) ⁻¹' ((fun x : Fin n → ℝ => -x) ⁻¹' S) = S := by
      ext x; simp
    rw [hTT] at h2
    exact le_antisymm h1 h2
  rw [← hpre]
  exact hmp {x : Fin n → ℝ | Fin.insertNth k s x ∈ D}

end Work.BW
