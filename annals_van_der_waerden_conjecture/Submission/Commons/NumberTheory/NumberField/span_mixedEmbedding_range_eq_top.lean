import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

namespace Commons.NumberTheory.NumberField

open Module

/-- If `x` is a rational linear combination of the family `f`, then its mixed embedding is a real
linear combination of the mixed embeddings of `f`. -/
theorem mixedEmbedding_mem_span_of_mem_span (K : Type*) [Field K] [NumberField K]
    {N : ℕ} (f : Fin N → K) {x : K}
    (hx : x ∈ Submodule.span ℚ (Set.range f)) :
    NumberField.mixedEmbedding K x ∈
      Submodule.span ℝ (Set.range (fun i : Fin N => NumberField.mixedEmbedding K (f i))) := by
  refine Submodule.span_induction
    (p := fun x _ => NumberField.mixedEmbedding K x ∈
      Submodule.span ℝ (Set.range (fun i : Fin N => NumberField.mixedEmbedding K (f i))))
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    have h : NumberField.mixedEmbedding K (c • y) =
        (c : ℝ) • NumberField.mixedEmbedding K y := by
      rw [map_rat_smul]
      ext <;> simp [Rat.smul_def, smul_eq_mul]
    rw [h]
    exact Submodule.smul_mem _ _ hy

theorem span_mixedEmbedding_range_eq_top (K : Type*) [Field K] [NumberField K] (N : ℕ)
    (y : Fin N → NumberField.RingOfIntegers K)
    (hspan : Submodule.span ℚ (Set.range (fun i : Fin N => (((y i : NumberField.RingOfIntegers K) : K)))) = ⊤) :
    Submodule.span ℝ (Set.range (fun i : Fin N =>
      NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K)))) = ⊤ := by
  classical
  set f : Fin N → K := fun i => ((y i : NumberField.RingOfIntegers K) : K) with hf
  have hspanf : Submodule.span ℚ (Set.range f) = ⊤ := by
    rw [hf]; exact hspan
  suffices h : Submodule.span ℝ
      (Set.range (fun i : Fin N => NumberField.mixedEmbedding K (f i))) = ⊤ by
    simpa only [hf] using h
  rw [eq_top_iff]
  rw [← (NumberField.mixedEmbedding.latticeBasis K).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  rw [NumberField.mixedEmbedding.latticeBasis_apply]
  exact mixedEmbedding_mem_span_of_mem_span K f (by rw [hspanf]; exact Submodule.mem_top)

end Commons.NumberTheory.NumberField