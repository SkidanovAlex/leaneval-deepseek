import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Submodule

theorem realSpan_zero_iff_bot {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℤ E) :
    Module.finrank ℝ (Submodule.span ℝ (W : Set E)) = 0 ↔ W = ⊥ := by
  constructor
  · intro h
    have hspan : Submodule.span ℝ (W : Set E) = ⊥ := by
      exact (Submodule.finrank_eq_zero (R := ℝ) (M := E) (S := Submodule.span ℝ (W : Set E))).mp h
    exact (Submodule.eq_bot_iff W).mpr (by
      intro x hx
      have hxspan : x ∈ Submodule.span ℝ (W : Set E) := Submodule.subset_span hx
      rw [hspan] at hxspan
      simpa using hxspan)
  · intro hW
    have hspan : Submodule.span ℝ (W : Set E) = (⊥ : Submodule ℝ E) := by
      rw [hW, Submodule.bot_coe]
      exact (Submodule.span_singleton_eq_bot (R := ℝ) (M := E) (x := 0)).mpr rfl
    rw [hspan]
    simp

end Commons.LinearAlgebra.Submodule