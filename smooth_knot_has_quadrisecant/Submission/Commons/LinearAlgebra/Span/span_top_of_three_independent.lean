import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra.Span

lemma span_top_of_three_independent {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (hfin : Module.finrank ℝ E = 3) {x y z : E}
    (hxyz : LinearIndependent ℝ ![x, y, z]) :
    Submodule.span ℝ ({x, y, z} : Set E) = ⊤ := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E := by simp [hfin]
  have hspan : Submodule.span ℝ (Set.range ![x, y, z]) = ⊤ :=
    hxyz.span_eq_top_of_card_eq_finrank hcard
  have hset : Set.range ![x, y, z] = ({x, y, z} : Set E) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro ha
      simp at ha
      rcases ha with rfl | rfl | rfl
      · refine ⟨0, ?_⟩; simp
      · refine ⟨1, ?_⟩; simp
      · refine ⟨2, ?_⟩; simp
  rw [← hset, hspan]

end Commons.LinearAlgebra.Span