import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.LinearGroup

theorem specialLinearGroup_two_mem_center_iff {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔
      ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, -, hr⟩
    exact ⟨r, by rw [← hr, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.property
      rw [hc, Matrix.det_smul] at hdet
      simpa using hdet
    · rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Commons.GroupTheory.LinearGroup