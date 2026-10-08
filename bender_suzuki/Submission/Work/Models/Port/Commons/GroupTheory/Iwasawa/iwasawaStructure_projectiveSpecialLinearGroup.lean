import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Iwasawa

theorem iwasawaStructure_projectiveSpecialLinearGroup {K : Type*} [Field K] :
    Nonempty (MulAction.IwasawaStructure (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (Projectivization K (Fin 2 → K))) := by
  exact ⟨PSL2.Iwasawa⟩

end Commons.GroupTheory.Iwasawa