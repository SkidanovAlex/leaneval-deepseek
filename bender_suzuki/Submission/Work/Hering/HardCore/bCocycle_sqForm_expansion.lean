import Mathlib
import Submission.Work.Higman.Family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

theorem bCocycle_sqForm_expansion {F : Type*} [Field F] (θ : F ≃+* F) (ε r s : F)
    (u v : F × F) :
    Work.Higman.bCocycle F θ ε (r • u + s • v) (r • u + s • v) =
      (r * θ r) * Work.Higman.bCocycle F θ ε u u +
        (r * θ s) * Work.Higman.bCocycle F θ ε u v +
        (s * θ r) * Work.Higman.bCocycle F θ ε v u +
        (s * θ s) * Work.Higman.bCocycle F θ ε v v := by
  simp only [Work.Higman.bCocycle, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, smul_eq_mul, map_add, map_mul]
  ring

end Work.Hering.HardCore
