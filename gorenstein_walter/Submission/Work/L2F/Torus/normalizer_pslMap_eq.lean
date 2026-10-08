import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Torus.normalizer_map_eq_of_le_ker
import Submission.Work.L2F.Torus.center_le_genZ

open scoped MatrixGroups
open Matrix

-- The hypothesis `(2 : F) ≠ 0` is not used: the statement also holds in characteristic `2`, where
-- the centre of `SL(2,F)` is trivial and `-1 = 1`.  We keep it (the statement is fixed) and
-- silence the unused-variable linter for it.
set_option linter.unusedVariables false

namespace Work.L2F.Torus

/-- The normalizer in `PSL(2,F)` of the image of `⟨x, -1⟩` is the image of the normalizer of
`⟨x, -1⟩` in `SL(2,F)` (`ker π = {±1} ⊆ ⟨x, -1⟩`). -/
theorem normalizer_pslMap_eq (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) : Subgroup.normalizer ((genZ F x).map (Work.PSL2.pslMap F) : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = (Subgroup.normalizer (genZ F x : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map (Work.PSL2.pslMap F) := by
  -- `π = pslMap F` is the quotient map by the centre of `SL(2,F)`, whose kernel is `{±1}`.
  have hker : MonoidHom.ker (Work.PSL2.pslMap F) ≤ genZ F x := by
    rw [show MonoidHom.ker (Work.PSL2.pslMap F) =
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) from QuotientGroup.ker_mk' _]
    exact center_le_genZ F x
  exact normalizer_map_eq_of_le_ker (Work.PSL2.pslMap F)
    (QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
    (genZ F x) hker

end Work.L2F.Torus
