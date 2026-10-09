import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aFinal.C2Chain

/-- A `Coeff`-submodule of a finite `ℤ`-module (where `Coeff = ULift ℤ`) is a finite `ℤ`-module.

Note that no compatibility between the `Coeff`-module and the canonical `ℤ`-module structure on
`V` is required: a `Coeff`-submodule is, in particular, an additive subgroup of `V`, hence a
`ℤ`-submodule, and `ℤ` is Noetherian, so every submodule of the finitely generated `ℤ`-module
`V` is again finitely generated.  The subtypes `↥L` and `↥(L.toAddSubgroup.toIntSubmodule)` are
the same type (same carrier set, inherited operations and the canonical `ℤ`-action). -/
theorem coeff_submodule_finite {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    [Module.Finite ℤ V] (L : Submodule SSGRoute.PTExt.Coeff V) : Module.Finite ℤ ↥L := by
  -- `⊤ : Submodule ℤ V` is finitely generated, since `V` is finite over `ℤ`.
  have htop : (⊤ : Submodule ℤ V).FG := Module.Finite.fg_top
  -- View `L` as a `ℤ`-submodule via its underlying additive subgroup; `ℤ` is Noetherian, so
  -- any submodule of a finitely generated `ℤ`-module is finitely generated.
  have hN : (AddSubgroup.toIntSubmodule L.toAddSubgroup).FG :=
    Submodule.FG.of_le htop le_top
  -- `↥(AddSubgroup.toIntSubmodule L.toAddSubgroup)` is definitionally `↥L` with the same `ℤ`-action.
  exact Module.Finite.of_fg hN

end Work.SSGRoute.E1aFinal.C2Chain
