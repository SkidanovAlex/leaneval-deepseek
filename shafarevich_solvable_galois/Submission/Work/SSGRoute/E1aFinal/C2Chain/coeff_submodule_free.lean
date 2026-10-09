import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aFinal.C2Chain

/-- A `Coeff`-submodule of a finite free `ℤ`-module is a free `ℤ`-module.

No compatibility between the `Coeff`-module structure on `V` and the canonical `ℤ`-module
structure of the hypotheses `[Module.Finite ℤ V]`/`[Module.Free ℤ V]` is needed: a
`Coeff`-submodule `L` is, in particular, an additive subgroup of `V`, and every additive
subgroup of a finite free `ℤ`-module is again free over `ℤ` (`ℤ` is a principal ideal
domain, and submodules of free modules of finite rank over a PID are free).  The subtypes
`↥L` and `↥(L.toAddSubgroup.toIntSubmodule)` are the same type — same carrier set,
inherited additive structure and canonical `ℤ`-action — so a basis of the latter is a
basis of the former. -/
theorem coeff_submodule_free {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    [Module.Finite ℤ V] [Module.Free ℤ V] (L : Submodule SSGRoute.PTExt.Coeff V) :
    Module.Free ℤ ↥L := by
  -- View `L` as a `ℤ`-submodule through its underlying additive subgroup.
  let N : Submodule ℤ V := AddSubgroup.toIntSubmodule L.toAddSubgroup
  -- `V` is free of finite rank over the PID `ℤ`, hence `N` has a finite basis.
  obtain ⟨n, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Module.finBasis ℤ V) N
  -- `↥N` and `↥L` are the same `ℤ`-module, so `b` is a basis of `↥L`.
  exact Module.Free.of_basis b

end Work.SSGRoute.E1aFinal.C2Chain
