import Mathlib.GroupTheory.Nilpotent

namespace Commons.GroupTheory.Nilpotent

/-- A finite group in which every maximal (coatome) subgroup is normal is nilpotent.

This is one direction of the standard characterization of finite nilpotent groups
(`Group.isNilpotent_of_finite_tfae`): a finite group is nilpotent iff every maximal
subgroup is normal, iff the normalizer condition holds, iff every Sylow subgroup is
normal, iff it is the direct product of its Sylow subgroups. -/
theorem isNilpotent_of_forall_isCoatom_normal {G : Type*} [Group G] [Finite G]
    (h : ∀ M : Subgroup G, IsCoatom M → M.Normal) : Group.IsNilpotent G :=
  ((Group.isNilpotent_of_finite_tfae (G := G)).out 1 3).mpr h

end Commons.GroupTheory.Nilpotent