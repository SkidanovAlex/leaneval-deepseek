import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.ZDataBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level cut out by a cochain: existence of a field on whose Galois group it vanishes

Schmidt--Wingberg's induction on `dim_{𝔽_p} E` (§4, pp. 18--19) replaces the running data by the
*level* `K̃`, the Galois closure over `k` of the field cut out by the class `z⁰` obtained from the
induction hypothesis: for every place `P` at which `z⁰` is ramified, `P` splits completely in `K̃`,
so the second summand `z⁰⁰` receives no contribution there and the two ramification sets are
disjoint (this is the hypothesis `hconf` of `Work.SSGRoute.hasZData_of_component_data`).

The present file supplies the existence of such a level: for a cochain that is additive and locally
constant on `G_K`, there is an intermediate field `L` of `Ω/k` with `z = 0` on `L.fixingSubgroup`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {E : Type} [AddCommGroup E]

/-- **The level cut out by a cochain.**  A cochain `z` which is additive and locally constant on
`G_K = K.fixingSubgroup` vanishes on the Galois group `G_L` of some intermediate field `L ⊆ Ω`,
namely any finite normal field whose fixing subgroup is contained in the open subgroup on which `z`
is trivial.  (In Schmidt--Wingberg's induction one takes for `L` the Galois closure of the field cut
out by `z⁰`; the field produced here is finite over `k`, so such a closure exists.) -/
theorem exists_fixingField_vanishing {K : IntermediateField k Ω} [FiniteDimensional k K]
    [Normal k K] [DistribMulAction (K ≃ₐ[k] K) E] {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ L : IntermediateField k Ω, ∀ g ∈ L.fixingSubgroup, z g = 0 := by
  obtain ⟨U, hUopen, _hUnorm, hUz⟩ := exists_normal_open_of_z_eq_zero (K := K) z hzadd hzloc
  have hGKopen : IsOpen ((K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen K
  obtain ⟨M, _hMfin, _hMnorm, hMle⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (U := k) (L := Ω)
      (U ⊓ K.fixingSubgroup) (hUopen.inter hGKopen)
  exact ⟨M, fun g hg => hUz g (hMle hg).1 (hMle hg).2⟩

end Work.SSGRoute
