import Mathlib.RingTheory.ClassGroup.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.IdeleClassGroup

/-- Two invertible fractional ideals whose classes in `ClassGroup R` coincide differ by a
principal ideal: if `ClassGroup.mk K I = ClassGroup.mk K J`, then `I * toPrincipalIdeal R K x = J`
for some `x : Kˣ`. -/
theorem exists_units_mul_toPrincipalIdeal_eq_of_mk_eq {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    ∃ x : Kˣ, I * toPrincipalIdeal R K x = J := by
  -- Transport along the canonical isomorphism between `ClassGroup R` and the quotient of the
  -- invertible fractional ideals of `R` in `K` by the principal ones.
  have h1 : ClassGroup.equiv K (ClassGroup.mk K I) = ClassGroup.equiv K (ClassGroup.mk K J) := by
    rw [h]
  rw [ClassGroup.equiv_mk, ClassGroup.equiv_mk] at h1
  -- `K` is its own canonical fraction field here, so the transport is the identity.
  simp only [FractionalIdeal.canonicalEquiv_self] at h1
  -- Equality in the quotient means the two differ by an element of the principal subgroup.
  rw [QuotientGroup.mk'_eq_mk'] at h1
  obtain ⟨z, hz, hzJ⟩ := h1
  rw [MonoidHom.mem_range] at hz
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, hzJ⟩

end NK.GlobalCFT.IdeleClassGroup
