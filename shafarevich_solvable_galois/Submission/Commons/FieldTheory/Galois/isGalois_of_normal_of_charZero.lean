import Mathlib.FieldTheory.Galois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Galois

/-- A finite normal extension of a field of characteristic zero is Galois.  (Separability is
automatic in characteristic zero: a finite-dimensional extension of a field is integral, and an
integral extension of a field of characteristic zero is separable.) -/
theorem isGalois_of_normal_of_charZero {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [FiniteDimensional F E] [Normal F E] : IsGalois F E := by
  rw [isGalois_iff]
  exact ⟨inferInstance, inferInstance⟩

end Commons.FieldTheory.Galois