import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- In a commutative local ring `R` with maximal ideal `𝔪`, an element whose
reduction modulo `𝔪` is a unit is itself a unit (its residue is nonzero, hence
it does not lie in `𝔪`).  Consequently reduction of units modulo the maximal
ideal,
`Rˣ → (R ⧸ 𝔪)ˣ`, is surjective. -/
theorem surjective_units_residue_of_isLocalRing {R : Type*} [CommRing R] [IsLocalRing R] :
    Function.Surjective (Units.map ((IsLocalRing.residue R).toMonoidHom)) := by
  intro u
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := R) (u : IsLocalRing.ResidueField R)
  have hxu : IsUnit x :=
    (IsLocalRing.residue_ne_zero_iff_isUnit x).mp (by rw [hx]; exact u.ne_zero)
  refine ⟨hxu.unit, ?_⟩
  exact Units.ext (by rw [Units.coe_map, IsUnit.unit_spec]; exact hx)

theorem surjective_units_residue_adicCompletion {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Surjective (Units.map ((IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom)) :=
  surjective_units_residue_of_isLocalRing

end Commons.NumberTheory.NumberField.Completion