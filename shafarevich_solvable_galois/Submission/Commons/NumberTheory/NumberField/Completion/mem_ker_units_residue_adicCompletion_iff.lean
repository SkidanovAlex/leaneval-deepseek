import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- In a commutative local ring `R`, the units reducing to `1` modulo the maximal
ideal are exactly the principal units `1 + 𝔪`, i.e. `u` lies in the kernel of the
reduction map on units if and only if `u - 1` lies in the maximal ideal. -/
theorem mem_ker_units_residue_iff {R : Type*} [CommRing R] [IsLocalRing R] (u : Rˣ) :
    u ∈ (Units.map ((IsLocalRing.residue R).toMonoidHom)).ker ↔
      ((u : R) - 1) ∈ IsLocalRing.maximalIdeal R := by
  rw [MonoidHom.mem_ker]
  have hkey : IsLocalRing.residue R (u : R) = 1 ↔
      ((u : R) - 1) ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]
    constructor
    · intro h; rw [h, sub_self]
    · intro h; exact sub_eq_zero.mp h
  rw [← hkey]
  constructor
  · intro h
    have := congrArg
      (fun x : (IsLocalRing.ResidueField R)ˣ => (x : IsLocalRing.ResidueField R)) h
    simpa [Units.coe_map] using this
  · intro h
    apply Units.ext
    simp [Units.coe_map, h]

theorem mem_ker_units_residue_adicCompletion_iff {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (v.adicCompletionIntegers K)ˣ) :
    u ∈ (Units.map ((IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom)).ker ↔
      ((u : v.adicCompletionIntegers K) - 1) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
  mem_ker_units_residue_iff u

end Commons.NumberTheory.NumberField.Completion