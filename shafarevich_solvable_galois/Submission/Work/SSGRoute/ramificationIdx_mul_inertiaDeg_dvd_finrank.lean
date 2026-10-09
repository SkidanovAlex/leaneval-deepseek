import Mathlib
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.style.haveILetI false

open NumberField
open scoped Pointwise

namespace Work.SSGRoute

/-- For a finite Galois extension `L/k` of number fields, a finite place `v₀` of `k` and a finite place `r` of `L` above it, the local degree `e(r)·f(r)` divides the global degree `[L : k]`. -/
theorem ramificationIdx_mul_inertiaDeg_dvd_finrank (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (h : r.asIdeal.LiesOver v₀.asIdeal) : r.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) * r.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ∣ Module.finrank k L := by
  classical
  -- `Gal(L/k)` acts on the ring of integers `𝓞 L` as a Galois group over `𝓞 k`
  haveI : IsGaloisGroup Gal(L/k) (𝓞 k) (𝓞 L) := inferInstance
  haveI hlies : r.asIdeal.LiesOver v₀.asIdeal := h
  -- the residue field at a height-one prime of a number field is finite, hence perfect
  haveI hperf : PerfectField v₀.asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum v₀
  -- the decomposition group at `r` has cardinality the local degree `e(r)·f(r)`
  have key : Nat.card (MulAction.stabilizer Gal(L/k) r.asIdeal) =
      v₀.asIdeal.ramificationIdxIn (𝓞 L) * v₀.asIdeal.inertiaDegIn (𝓞 L) :=
    Ideal.card_stabilizer_eq v₀.asIdeal r.asIdeal
  -- and the "in" invariants agree with the invariants of the chosen prime `r`
  have h1 : v₀.asIdeal.ramificationIdxIn (𝓞 L) = r.asIdeal.ramificationIdx (𝓞 k) :=
    Ideal.ramificationIdxIn_eq_ramificationIdx v₀.asIdeal r.asIdeal Gal(L/k)
  have h2 : v₀.asIdeal.inertiaDegIn (𝓞 L) = r.asIdeal.inertiaDeg (𝓞 k) :=
    Ideal.inertiaDegIn_eq_inertiaDeg v₀.asIdeal r.asIdeal Gal(L/k)
  rw [h1, h2] at key
  rw [← key]
  -- the decomposition group is a subgroup of `Gal(L/k) = Aut(L/k)`, whose order is `[L : k]`
  calc Nat.card (MulAction.stabilizer Gal(L/k) r.asIdeal)
      ∣ Nat.card (Gal(L/k)) := Subgroup.card_subgroup_dvd_card _
    _ = Module.finrank k L := IsGalois.card_aut_eq_finrank k L

end Work.SSGRoute
