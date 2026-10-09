/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The residue units of a `p`-adic field modulo the principal units

For `κ = K_𝔭` the `𝔭`-adic completion of a number field `K` at a finite prime `𝔭` with residue
field cardinality `q = residueCard K 𝔭`, the reduction map
`𝒪_κˣ → (𝒪_κ/𝔪_κ)ˣ = κ̄ˣ` is surjective with kernel the group `U¹ = principalUnits K 𝔭` of
principal units.  Hence

  `𝒪_κˣ ⧸ U¹ ≃* κ̄ˣ`,

and since `κ̄` is a finite field of cardinality `q`, its unit group is cyclic of order `q - 1`, so

  `𝒪_κˣ ⧸ U¹ ≃* Multiplicative (ZMod (q - 1))`,

the group of order `q - 1` written multiplicatively.  This is the combinatorial half of the
description `κˣ ≅ ℤ × μ_{q-1} × U¹` of the local units.

The proof is: `principalUnits` *is* the kernel of the reduction map on units
(`NK.LocalInputs.mem_principalUnits_iff`), that map is surjective
(`Commons....surjective_units_residue_adicCompletion`), the residue field is finite
(`Commons....finite_residueField_adicCompletion`) so its unit group is cyclic
(`instIsCyclicUnitsOfFinite`), and `Nat.card_units` computes its cardinality as `q - 1`.
-/
import Mathlib
import Submission.NK.LocalInputs.All
import Submission.NK.LocalStructure.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep.Units

/-- **A cyclic group of order `n` is `Multiplicative (ZMod n)`.**  Elementary transport of
`zmodCyclicMulEquiv` along an equality of the cardinality with `n`; the statement is `Nonempty`
because the isomorphism is non-canonical (it depends on the choice of a generator). -/
theorem nonempty_mulEquiv_multiplicative_zmod_of_isCyclic (G : Type*) [Group G] (h : IsCyclic G)
    {n : ℕ} (hn : Nat.card G = n) : Nonempty (G ≃* Multiplicative (ZMod n)) :=
  ⟨hn ▸ (zmodCyclicMulEquiv h).symm⟩

/-- **The unit group of the residue field is cyclic**: the residue field of the `𝔭`-adic
completion of a number field is a finite field, and the units of a finite field form a cyclic
group. -/
theorem isCyclic_residueUnits {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsCyclic (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ := by
  have hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  have hunit : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ :=
    Finite.of_injective _ Units.val_injective
  exact instIsCyclicUnitsOfFinite

/-- **The cardinality of the residue units.**  The units of the residue field of `𝒪_κ` number
`q - 1`, where `q = residueCard K 𝔭` is the residue field cardinality. -/
theorem natCard_residueUnits {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ =
      NK.LocalStructure.residueCard K 𝔭 - 1 := by
  rw [Nat.card_units, NK.LocalStructure.residueCard]

/-- **The residue units are the units of `𝒪_κ` modulo the principal units.**  The reduction map
on units `𝒪_κˣ → (𝒪_κ/𝔪_κ)ˣ` is surjective with kernel `principalUnits K 𝔭`. -/
theorem nonempty_residueUnits_quot_principalUnits {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (((𝔭.adicCompletionIntegers K)ˣ ⧸ NK.LocalInputs.principalUnits K 𝔭) ≃*
      (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ) :=
  ⟨QuotientGroup.quotientKerEquivOfSurjective
    (Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom)
    (Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion 𝔭)⟩

/-- **The residue units modulo the principal units are cyclic of order `q - 1`**, where
`q = residueCard K 𝔭` is the residue field cardinality of the `𝔭`-adic completion `κ` of a
number field `K`: the standard identification `𝒪_κˣ/U¹ ≅ κ̄ˣ` of the units of the local field
with the units of its (finite) residue field. -/
theorem residueUnits_quot_principalUnits_mulEquiv {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (((𝔭.adicCompletionIntegers K)ˣ ⧸ NK.LocalInputs.principalUnits K 𝔭) ≃*
      Multiplicative (ZMod (NK.LocalStructure.residueCard K 𝔭 - 1))) := by
  obtain ⟨e⟩ := nonempty_residueUnits_quot_principalUnits 𝔭
  obtain ⟨f⟩ := nonempty_mulEquiv_multiplicative_zmod_of_isCyclic _
    (isCyclic_residueUnits 𝔭) (natCard_residueUnits 𝔭)
  exact ⟨e.trans f⟩

end NK.TameStructureDeep.Units
