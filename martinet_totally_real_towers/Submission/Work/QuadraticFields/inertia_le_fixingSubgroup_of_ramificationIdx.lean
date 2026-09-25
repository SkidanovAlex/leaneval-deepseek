import Mathlib
import Submission.Work.QuadraticFields.Ramification
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le

/-!
# Inertia groups of unramified subextensions

If `L ⊆ M` are number fields with `L/ℚ` and `M/ℚ` Galois, `p` is a rational prime and every prime
of `𝓞 L` above `p` is unramified over `ℤ`, then the inertia group of any prime `𝔓` of `𝓞 M` above
`p` fixes `L` pointwise.  Equivalently, `I(𝔓)` is contained in the fixing subgroup of `L`.

The proof is the standard one:

* the restriction of `I(𝔓) ≤ Gal(M/ℚ)` to `L` is contained in `I(𝔓 ∩ 𝓞 L) ≤ Gal(L/ℚ)`
  (`inertia_map_restrictNormalHom_le`);
* `Nat.card I(𝔮) = e(𝔮)` for `𝔮` a prime of a Galois extension of `ℚ` over a prime of `ℤ`
  (`Ideal.card_inertia_eq_ramificationIdxIn`), so `e(𝔮) = 1` forces `I(𝔮) = ⊥`;
* hence the restriction map kills `I(𝔓)`, i.e. `I(𝔓) ≤ ker (restrictNormalHom L) = L.fixingSubgroup`.

## Main result

* `Work.QuadraticFields.inertia_le_fixingSubgroup_of_ramificationIdx`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField

theorem inertia_le_fixingSubgroup_of_ramificationIdx {M : Type*} [Field M] [NumberField M]
    [IsGalois ℚ M] (L : IntermediateField ℚ M) [FiniteDimensional ℚ ↥L] [Normal ℚ ↥L]
    (p : ℕ) (hp : Nat.Prime p) (𝔓 : Ideal (NumberField.RingOfIntegers M)) [𝔓.IsPrime]
    (h𝔓 : (p : NumberField.RingOfIntegers M) ∈ 𝔓)
    (hunr : ∀ (𝔮 : Ideal (NumberField.RingOfIntegers ↥L)), 𝔮.IsPrime →
      ((p : NumberField.RingOfIntegers ↥L) ∈ 𝔮) →
      𝔮.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1) :
    Ideal.inertia (M ≃ₐ[ℚ] M) 𝔓 ≤ L.fixingSubgroup := by
  haveI : NumberField ↥L := NumberField.of_module_finite ℚ ↥L
  haveI : IsGalois ℚ ↥L := IsGalois.mk
  -- `𝔮 := 𝔓 ∩ 𝓞 L` is the prime of `L` below `𝔓`; it lies over `p`.
  have hQprime : (𝔓.under (𝓞 ↥L)).IsPrime := Ideal.IsPrime.under _ 𝔓
  have hQmem : (p : 𝓞 ↥L) ∈ 𝔓.under (𝓞 ↥L) := by
    rw [Ideal.mem_under, map_natCast]
    exact h𝔓
  -- `p` is unramified in `L`, so the inertia group of `𝔮` in `Gal(L/ℚ)` is trivial.
  have hram : (𝔓.under (𝓞 ↥L)).ramificationIdx (𝓞 ℚ) = 1 := hunr _ hQprime hQmem
  have hbot : Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (𝔓.under (𝓞 ↥L)) = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (F := ℚ) (K := ↥L) ((𝔓.under (𝓞 ↥L)).under (𝓞 ℚ))
      (𝔓.under (𝓞 ↥L))).mpr hram
  -- The restriction of `I(𝔓)` to `L` lands in the inertia group of `𝔮`.
  have hle := Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le
      (F := ℚ) (L := ↥L) (M := M) ((𝔓.under (𝓞 ↥L)).under (𝓞 ℚ)) (𝔓.under (𝓞 ↥L)) 𝔓
  rw [← IntermediateField.restrictNormalHom_ker L]
  intro σ hσ
  have hmem : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := M) (E := ↥L) σ ∈
      Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (𝔓.under (𝓞 ↥L)) :=
    hle (Subgroup.mem_map_of_mem _ hσ)
  rw [hbot] at hmem
  simpa using hmem

end Work.QuadraticFields
