/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The arithmetic of local fields: vocabulary

This is the entry point of the `Work.LocalFields` chapter.  It sets up the vocabulary used
throughout: finite primes of a number field, the completion at a finite prime, its ring of
integers, its residue field and its valuation; and a bundled notion of "non-archimedean local
field".

## Main definitions

* `Work.LocalFields.FinitePrime K` : the finite primes of a number field `K`, i.e. the
  nonzero prime ideals of `𝓞 K` (Mathlib's `IsDedekindDomain.HeightOneSpectrum`).
* `Work.LocalFields.Completion K v` : the `v`-adic completion `K_v`.
* `Work.LocalFields.intRing K v` : the ring of integers `𝒪_v` of `K_v`.
* `Work.LocalFields.residueFieldOf K v` : the residue field `κ_v` of `K_v`.
* `Work.LocalFields.IsLocalField k` : non-archimedean local fields (rank one, compact ring of
  integers), which is equivalent to the classical "complete discretely valued with finite
  residue field".
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

/-- The **finite primes** of a number field `K` are the maximal ideals of its ring of integers,
i.e. Mathlib's `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`. -/
abbrev FinitePrime (K : Type*) [Field K] : Type _ := IsDedekindDomain.HeightOneSpectrum (𝓞 K)

section NumberField

variable {K : Type*} [Field K] [NumberField K] (v : FinitePrime K)

/-- The `v`-adic **completion** `K_v` of a number field `K` at a finite prime `v`. -/
noncomputable abbrev Completion (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) : Type _ :=
  v.adicCompletion K

/-- The **ring of integers** `𝒪_v` of `K_v`: the valuation ring of the `v`-adic valuation. -/
noncomputable abbrev intRing (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) :
    Subring (Completion K v) := 𝒪[Completion K v]

/-- The **maximal ideal** of the ring of integers of `K_v`. -/
noncomputable abbrev maximalIdealAt (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) :
    Ideal (intRing K v) := 𝓂[Completion K v]

/-- The **residue field** `κ_v` of `K_v`. -/
abbrev residueFieldOf (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) : Type _ :=
  𝓀[Completion K v]

/-- The `v`-adic valuation on `K` itself. -/
noncomputable abbrev valOnK (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) :
    Valuation K ℤᵐ⁰ := IsDedekindDomain.HeightOneSpectrum.valuation K v

/-- The `v`-adic valuation on the completion, as a `ℤᵐ⁰`-valued valuation. -/
noncomputable abbrev adicVal (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) :
    Valuation (Completion K v) ℤᵐ⁰ := Valued.v

/-- The canonical embedding `K ↪ K_v`. -/
noncomputable abbrev emb (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) :
    K →+* Completion K v := algebraMap K (Completion K v)

/-- The `v`-adic absolute value on `K`, normalised so that `|π| = 1 / #κ_v` for a
uniformizer `π`. -/
noncomputable abbrev adicAbv (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) :
    AbsoluteValue K ℝ := NumberField.HeightOneSpectrum.adicAbv K v

/-- The *residue cardinality* `q_v = #κ_v = N(v)`, the norm of the prime `v`. -/
noncomputable abbrev residueCard (K : Type*) [Field K] [NumberField K] (v : FinitePrime K) : ℕ :=
  v.asIdeal.absNorm

/-- The equivalence between the finite primes of `K` (as we use them) and Mathlib's type of
finite places of a number field. -/
noncomputable def finitePrimeEquivFinitePlace (K : Type*) [Field K] [NumberField K] :
    FinitePrime K ≃ NumberField.FinitePlace K :=
  NumberField.FinitePlace.equivHeightOneSpectrum.symm

variable {v}

@[simp] theorem emb_apply (x : K) : emb K v x = (x : Completion K v) := rfl
@[simp] theorem emb_zero : emb K v (0 : K) = 0 := map_zero _
@[simp] theorem emb_one : emb K v (1 : K) = 1 := map_one _
@[simp] theorem emb_add (x y : K) : emb K v (x + y) = emb K v x + emb K v y := map_add _ _ _
@[simp] theorem emb_mul (x y : K) : emb K v (x * y) = emb K v x * emb K v y := map_mul _ _ _

/-- The canonical embedding of a number field into its completion at a finite prime is
injective. -/
theorem emb_injective : Function.Injective (emb K v) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  have h1 : (x : Completion K v) = 0 := hx
  have h2 : Valued.v (x : Completion K v) = 0 := by rw [h1, map_zero]
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K v x] at h2
  exact (v.valuation K).zero_iff.mp h2

/-- `𝓞 K ⧸ v` is finite. -/
theorem finite_quotient : Finite (𝓞 K ⧸ v.asIdeal) :=
  v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot

noncomputable instance : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _

/-- The norm `N(v) = #(𝓞 K ⧸ v)` of a finite prime is `> 1`. -/
theorem one_lt_residueCard : 1 < residueCard K v :=
  NumberField.HeightOneSpectrum.one_lt_absNorm v

end NumberField

/-! ## Non-archimedean local fields

The completion `K_v` of a number field carries a `Valued K_v ℤᵐ⁰` structure coming from the
`v`-adic valuation, and it is a (non-archimedean) local field: its ring of integers is compact.
We record this as a small class, tailored to the `Valued _ ℤᵐ⁰` situation, and derive from it the
facts one wants about local fields. -/

/-- A **non-archimedean local field**, in the form used in this development: a field `k` carrying
a `ℤᵐ⁰`-valued valuation whose topology is the valuation topology, such that the valuation has
rank one and the ring of integers `𝒪[k]` is compact.

(For a valued field with rank-one valuation, compactness of `𝒪[k]` is equivalent to
"complete + discretely valued + finite residue field", the classical definition of a local
field.) -/
class IsLocalField (k : Type*) [Field k] [Valued k ℤᵐ⁰] : Prop where
  /-- The valuation has rank one. -/
  rankOne : Nonempty (Valued.v (R := k)).RankOne
  /-- The field is complete. -/
  complete : CompleteSpace k
  /-- The ring of integers is compact. -/
  compactInteger : CompactSpace 𝒪[k]

namespace IsLocalField

variable {k : Type*} [Field k] [Valued k ℤᵐ⁰]

/-- The rank-one structure of a local field. -/
noncomputable def rankOneData (h : IsLocalField k) : (Valued.v (R := k)).RankOne := h.rankOne.some

/-- The rank-one structure of a local field, as a (low priority) instance. -/
noncomputable instance (priority := low) instRankOne [h : IsLocalField k] :
    (Valued.v (R := k)).RankOne := h.rankOne.some

instance instComplete [h : IsLocalField k] : CompleteSpace k := h.complete

instance instCompactInteger [h : IsLocalField k] : CompactSpace 𝒪[k] := h.compactInteger

/-- The ring of integers of a local field is a discrete valuation ring. -/
instance instDVR [h : IsLocalField k] : IsDiscreteValuationRing 𝒪[k] :=
  ((Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := k) (Γ₀ := ℤᵐ⁰)).mp h.compactInteger).2.1

/-- The residue field of a local field is finite. -/
instance instFiniteResidueField [h : IsLocalField k] : Finite 𝓀[k] :=
  ((Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := k) (Γ₀ := ℤᵐ⁰)).mp h.compactInteger).2.2

/-- The ring of integers of a local field is complete. -/
instance instCompleteSpaceInt [h : IsLocalField k] : CompleteSpace 𝒪[k] :=
  ((Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := k) (Γ₀ := ℤᵐ⁰)).mp h.compactInteger).1

/-- A non-archimedean local field is proper as a metric space. -/
instance instProperSpace [h : IsLocalField k] : ProperSpace k :=
  (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := k) (Γ₀ := ℤᵐ⁰)).mpr
    ⟨h.complete, inferInstance, inferInstance⟩

/-- A local field is not a field with the discrete valuation: its maximal ideal is nontrivial. -/
theorem maximalIdeal_ne_bot [h : IsLocalField k] : 𝓂[k] ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field 𝒪[k]

/-- A local field has a uniformizer. -/
theorem exists_irreducible [h : IsLocalField k] : ∃ π : 𝒪[k], Irreducible π :=
  IsDiscreteValuationRing.exists_irreducible 𝒪[k]

end IsLocalField

end Work.LocalFields
