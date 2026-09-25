/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver

/-!
# Places of a number field and their local fields

This file sets up the geometry of places of a number field `K`, the local fields `K_v` and their
groups of units `K_vˣ` together with the subgroups `𝒪_vˣ` of local units.  It is the base layer
for the idèles (`NK.GlobalCFT.Idele`) and for global class field theory.

## Main definitions

* `NK.GlobalCFT.Place K`: the places of `K`, the disjoint union of the archimedean places
  (`InfinitePlace K`) and the nonarchimedean ones (the nonzero primes of `𝓞 K`).
* `NK.GlobalCFT.Place.localField K v`: the completion `K_v` of `K` at `v`; a `NormedField`.
* `NK.GlobalCFT.Place.localUnits K v : Subgroup (localField K v)ˣ`: the group of units `𝒪_vˣ`
  for a finite place (all of `K_vˣ` at an infinite place).
* `NK.GlobalCFT.Place.LiesOver`: the relation "the place `w` of `L` lies over the place `v`
  of `K`", for a finite extension `L/K`.
* `NK.GlobalCFT.Place.fiberInfinite`, `NK.GlobalCFT.Place.primesOverFinite`: the finite sets
  of places of `L` above a given place of `K`.

## Implementation notes

The local units at an archimedean place are *all* of `K_vˣ`, so that the idèles are the usual
restricted product which only restricts at the nonarchimedean places.  Consequently
`∏_v 𝒪_vˣ` is *not* compact (the archimedean factors are not compact); the compact object is
`∏_{v finite} 𝒪_vˣ`; see `NK.GlobalCFT.Idele`.
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

/-- The places of the number field `K`: the disjoint union of the archimedean places and the
nonarchimedean places (nonzero prime ideals of `𝓞 K`). -/
abbrev Place (K : Type*) [Field K] [NumberField K] : Type _ :=
  InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)

namespace Place

variable {K : Type*} [Field K] [NumberField K]

/-- The infinite (archimedean) place attached to an element of `InfinitePlace K`. -/
abbrev ofInfinite (w : InfinitePlace K) : Place K := Sum.inl w

/-- The finite (nonarchimedean) place attached to a nonzero prime ideal of `𝓞 K`. -/
abbrev ofFinite (q : HeightOneSpectrum (𝓞 K)) : Place K := Sum.inr q

@[simp] theorem ofInfinite_inj {w w' : InfinitePlace K} :
    ofInfinite w = ofInfinite w' ↔ w = w' := by simp [ofInfinite]

@[simp] theorem ofFinite_inj {q q' : HeightOneSpectrum (𝓞 K)} :
    ofFinite q = ofFinite q' ↔ q = q' := by simp [ofFinite]

theorem ofInfinite_ne_ofFinite (w : InfinitePlace K) (q : HeightOneSpectrum (𝓞 K)) :
    ofInfinite w ≠ ofFinite q := Sum.inl_ne_inr

/-- A place is infinite (archimedean) if it comes from an archimedean place of `K`. -/
def IsInfinite : Place K → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- A place is finite (nonarchimedean) if it is not archimedean. -/
def IsFinite (v : Place K) : Prop := ¬ IsInfinite v

instance (v : Place K) : Decidable (IsInfinite v) := by
  cases v <;> (unfold IsInfinite; infer_instance)

instance (v : Place K) : Decidable (IsFinite v) := by
  unfold IsFinite; infer_instance

@[simp] theorem isInfinite_ofInfinite (w : InfinitePlace K) : IsInfinite (ofInfinite w) := trivial

@[simp] theorem not_isInfinite_ofFinite (q : HeightOneSpectrum (𝓞 K)) :
    ¬ IsInfinite (ofFinite q) := not_false

@[simp] theorem isFinite_ofFinite (q : HeightOneSpectrum (𝓞 K)) : IsFinite (ofFinite q) :=
  not_false

@[simp] theorem not_isFinite_ofInfinite (w : InfinitePlace K) : ¬ IsFinite (ofInfinite w) := by
  simp [IsFinite, IsInfinite]

theorem isFinite_iff {v : Place K} : IsFinite v ↔ ∃ q, v = ofFinite q := by
  cases v with
  | inl w => simp [IsFinite, IsInfinite]
  | inr q => simp

theorem isInfinite_iff {v : Place K} : IsInfinite v ↔ ∃ w, v = ofInfinite w := by
  cases v with
  | inl w => simp
  | inr q => simp [IsInfinite]

theorem isFinite_iff_not_isInfinite {v : Place K} : IsFinite v ↔ ¬ IsInfinite v := Iff.rfl

/-! ### The local field at a place -/

/-- The completion of `K` at the place `v`: the archimedean completion at an infinite place, the
`v`-adic completion at a finite place. -/
abbrev localField (K : Type*) [Field K] [NumberField K] : Place K → Type _
  | Sum.inl w => w.Completion
  | Sum.inr q => q.adicCompletion K

@[simp] theorem localField_ofInfinite (w : InfinitePlace K) :
    localField K (ofInfinite w) = w.Completion := rfl

@[simp] theorem localField_ofFinite (q : HeightOneSpectrum (𝓞 K)) :
    localField K (ofFinite q) = q.adicCompletion K := rfl

instance (v : Place K) : Field (localField K v) := by
  cases v with
  | inl w => exact inferInstanceAs (Field w.Completion)
  | inr q => exact inferInstanceAs (Field (q.adicCompletion K))

instance (v : Place K) : NormedField (localField K v) := by
  cases v with
  | inl w => exact inferInstanceAs (NormedField w.Completion)
  | inr q => exact inferInstanceAs (NormedField (q.adicCompletion K))

instance (v : Place K) : Algebra K (localField K v) := by
  cases v with
  | inl w => exact inferInstanceAs (Algebra K w.Completion)
  | inr q => exact inferInstanceAs (Algebra K (q.adicCompletion K))

instance (v : Place K) : Field (localField K v) := by
  cases v with
  | inl w => exact inferInstanceAs (Field w.Completion)
  | inr q => exact inferInstanceAs (Field (q.adicCompletion K))

instance (v : Place K) : NormedField (localField K v) := by
  cases v with
  | inl w => exact inferInstanceAs (NormedField w.Completion)
  | inr q => exact inferInstanceAs (NormedField (q.adicCompletion K))

instance (v : Place K) : IsTopologicalRing (localField K v) := by
  cases v with
  | inl w => exact inferInstanceAs (IsTopologicalRing w.Completion)
  | inr q => exact inferInstanceAs (IsTopologicalRing (q.adicCompletion K))

instance (v : Place K) : IsOpenUnits (localField K v) := by
  cases v with
  | inl w => exact inferInstanceAs (IsOpenUnits w.Completion)
  | inr q => exact inferInstanceAs (IsOpenUnits (q.adicCompletion K))

instance (v : Place K) : IsTopologicalGroup ((localField K v)ˣ) := by
  cases v with
  | inl w => exact inferInstanceAs (IsTopologicalGroup w.Completionˣ)
  | inr q => exact inferInstanceAs (IsTopologicalGroup (q.adicCompletion K)ˣ)

/-- The group of local units `𝒪_vˣ` at a finite place, and all of `K_vˣ` at an infinite place. -/
def localUnits (K : Type*) [Field K] [NumberField K] (v : Place K) :
    Subgroup ((localField K v)ˣ) :=
  match v with
  | Sum.inl _ => ⊤
  | Sum.inr q => (q.adicCompletionIntegers K).units

@[simp] theorem localUnits_ofInfinite (w : InfinitePlace K) :
    localUnits K (ofInfinite w) = ⊤ := rfl

@[simp] theorem localUnits_ofFinite (q : HeightOneSpectrum (𝓞 K)) :
    localUnits K (ofFinite q) = (q.adicCompletionIntegers K).units := rfl

/-- Membership in the local units at a finite place is "valuation one". -/
theorem mem_localUnits_ofFinite_iff_valued_eq_one {q : HeightOneSpectrum (𝓞 K)}
    {x : (q.adicCompletion K)ˣ} :
    x ∈ localUnits K (ofFinite q) ↔ Valued.v (x : q.adicCompletion K) = 1 := by
  rw [localUnits_ofFinite]
  exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one

/-- Membership in the local units at a finite place, in terms of the unit ball. -/
theorem mem_localUnits_ofFinite {q : HeightOneSpectrum (𝓞 K)}
    {x : (q.adicCompletion K)ˣ} :
    x ∈ localUnits K (ofFinite q) ↔
      (x : q.adicCompletion K) ∈ q.adicCompletionIntegers K ∧
        ((x⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K) ∈ q.adicCompletionIntegers K :=
  Submonoid.mem_units_iff _ x

theorem mem_localUnits_ofInfinite {w : InfinitePlace K} {x : (localField K (ofInfinite w))ˣ} :
    x ∈ localUnits K (ofInfinite w) := trivial

/-- The local units are open in the local unit group in the archimedean case (they are
everything). -/
theorem isOpen_localUnits_ofInfinite (w : InfinitePlace K) :
    IsOpen (localUnits K (ofInfinite w) : Set ((localField K (ofInfinite w))ˣ)) := by
  rw [localUnits_ofInfinite]; exact isOpen_univ

/-- The local units are open subgroups of the local unit groups: at an archimedean place they
are everything, at a finite place they are the units of the valuation ring, i.e. the elements of
the (open) unit ball whose inverse is also in the unit ball. -/
theorem isOpen_localUnits (v : Place K) :
    IsOpen (localUnits K v : Set ((localField K v)ˣ)) := by
  cases v with
  | inl w =>
      rw [localUnits_ofInfinite]
      exact isOpen_univ
  | inr q =>
      rw [localUnits_ofFinite]
      have h1 : IsOpen {x : (q.adicCompletion K)ˣ |
          (x : q.adicCompletion K) ∈ q.adicCompletionIntegers K} :=
        (Valued.isOpen_valuationSubring (q.adicCompletion K)).preimage Units.continuous_val
      have h2 : IsOpen {x : (q.adicCompletion K)ˣ |
          ((x⁻¹ : (q.adicCompletion K)ˣ) : q.adicCompletion K) ∈ q.adicCompletionIntegers K} :=
        h1.preimage continuous_inv
      convert h1.inter h2 using 2
      all_goals rfl

instance : Fact (∀ v : Place K, IsOpen (localUnits K v : Set ((localField K v)ˣ))) :=
  ⟨isOpen_localUnits⟩

/-! ### Places of an extension field

For a finite extension `L / K` of number fields we set up the relation "`w` lies over `v`" and the
finite fibres of the map `w ↦ v`, together with the local norms `N_{L_w/K_v}`. -/

section Extension

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- The place `w` of `L` lies over the place `v` of `K` if the corresponding absolute values
restrict to each other. -/
def LiesOver (w : Place L) (v : Place K) : Prop :=
  (∃ (w' : InfinitePlace L) (v' : InfinitePlace K),
      w = ofInfinite w' ∧ v = ofInfinite v' ∧ w'.LiesOver v') ∨
    (∃ (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K)),
      w = ofFinite q ∧ v = ofFinite Q ∧ q.asIdeal.LiesOver Q.asIdeal)

theorem liesOver_iff (w : Place L) (v : Place K) :
    LiesOver w v ↔
      (∃ (w' : InfinitePlace L) (v' : InfinitePlace K),
        w = ofInfinite w' ∧ v = ofInfinite v' ∧ w'.LiesOver v') ∨
      (∃ (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K)),
        w = ofFinite q ∧ v = ofFinite Q ∧ q.asIdeal.LiesOver Q.asIdeal) := Iff.rfl

theorem liesOver_ofInfinite {w : InfinitePlace L} {v : InfinitePlace K} (h : w.LiesOver v) :
    LiesOver (ofInfinite w) (ofInfinite v) := Or.inl ⟨w, v, rfl, rfl, h⟩

theorem liesOver_ofFinite {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 K)}
    (h : q.asIdeal.LiesOver Q.asIdeal) : LiesOver (ofFinite q) (ofFinite Q) :=
  Or.inr ⟨q, Q, rfl, rfl, h⟩

/-- Nonarchimedeanness is preserved by the "lies over" relation. -/
theorem isFinite_of_liesOver {w : Place L} {v : Place K} (h : LiesOver w v) :
    IsFinite w ↔ IsFinite v := by
  rcases h with ⟨w', v', rfl, rfl, _⟩ | ⟨q, Q, rfl, rfl, _⟩ <;> simp

/-- The infinite places of `L` above a given infinite place of `K`. -/
noncomputable def fiberInfinite (v : InfinitePlace K) : Finset (InfinitePlace L) := by
  classical exact (Finset.univ : Finset (InfinitePlace L)).filter (fun w => w.LiesOver v)

@[simp] theorem mem_fiberInfinite {v : InfinitePlace K} {w : InfinitePlace L} :
    w ∈ fiberInfinite v ↔ w.LiesOver v := by
  classical simp [fiberInfinite]

/-- The finite places of `L` above a given nonzero prime of `𝓞 K`: the primes of `𝓞 L` lying
over `Q`. -/
noncomputable def primesOverFinite (Q : HeightOneSpectrum (𝓞 K)) :
    Finset (HeightOneSpectrum (𝓞 L)) := by
  classical
  have hfin : (Q.asIdeal.primesOver (𝓞 L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver Q.asIdeal Q.isPrime Q.ne_bot
  letI : Fintype ↥(Q.asIdeal.primesOver (𝓞 L)) := hfin.fintype
  exact Finset.univ.image
    (fun q : ↥(Q.asIdeal.primesOver (𝓞 L)) =>
      ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver Q.ne_bot q.2⟩)

theorem mem_primesOverFinite {Q : HeightOneSpectrum (𝓞 K)} {q : HeightOneSpectrum (𝓞 L)} :
    q ∈ primesOverFinite Q ↔ q.asIdeal.LiesOver Q.asIdeal := by
  classical
  have hfin : (Q.asIdeal.primesOver (𝓞 L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver Q.asIdeal Q.isPrime Q.ne_bot
  letI : Fintype ↥(Q.asIdeal.primesOver (𝓞 L)) := hfin.fintype
  rw [primesOverFinite]
  constructor
  · intro h
    obtain ⟨I, -, hI⟩ := Finset.mem_image.mp h
    have hq : q.asIdeal = I.1 := by rw [← hI]
    rw [hq]
    exact I.2.2
  · intro h
    refine Finset.mem_image.mpr ⟨⟨q.asIdeal, q.isPrime, h⟩, Finset.mem_univ _, ?_⟩
    exact HeightOneSpectrum.ext rfl

/-- The local algebra structure at an infinite place: `L_w` is a `K_v`-algebra. -/
noncomputable def localAlgebraMapInfinite (w : InfinitePlace L) (v : InfinitePlace K)
    [w.LiesOver v] : v.Completion →+* w.Completion :=
  NumberField.LiesOver.completionMap (v := v) (w := w)

/-- The local algebra structure at a finite place: `L_q` is a `K_Q`-algebra. -/
noncomputable def localAlgebraMapFinite (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) (h : q.asIdeal.LiesOver Q.asIdeal) :
    Q.adicCompletion K →+* q.adicCompletion L :=
  Commons.RingTheory.Henselian.adicCompletionMap Q q h

/-- The local norm `N_{L_w/K_v} : L_wˣ →* K_vˣ` at an infinite place. -/
noncomputable def localNormInfinite (w : InfinitePlace L) (v : InfinitePlace K) [w.LiesOver v] :
    w.Completionˣ →* v.Completionˣ :=
  letI : Algebra v.Completion w.Completion :=
    (NumberField.LiesOver.completionMap (v := v) (w := w)).toAlgebra
  Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)

/-- The local norm `N_{L_q/K_Q} : L_qˣ →* K_Qˣ` at a finite place. -/
noncomputable def localNormFinite (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) (h : q.asIdeal.LiesOver Q.asIdeal) :
    (q.adicCompletion L)ˣ →* (Q.adicCompletion K)ˣ :=
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q h).toAlgebra
  Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)

end Extension

/-! ### The action of the Galois group on the places of `L`

For a finite extension `L / K` the automorphism group `Gal(L/K) = (L ≃ₐ[K] L)` acts on the places
of `L`: an archimedean place is composed with the automorphism, a nonarchimedean place is the
image prime under the induced automorphism of `𝓞 L`.  This is the geometric input for the action
of `Gal(L/K)` on the idèle group `𝕀 L` and on the idèle class group `C_L`. -/

section GaloisAction

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The induced automorphism of `𝓞 L` attached to `σ : L ≃ₐ[K] L`. -/
noncomputable def ringOfIntegersEquiv (σ : L ≃ₐ[K] L) : (𝓞 L) ≃+* (𝓞 L) :=
  (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv

@[simp] theorem ringOfIntegersEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    ringOfIntegersEquiv σ x = σ x := rfl

/-- The image of a nonzero prime of `𝓞 L` under `σ : L ≃ₐ[K] L`, i.e. the prime `σ 𝔮`; this is
the convention of "precomposition with `σ⁻¹`", matching Mathlib's action on the archimedean
places (`σ • w = w ∘ σ⁻¹`). -/
noncomputable def smulHeightOneSpectrum (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 L) :=
  ⟨Ideal.map (ringOfIntegersEquiv σ) q.asIdeal,
    inferInstance,
    fun h => q.ne_bot ((Ideal.map_eq_bot_iff_of_injective
      (ringOfIntegersEquiv σ).injective).mp h)⟩

@[simp] theorem smulHeightOneSpectrum_asIdeal (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    (smulHeightOneSpectrum σ q).asIdeal =
      Ideal.map (ringOfIntegersEquiv σ) q.asIdeal := rfl

/-- The action of `Gal(L/K)` on the places of `L`. -/
noncomputable instance : SMul (L ≃ₐ[K] L) (Place L) where
  smul σ v :=
    match v with
    | Sum.inl w => Sum.inl (σ • w)
    | Sum.inr q => Sum.inr (smulHeightOneSpectrum σ q)

@[simp] theorem smul_ofInfinite (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    σ • ofInfinite w = ofInfinite (σ • w) := rfl

@[simp] theorem smul_ofFinite (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    σ • ofFinite q = ofFinite (smulHeightOneSpectrum σ q) := rfl

end GaloisAction

end Place

end NK.GlobalCFT

