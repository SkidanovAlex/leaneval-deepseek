import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv

/-!
# The universe bookkeeping for the index form of Hasse's norm theorem

`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` proves
`[C_K : N_{L/K} C_L] = [L : K]` for cyclic extensions of number fields, but with the two fields
living in the universe `Type 0` (`{K L : Type}`).  The present file removes that restriction: it
transports the two fields, together with the whole structure of the extension, to their `Shrink`
models in `Type 0`.

Mathlib already transports the field, algebra, module and finite-dimensionality structures to
`Shrink α`.  What is *not* in Mathlib is the transport of the extension itself, i.e. of

* the `Shrink K`-algebra structure on `Shrink L` (`shrinkAlgebra`), with `algebraMap` given by
  `Shrink L ← L ← K ← Shrink K`;
* the finiteness and Galois-ness of the transported extension — both from Mathlib's
  `Module.Finite.of_equiv_equiv` and `IsGalois.of_equiv_equiv`, applied to the ring equivalences
  `Shrink.ringEquiv K`, `Shrink.ringEquiv L`;
* the cyclicity of the transported Galois group, from the conjugation isomorphism
  `Submission.NeukirchUchida.conjHomEquiv` and the `MapsBase` computation `shrink_mapsBase`.

Together with the invariance of `finrank` (`Algebra.finrank_eq_of_equiv_equiv`) and of the norm
index (`NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv`) this gives the statement of
`NK.GlobalCFTdeep.hasseNorm_index_eq_universe`. -/

namespace NK.GlobalCFTdeep

set_option linter.style.haveILetI false

namespace HasseIndex

universe u v

noncomputable section

/-- **The transported `Shrink K`-algebra structure on `Shrink L`.**

`algebraMap` is the composite `Shrink K → K → L → Shrink L` (where the first map is the inverse of
`Shrink.ringEquiv K` and the last one that of `Shrink.ringEquiv L`), so that the two ring
equivalences are compatible with the algebra structures *definitionally* (`shrink_algebraMap`), and
`Shrink L` with its canonical `K`-algebra structure is a `Shrink K`-algebra with the same
multiplication. -/
noncomputable instance shrinkAlgebra (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Small.{0} K] [Small.{0} L] : Algebra (Shrink.{0} K) (Shrink.{0} L) :=
  RingHom.toAlgebra
    (((Shrink.ringEquiv L).symm : L →+* Shrink L).comp
      ((algebraMap K L).comp (Shrink.ringEquiv K).toRingHom))

/-- The defining computation of `shrinkAlgebra`: `algebraMap` is the composite of the two
`Shrink` ring equivalences with `algebraMap K L`. -/
@[simp]
theorem shrink_algebraMap (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] (r : Shrink.{0} K) :
    algebraMap (Shrink K) (Shrink L) r =
      (Shrink.ringEquiv L).symm (algebraMap K L ((Shrink.ringEquiv K) r)) := rfl

/-- **Compatibility of the shrink equivalences with the algebra maps** (the hypothesis of
Mathlib's `Module.Finite.of_equiv_equiv`, `IsGalois.of_equiv_equiv` and
`Algebra.finrank_eq_of_equiv_equiv`): shrinking commutes with the extension. -/
theorem shrink_algebraMap_compat (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] (x : K) :
    algebraMap (Shrink K) (Shrink L) ((Shrink.ringEquiv K).symm.toRingHom x) =
      (Shrink.ringEquiv L).symm.toRingHom (algebraMap K L x) := by
  rw [show algebraMap (Shrink K) (Shrink L) ((Shrink.ringEquiv K).symm.toRingHom x) =
      (Shrink.ringEquiv L).symm.toRingHom
        (algebraMap K L ((Shrink.ringEquiv K).toRingHom ((Shrink.ringEquiv K).symm.toRingHom x)))
      from rfl]
  simp

/-- The same compatibility of `shrink_algebraMap_compat`, with the `RingEquiv`s read as functions
(this is the form of the hypothesis of `normClassSubgroup_index_eq_of_ringEquiv`). -/
theorem shrink_algebraMap_compat_apply (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Small.{0} K] [Small.{0} L] (x : K) :
    algebraMap (Shrink K) (Shrink L) ((Shrink.ringEquiv K).symm x) =
      (Shrink.ringEquiv L).symm (algebraMap K L x) := by
  rw [show algebraMap (Shrink K) (Shrink L) ((Shrink.ringEquiv K).symm x) =
      (Shrink.ringEquiv L).symm
        (algebraMap K L ((Shrink.ringEquiv K) ((Shrink.ringEquiv K).symm x)))
      from rfl]
  simp

/-- The compatibility of the algebra maps, as an identity of ring homomorphisms. -/
theorem shrink_hc (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    (algebraMap (Shrink K) (Shrink L)).comp ((Shrink.ringEquiv K).symm : K →+* Shrink K) =
      (((Shrink.ringEquiv L).symm : L →+* Shrink L)).comp (algebraMap K L) := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  exact shrink_algebraMap_compat K L x

/-- `Shrink` preserves characteristic zero. -/
instance shrink_charZero (K : Type u) [Field K] [CharZero K] [Small.{0} K] :
    CharZero (Shrink.{0} K) := by
  refine charZero_of_inj_zero (fun n hn => ?_)
  have h2 : (equivShrink K).symm ((n : Shrink.{0} K)) = (n : K) := by
    rw [show (n : Shrink.{0} K) = (equivShrink K) (n : K) from rfl]
    exact Equiv.symm_apply_apply _ _
  have h3 : (equivShrink K).symm (0 : Shrink.{0} K) = (0 : K) := by
    rw [show (0 : Shrink.{0} K) = (equivShrink K) (0 : K) from rfl]
    exact Equiv.symm_apply_apply _ _
  have h4 := congrArg (fun z => (equivShrink K).symm z) hn
  rw [h2, h3] at h4
  exact CharZero.cast_injective (R := K) (by simpa using h4)

/-- `Shrink` preserves finite-dimensionality over `ℚ`. -/
instance shrink_finiteDimensional_rat (K : Type u) [Field K] [NumberField K] [Small.{0} K] :
    FiniteDimensional ℚ (Shrink.{0} K) :=
  LinearEquiv.finiteDimensional (Shrink.linearEquiv ℚ K).symm

/-- `Shrink` preserves the property of being a number field. -/
instance shrink_numberField (K : Type u) [Field K] [NumberField K] [Small.{0} K] :
    NumberField (Shrink.{0} K) where
  to_charZero := shrink_charZero K
  to_finiteDimensional := shrink_finiteDimensional_rat K

/-- **Shrinking preserves finite-dimensionality of the extension.**  The finite generating set of
`L` over `K` is carried to `Shrink L` over `Shrink K` by the two ring equivalences. -/
instance shrink_finiteDimensional (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Small.{0} K] [Small.{0} L] :
    FiniteDimensional (Shrink K) (Shrink L) :=
  Module.Finite.of_equiv_equiv (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrink_hc K L)

/-- **Shrinking preserves the Galois property of the extension.** -/
instance shrink_isGalois (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [Small.{0} K] [Small.{0} L] : IsGalois (Shrink K) (Shrink L) :=
  IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv K).symm) (g := (Shrink.ringEquiv L).symm)
    (shrink_hc K L)

/-- **`MapsBase` for the shrink ring equivalence**: the inverse of `Shrink.ringEquiv L` maps the
image of `K` in `L` onto the image of `Shrink K` in `Shrink L`.  This is the hypothesis of the
conjugation isomorphism `Submission.NeukirchUchida.conjHomEquiv`, which identifies the Galois
groups of the two extensions. -/
theorem shrink_mapsBase (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    Submission.NeukirchUchida.MapsBase (algebraMap (Shrink K) (Shrink L)) (algebraMap K L)
      ((Shrink.ringEquiv L).symm : L ≃+* Shrink L) := by
  rw [Submission.NeukirchUchida.MapsBase]
  ext x
  simp only [Subring.mem_map, RingHom.mem_range]
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, hxy⟩
    exact ⟨(Shrink.ringEquiv K).symm.toRingHom a,
      by rw [shrink_algebraMap_compat]; exact hxy⟩
  · rintro ⟨r, hr⟩
    exact ⟨algebraMap K L ((Shrink.ringEquiv K).toRingHom r), ⟨_, rfl⟩, hr⟩

/-- **Shrinking preserves cyclicity of the Galois group.**  The two Galois groups are identified by
conjugation with the shrink ring equivalence (`shrink_mapsBase` and
`Submission.NeukirchUchida.conjHomEquiv`). -/
instance shrink_isCyclic (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] [IsCyclic (L ≃ₐ[K] L)] :
    IsCyclic ((Shrink L) ≃ₐ[Shrink K] (Shrink L)) :=
  ((Submission.NeukirchUchida.conjHomEquiv (shrink_mapsBase K L)).isCyclic).mpr inferInstance

/-- **The degree is invariant under shrinking.** -/
theorem shrink_finrank_eq (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    Module.finrank K L = Module.finrank (Shrink K) (Shrink L) :=
  Algebra.finrank_eq_of_equiv_equiv (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrink_hc K L)

end

end HasseIndex

open HasseIndex

/-- **Index form of Hasse's norm theorem.**  For cyclic `L/K` of number fields, in an arbitrary
universe, the index of the norm class subgroup is the degree: `[C_K : N_{L/K}C_L] = [L : K]`.

At universe zero the statement is `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`; the general
case follows by pure transport, with no new arithmetic: a number field in a higher universe is
countable, hence equivalent to a universe-zero model (Mathlib's `Shrink`, the field, number-field,
algebra and finiteness structures being transported along the equivalence, via
`Function.Injective.field` and friends), and the norm index is invariant under ring equivalences of
extensions — `NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv`, delegated separately,
which is stated with polymorphic type binders precisely so that it can compare a number field with
its universe-zero model.  The degree is invariant on the nose.

This is the index half of `NK.HasseTwist.Sha2Input.hasse_norm`, whose type is the Hasse norm
result at an arbitrary universe; the norm half is analogous. -/
theorem hasseNorm_index_eq_universe {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index = Module.finrank K L := by
  -- A number field is countable, so it has a model in `Type 0`.
  haveI hK : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  haveI hL : Countable L := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := L)
  haveI hsK : Small.{0} K := Countable.toSmall K
  haveI hsL : Small.{0} L := Countable.toSmall L
  -- The universe-zero statement, at the `Shrink` models.
  have h1 := index_eq_finrank_of_isCyclic (K := Shrink.{0} K) (L := Shrink.{0} L)
  -- Invariance of the norm index under the ring equivalences of the extensions.
  have h2 := normClassSubgroup_index_eq_of_ringEquiv (K := K) (L := L) (K' := Shrink.{0} K)
    (L' := Shrink.{0} L) ((Shrink.ringEquiv K).symm) ((Shrink.ringEquiv L).symm)
    (fun x => (HasseIndex.shrink_algebraMap_compat_apply K L x).symm)
  -- Invariance of the degree.
  have h3 := HasseIndex.shrink_finrank_eq K L
  rw [h2, h1, ← h3]

end NK.GlobalCFTdeep
