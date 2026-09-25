import Mathlib
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx

/-!
# The relative different is trivial, transported along a base ring equivalence

Let `F` and `F'` be number fields embedded in a common number field `L`, and suppose that a
ring isomorphism `e : F ≃+* F'` identifies the two embeddings:

`algebraMap F' L (e x) = algebraMap F L x` for all `x : F`.

Then the two embeddings have the same image in `L`, hence the same image on the rings of
integers.  Since being unramified at a prime of `𝓞 L` only depends on the image of the base
ring inside `𝓞 L`, the relative different `differentIdeal (𝓞 F) (𝓞 L)` is the unit ideal if
and only if `differentIdeal (𝓞 F') (𝓞 L)` is.

The proof reduces `differentIdeal = ⊤` to the vanishing of all ramification indices
(`Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx`, resp. its
converse direction through
`Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal`), and then
transports the ramification index of a prime `Q` of `𝓞 L` across the isomorphism
`RingOfIntegers.mapRingEquiv e : 𝓞 F ≃+* 𝓞 F'` of the base rings.  For the transport one only
needs that the two base rings have the same image in `𝓞 L`: writing `ψ` for that ring
equivalence, `(Q.under (𝓞 F)).map ψ = Q.under (𝓞 F')`, whence the two ideals
`(Q.under ·).map (algebraMap · (Localization.AtPrime Q))` of the local ring at `Q` coincide
and so do the lengths defining `Ideal.ramificationIdx`.
-/

set_option linter.style.haveILetI false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- The composite `𝓞 F → 𝓞 F' → 𝓞 L` is `𝓞 F → 𝓞 L` when `e : F ≃+* F'` identifies the two
embeddings of `F` and `F'` into `L`. -/
private lemma algebraMap_comp_mapRingEquiv {F F' L : Type*} [Field F] [Field F'] [Field L]
    [Algebra F L] [Algebra F' L] (e : F ≃+* F')
    (hcomp : ∀ x : F, algebraMap F' L (e x) = algebraMap F L x) :
    (algebraMap (𝓞 F') (𝓞 L)).comp (NumberField.RingOfIntegers.mapRingEquiv e : 𝓞 F →+* 𝓞 F')
      = algebraMap (𝓞 F) (𝓞 L) := by
  ext x
  change ((NumberField.RingOfIntegers.mapRingHom (algebraMap F' L))
      (NumberField.RingOfIntegers.mapRingEquiv e x) : L) = _
  rw [NumberField.RingOfIntegers.mapRingHom_apply]
  change algebraMap F' L (e (x : F)) = algebraMap F L (x : F)
  rw [hcomp x]

/-- **The ramification index only depends on the image of the base ring.**

If `e : F ≃+* F'` identifies the embeddings of `F` and `F'` into `L`, then a prime `Q` of
`𝓞 L` has the same ramification index over `𝓞 F` and over `𝓞 F'`. -/
private theorem ramificationIdx_eq_of_ringEquiv {F F' L : Type*} [Field F] [NumberField F]
    [Field F'] [NumberField F'] [Field L] [NumberField L] [Algebra F L] [Algebra F' L]
    (e : F ≃+* F')
    (hcomp : ∀ x : F, algebraMap F' L (e x) = algebraMap F L x)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    Q.ramificationIdx (𝓞 F) = Q.ramificationIdx (𝓞 F') := by
  let ψ : 𝓞 F ≃+* 𝓞 F' := NumberField.RingOfIntegers.mapRingEquiv e
  have hφ : (algebraMap (𝓞 F') (𝓞 L)).comp (ψ : 𝓞 F →+* 𝓞 F') = algebraMap (𝓞 F) (𝓞 L) :=
    algebraMap_comp_mapRingEquiv e hcomp
  -- The images of the two rings of integers in `𝓞 L` agree: `Q.under (𝓞 F)` maps to
  -- `Q.under (𝓞 F')` under `ψ`.
  have hunder : (Q.under (𝓞 F)).map (ψ : 𝓞 F →+* 𝓞 F') = Q.under (𝓞 F') := by
    have h1 : Q.under (𝓞 F) = (Q.under (𝓞 F')).comap (ψ : 𝓞 F →+* 𝓞 F') := by
      rw [Ideal.under_def, Ideal.under_def, Ideal.comap_comap, ← hφ]
    rw [h1, Ideal.map_comap_of_surjective (ψ : 𝓞 F →+* 𝓞 F') ψ.surjective]
  -- hence the two preimages of `Q` in `𝓞 L` agree
  have hJ : (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 L))
      = (Q.under (𝓞 F')).map (algebraMap (𝓞 F') (𝓞 L)) := by
    rw [← hφ, ← Ideal.map_map, hunder]
  -- and so the two ideals of `Localization.AtPrime Q` defining the ramification index agree
  have hI : (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (Localization.AtPrime Q))
      = (Q.under (𝓞 F')).map (algebraMap (𝓞 F') (Localization.AtPrime Q)) := by
    rw [IsScalarTower.algebraMap_eq (𝓞 F) (𝓞 L) (Localization.AtPrime Q),
        IsScalarTower.algebraMap_eq (𝓞 F') (𝓞 L) (Localization.AtPrime Q),
        ← Ideal.map_map, ← Ideal.map_map, hJ]
  rw [Ideal.ramificationIdx_def (q := Q) (R := 𝓞 F),
      Ideal.ramificationIdx_def (q := Q) (R := 𝓞 F'), hI]

theorem differentIdeal_eq_top_of_base_ringEquiv {F F' L : Type*} [Field F] [NumberField F]
    [Field F'] [NumberField F'] [Field L] [NumberField L] [Algebra F L] [Algebra F' L]
    (e : F ≃+* F') (hcomp : ∀ x : F, algebraMap F' L (e x) = algebraMap F L x)
    (h : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) = ⊤) :
    differentIdeal (NumberField.RingOfIntegers F') (NumberField.RingOfIntegers L) = ⊤ := by
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd
    (E := F') (K := L) ?_
  intro Q hQ
  haveI : Q.IsPrime := hQ
  -- `Q` has ramification index `1` over `𝓞 F`, because the relative different of `L/F` is `⊤`
  have hQram : Q.ramificationIdx (𝓞 F) = 1 :=
    (Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := F) (K := L) Q hQ).mp (by
        rw [h]
        intro hcon
        exact hQ.ne_top (le_antisymm le_top (Ideal.dvd_iff_le.mp hcon)))
  -- and the ramification index of `Q` does not change when the base ring is identified with `𝓞 F'`
  have htrans : Q.ramificationIdx (𝓞 F) = Q.ramificationIdx (𝓞 F') :=
    ramificationIdx_eq_of_ringEquiv e hcomp Q
  rw [Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := F') (K := L) Q hQ, ← htrans]
  exact hQram

end Work.ClassFieldTower
