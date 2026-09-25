import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.NUV2.ArtinBridge.normClassSubgroup_isOpen_aux
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormFinite_range
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range

/-!
# The norm subgroup of the idèle class group is open

For a finite extension `L / K` of number fields the norm subgroup
`N_{L/K} C_L = (N_{L/K} 𝕀 L) · Kˣ ⧸ Kˣ` of the idèle class group `C_K = 𝕀 K ⧸ Kˣ` is **open**.

The proof is class-field-theory-free:

* the general part (a subgroup of `𝕀 K` containing an open subgroup is open; an open subgroup of
  `𝕀 K` contained in `N_{L/K} 𝕀 L` makes `N_{L/K}C_L` open) is in
  `Submission.NK.NUV2.ArtinBridge.normClassSubgroup_isOpen_aux`;
* the local inputs used for the Galois case are `exists_isOpen_subgroup_le_localNormFinite_range`
  and `exists_isOpen_subgroup_le_localNormInfinite_range`, together with
  `localUnits_le_image_localNormFinite_of_unramified` (the local norm is onto on units at an
  unramified place);
* for a general finite `L / K` one applies the Galois case to the normal closure `M / K` of `L / K`
  and uses `N_{M/K} C_M ≤ N_{L/K} C_L` (`Idele.normClassSubgroup_le_of_tower`): a subgroup
  containing an open subgroup is open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-- **The Galois case.**  For a finite Galois extension `L / K` of number fields the norm
subgroup `N_{L/K} C_L` is open in `C_K`. -/
theorem isOpen_normClassSubgroup_of_isGalois {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsOpen (Idele.normClassSubgroup K L : Set (IdeleClassGroup K)) := by
  obtain ⟨S, hSinf, hunr⟩ := exists_finset_places_good (K := K) (L := L)
  choose g hg using fun v => exists_place_liesOver (K := K) (L := L) v
  -- The local data: at every place the local norm homomorphism, an open subgroup of its range
  -- inside `S`, and surjectivity on local units outside `S`.
  have hdata : ∀ v : Place K, ∃ Φ : (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ,
      (∀ u : (Place.localField L (g v))ˣ,
        Idele.normIdeleFun K L (singleIdeleL (g v) u) v = Φ u) ∧
      (v ∈ S → ∃ A : Subgroup ((Place.localField K v)ˣ),
        IsOpen (A : Set ((Place.localField K v)ˣ)) ∧ A ≤ Φ.range) ∧
      (v ∉ S → ∀ a ∈ Place.localUnits K v,
        ∃ u ∈ Place.localUnits L (g v), Φ u = a) := by
    intro v
    rcases hg v with ⟨w, v', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
    · obtain rfl := h2
      haveI : w.LiesOver v' := h3
      rw [h1]
      exact ⟨Place.localNormInfinite w v',
        fun u => normIdeleFun_singleIdeleL_ofInfinite w v' u,
        fun _ => exists_isOpen_subgroup_le_localNormInfinite_range w v',
        fun hvS => absurd (hSinf v') hvS⟩
    · obtain rfl := h2
      rw [h1]
      exact ⟨Place.localNormFinite q Q h3,
        fun u => normIdeleFun_singleIdeleL_ofFinite q Q h3 u,
        fun _ => exists_isOpen_subgroup_le_localNormFinite_range q Q h3,
        fun hvS a ha =>
          localUnits_le_image_localNormFinite_of_unramified q Q h3
            (hunr q Q h3 hvS) a ha⟩
  choose Φ hbridge hSdata hUdata using hdata
  let A : (v : S) → Subgroup ((Place.localField K v)ˣ) := fun v => Classical.choose (hSdata v.1 v.2)
  exact isOpen_normClassSubgroup_of_localData S A g hg Φ hbridge
    (fun v => (Classical.choose_spec (hSdata v.1 v.2)).1)
    (fun v => (Classical.choose_spec (hSdata v.1 v.2)).2)
    (fun v hvS a ha => hUdata v hvS a ha)

/-- **The norm subgroup of the idèle class group is open** (Neukirch–Uchida, preliminary).

For a finite extension `L / K` of number fields, `N_{L/K} C_L` is an open subgroup of `C_K`. -/
theorem isOpen_normClassSubgroup {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    IsOpen (NK.GlobalCFT.Idele.normClassSubgroup K L :
      Set (NK.GlobalCFT.IdeleClassGroup K)) := by
  -- the normal closure of `L` over `K`
  let Ω := AlgebraicClosure L
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  haveI hnormal : Normal K Ω :=
    { toIsAlgebraic := inferInstance, splits' := fun x => IsAlgClosed.splits _ }
  haveI hsep : Algebra.IsSeparable K Ω := Algebra.IsSeparable.of_integral K Ω
  haveI hgalΩ : IsGalois K Ω := isGalois_iff.mpr ⟨hsep, hnormal⟩
  haveI hfdK : FiniteDimensional K M := normalClosure.is_finiteDimensional K L Ω
  haveI hgal : IsGalois K M := IsGalois.normalClosure K L Ω
  haveI hfdL : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  haveI hst : IsScalarTower ℚ K M := inferInstance
  haveI hnfM : NumberField M :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans K M }
  -- the Galois case for `M / K`
  have hgalopen : IsOpen (Idele.normClassSubgroup K M : Set (IdeleClassGroup K)) :=
    isOpen_normClassSubgroup_of_isGalois (K := K) (L := M)
  -- `N_{M/K} C_M ≤ N_{L/K} C_L`, and a subgroup containing an open subgroup is open
  have hle : Idele.normClassSubgroup K M ≤ Idele.normClassSubgroup K L :=
    Idele.normClassSubgroup_le_of_tower (K := K) (L := L) (M := M)
  exact Subgroup.isOpen_mono hle hgalopen

end NK.NUV2.ArtinBridge
