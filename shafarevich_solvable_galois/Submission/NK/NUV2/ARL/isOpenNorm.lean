/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans
import Submission.NK.NUV2.ArtinBridge.normClassSubgroup_isOpen_aux
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormFinite_range
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range
import Submission.NK.GlobalCFTdeep.NormIndex.exists_good_S
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Openness of the idèlic norm subgroup `N_{L/K} 𝕀 L ≤ 𝕀 K`

For a finite extension `L / K` of number fields, the norm subgroup
`N_{L/K} 𝕀 L = NK.GlobalCFT.Idele.normImage K L` is an **open** subgroup of the idèle group
`𝕀 K`:

`NK.NUV2.ARL.isOpenNorm`.

## The mathematical argument

The classical proof (Neukirch, *Algebraic Number Theory*, V.1.6) runs over the places of `K`:

* choose a finite set `S` of places of `K` containing the archimedean places and all the places
  below a ramified prime (`NK.GlobalCFTdeep.NormIndex.exists_good_S`), and choose a place
  `g v` of `L` above every place `v` of `K` (`NK.GlobalCFTdeep.NormIndex.exists_place_liesOver`);
* at the places of `S` the local norm group `N_{L_{g v}/K_v} L_{g v}ˣ = (Φ v).range` contains an
  *open* subgroup of `K_vˣ`, i.e. the local norm is an open map
  (`NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormFinite_range`,
  `NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range`);
* outside `S` the extension is unramified and the local norm is *onto* on local units
  (`Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one`);
* consequently the idèles which satisfy the corresponding local conditions lie in `N 𝕀 L`
  (`NK.NUV2.ArtinBridge.constrainedLoc_le_normImage`), and since these local conditions
  describe an open subgroup (`NK.NUV2.ArtinBridge.isOpen_constrainedLoc`), `N 𝕀 L` is open.

The local inputs above are all available **for a finite Galois extension** `L / K`
(`isOpen_normImage_of_isGalois`).  The general (not necessarily Galois) case is reduced to the
Galois case with the **Galois closure**: if `M ⊇ L` is a finite Galois extension of `K`, then the
idèlic norm is transitive along the tower `K ⊆ L ⊆ M`
(`NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans`), so

`N_{M/K} 𝕀 M ⊆ N_{L/K} 𝕀 L`,

and a subgroup containing the open subgroup `N_{M/K} 𝕀 M` is itself open.  The Galois closure
`NK.GlobalCFTdeep.galoisClosure K L = normalClosure K L (AlgebraicClosure L)` (finite Galois
over `K`, and a number field) is provided by the existing development.

## Main results

* `NK.NUV2.ARL.isOpenNorm`;
* `NK.NUV2.ARL.isOpen_normImage_of_isGalois` (the Galois case);
* `NK.NUV2.ARL.exists_galoisClosure_normImage_le` (the Galois closure and the containment of
  the norm subgroups);
* `NK.NUV2.ARL.normImage_le_of_tower` (monotonicity of the norm subgroup along a tower).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ARL

open NK.GlobalCFT

/-- **Monotonicity of the idèlic norm subgroup along a tower.**  For a tower `K ⊆ L ⊆ M` of
number fields, every norm from `M` to `K` factors as a norm from `M` to `L` followed by a norm
from `L` to `K`, so `N_{M/K} 𝕀 M ≤ N_{L/K} 𝕀 L`. -/
theorem normImage_le_of_tower {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] :
    Idele.normImage K M ≤ Idele.normImage K L := by
  rw [Idele.normImage_eq_map, Idele.normImage_eq_map]
  rintro x ⟨y, rfl⟩
  refine ⟨Idele.normIdeleHom L M y, ?_⟩
  have h := NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans (K := K) (L := L) (M := M)
  simpa using congrFun (congrArg DFunLike.coe h) y

/-- **The idèlic norm subgroup is open for a finite Galois extension.**  This is the classical
per-place argument described in the module docstring. -/
theorem isOpen_normImage_of_isGalois {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsOpen (Idele.normImage K L : Set (Idele K)) := by
  classical
  obtain ⟨S, hSinf, hunr, -⟩ := NK.GlobalCFTdeep.NormIndex.exists_good_S (K := K) (L := L)
  choose g hg using fun v => NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := K) (L := L) v
  -- the local norm data at every place of `K`
  have hdata : ∀ v : Place K, ∃ Φ : (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ,
      (∀ u, Idele.normIdeleFun K L (NK.NUV2.ArtinBridge.singleIdeleL (g v) u) v = Φ u) ∧
      (∃ A : Subgroup ((Place.localField K v)ˣ), IsOpen (A : Set ((Place.localField K v)ˣ)) ∧
        A ≤ Φ.range) ∧
      (v ∉ S → ∀ a ∈ Place.localUnits K v,
        ∃ u ∈ Place.localUnits L (g v), Φ u = a) := by
    intro v
    rcases hg v with ⟨w, v', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
    · -- archimedean place
      obtain rfl := h2
      haveI : w.LiesOver v' := h3
      rw [h1]
      refine ⟨Place.localNormInfinite w v',
        fun u => NK.NUV2.ArtinBridge.normIdeleFun_singleIdeleL_ofInfinite w v' u, ?_, ?_⟩
      · exact NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range w v'
      · intro hvS _ _
        exact absurd (hSinf v') hvS
    · -- nonarchimedean place
      obtain rfl := h2
      rw [h1]
      refine ⟨Place.localNormFinite q Q h3,
        fun u => NK.NUV2.ArtinBridge.normIdeleFun_singleIdeleL_ofFinite q Q h3 u, ?_, ?_⟩
      · exact NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormFinite_range q Q h3
      · intro hQS a ha
        exact NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q q h3 (hunr q Q h3 hQS) a ha
  choose Φ hrest using hdata
  have hbridge : ∀ (v : Place K) (u : (Place.localField L (g v))ˣ),
      Idele.normIdeleFun K L (NK.NUV2.ArtinBridge.singleIdeleL (g v) u) v = Φ v u :=
    fun v => (hrest v).1
  have hrest2 : ∀ v : Place K, ∃ A : Subgroup ((Place.localField K v)ˣ),
      IsOpen (A : Set ((Place.localField K v)ˣ)) ∧ A ≤ (Φ v).range := fun v => (hrest v).2.1
  have hunit : ∀ v : Place K, v ∉ S → ∀ a ∈ Place.localUnits K v,
      ∃ u ∈ Place.localUnits L (g v), Φ v u = a := fun v => (hrest v).2.2
  choose A hA using hrest2
  -- the open subgroup of idèles satisfying the local conditions lies in the norm subgroup
  have hle := NK.NUV2.ArtinBridge.constrainedLoc_le_normImage S (fun v : ↥S => A ↑v) g hg Φ
      hbridge (fun v => (hA ↑v).2) (fun v hvS => hunit v hvS)
  have hop := NK.NUV2.ArtinBridge.isOpen_constrainedLoc S (fun v : ↥S => A ↑v)
      (fun v => (hA ↑v).1)
  exact Subgroup.isOpen_mono (H₁ := NK.NUV2.ArtinBridge.constrainedLoc S (fun v : ↥S => A ↑v))
    hle hop

/-- **The Galois closure reduces the general case to the Galois case.**  For a finite extension
`L / K` of number fields there is a number field `M` with `K ⊆ L ⊆ M`, `M / K` finite Galois, such
that `N_{M/K} 𝕀 M ≤ N_{L/K} 𝕀 L`; one takes for `M` the Galois closure
`NK.GlobalCFTdeep.galoisClosure K L = normalClosure K L (AlgebraicClosure L)` of `L / K`. -/
theorem exists_galoisClosure_normImage_le {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : FiniteDimensional K M)
      (_ : IsGalois K M),
      Idele.normImage K M ≤ Idele.normImage K L := by
  haveI : FiniteDimensional L (NK.GlobalCFTdeep.galoisClosure K L) :=
    Module.Finite.right K L _
  haveI : NumberField (NK.GlobalCFTdeep.galoisClosure K L) :=
    NumberField.of_module_finite K (NK.GlobalCFTdeep.galoisClosure K L)
  haveI : IsGalois K (NK.GlobalCFTdeep.galoisClosure K L) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  exact ⟨NK.GlobalCFTdeep.galoisClosure K L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, normImage_le_of_tower⟩

/-- **The norm subgroup `N_{L/K} 𝕀 L` of the idèles of `K` is open**, for any finite extension
`L / K` of number fields. -/
theorem isOpenNorm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    IsOpen (NK.GlobalCFT.Idele.normImage K L : Set (NK.GlobalCFT.Idele K)) := by
  -- pass to the Galois closure `M`
  obtain ⟨M, hFM, hNFM, hAKM, hFDKM, hGM, hle⟩ :=
    exists_galoisClosure_normImage_le (K := K) (L := L)
  letI := hFM
  letI := hNFM
  letI := hAKM
  letI := hFDKM
  letI := hGM
  have hopen : IsOpen (NK.GlobalCFT.Idele.normImage K M :
      Set (NK.GlobalCFT.Idele K)) := isOpen_normImage_of_isGalois
  exact Subgroup.isOpen_mono (H₁ := NK.GlobalCFT.Idele.normImage K M) hle hopen

end NK.NUV2.ARL
