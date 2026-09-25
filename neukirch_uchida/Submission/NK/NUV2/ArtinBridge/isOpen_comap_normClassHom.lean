import Mathlib
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.Norm.globalCFT_localNorm_mem_localUnits
import Submission.NK.NUV2.ArtinBridge.continuous_localNormFinite
import Submission.NK.NUV2.ArtinBridge.continuous_localNormInfinite

/-!
# The norm of idèle class groups pulls open subgroups back to open subgroups

For a finite extension `L / K` of number fields, the idèlic norm
`N_{L/K} : 𝕀 L →* 𝕀 K` and the induced norm `C_L →* C_K` on idèle class groups
(`NK.GlobalCFT.Idele.normIdeleHom`, `NK.GlobalCFT.IdeleClassGroup.normClassHom`) are
**continuous**.  Consequently the preimage of an open subgroup `N ≤ C_K` is an open subgroup of
`C_L`, which is the statement proved here:

`NK.NUV2.ArtinBridge.isOpen_comap_normClassHom`.

## The proof

Continuity of `normClassHom K L` follows from continuity of `normIdeleHom K L` because the
quotient map `𝕀 L → C_L` is a quotient map: it suffices that the composite
`C_L → C_K` with `mk L : 𝕀 L → C_L` is continuous, which is the continuity of
`mk K ∘ normIdeleHom K L`.

Continuity of the idèlic norm is the substantive part.  Writing `𝕀 L = Πʳ w, [L_wˣ, 𝒪_wˣ]` as a
restricted product, we show that a neighbourhood of `1` in `𝕀 K` pulls back to a neighbourhood of
`1` in `𝕀 L`:

* a neighbourhood of the unit-idèles `∏_v 𝒪_vˣ` (an open subgroup of `𝕀 K`) is a neighbourhood of
  `1` in `𝕀 K` (`RestrictedProduct.nhds_eq_map_structureMap`, since `∏_v 𝒪_vˣ` is the "all units"
  piece of the restricted product);
* the "unit idèles norm" `unitNormMap : ∏_w 𝒪_wˣ → ∏_v 𝒪_vˣ`, `a ↦ (v ↦ ∏_{w | v} N(a_w))`, is
  well defined (the norm of a local unit is a local unit) and continuous by the universal property
  of the product topology: each component is a finite product over the fibre of `v` of continuous
  local norms `N_{L_w/K_v}` (`continuous_localNormFinite`, `continuous_localNormInfinite`);
* finally `normIdeleHom` and `unitNormMap` are intertwined by the inclusions
  `∏_v 𝒪_vˣ ↪ 𝕀 K`, i.e. `normIdeleHom (unitIdeles a) = unitIdeles (unitNormMap a)`.

## Main statements

* `NK.NUV2.ArtinBridge.IsOpenComapNormClassHom.continuous_normIdeleHom`:
  `N_{L/K} : 𝕀 L →* 𝕀 K` is continuous;
* `NK.NUV2.ArtinBridge.IsOpenComapNormClassHom.continuous_normClassHom`:
  `N_{L/K} : C_L →* C_K` is continuous;
* `NK.NUV2.ArtinBridge.isOpen_comap_normClassHom`: the preimage of an open subgroup is open.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct Topology
open NumberField IsDedekindDomain
open Filter
open NK.GlobalCFT

namespace NK.NUV2.ArtinBridge

namespace IsOpenComapNormClassHom

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ### The unit idèles -/

/-- The group of unit idèles `∏_v 𝒪_vˣ` of `K`, as a subset of the idèle group `𝕀 K`
(an element is determined by its components, all of which are local units). -/
noncomputable def unitIdeles (K : Type) [Field K] [NumberField K] :
    ((v : Place K) → ↥(Place.localUnits K v)) → Idele K :=
  fun a => ⟨fun v => (a v : (Place.localField K v)ˣ),
    Filter.Eventually.of_forall fun v => (a v).2⟩

theorem unitIdeles_one_eq_one (K : Type) [Field K] [NumberField K] :
    unitIdeles K (1 : (v : Place K) → ↥(Place.localUnits K v)) = 1 := by
  refine Idele.ext fun v => ?_
  rfl

/-- **A neighbourhood of the identity in `𝕀 K` is a neighbourhood of the unit idèles**: the
"all units" piece `∏_v 𝒪_vˣ` of the restricted product carries the product topology, and
`structureMap` is a homeomorphism onto an open subset of `𝕀 K`
(`RestrictedProduct.nhds_eq_map_structureMap`). -/
theorem nhds_one_eq_map_unitIdeles (K : Type) [Field K] [NumberField K] :
    𝓝 (1 : Idele K) = Filter.map (unitIdeles K)
      (𝓝 (1 : (v : Place K) → ↥(Place.localUnits K v))) := by
  have h := RestrictedProduct.nhds_eq_map_structureMap
    (R := fun v : Place K => (Place.localField K v)ˣ)
    (A := fun v => (Place.localUnits K v : Set _))
    (fun v => Place.isOpen_localUnits v)
    (1 : (v : Place K) → ↥(Place.localUnits K v))
  rw [← unitIdeles_one_eq_one K]
  rw [show unitIdeles K = RestrictedProduct.structureMap
      (fun v : Place K => (Place.localField K v)ˣ)
      (fun v => (Place.localUnits K v : Set _)) Filter.cofinite from rfl]
  exact h

/-! ### The norm of a unit idèle is a unit idèle -/

/-- **The norm of an idèle which is a local unit everywhere is a local unit everywhere.**  Each
local norm `N_{L_w/K_v}` maps local units to local units
(`NK.GlobalCFT.Norm.globalCFT_localNorm_mem_localUnits`), and the component of the norm at `v`
is a finite product of such local norms over the places `w | v`. -/
theorem normIdeleFun_mem_localUnits (x : Idele L) (h : ∀ w : Place L, x w ∈ Place.localUnits L w)
    (v : Place K) :
    Idele.normIdeleFun K L x v ∈ Place.localUnits K v := by
  cases v with
  | inl w =>
    rw [Idele.normIdeleFun_ofInfinite, Place.localUnits_ofInfinite]
    exact Subgroup.mem_top _
  | inr Q =>
    rw [Idele.normIdeleFun_ofFinite, Place.localUnits_ofFinite]
    refine Subgroup.prod_mem _ ?_
    intro q' _
    exact Norm.globalCFT_localNorm_mem_localUnits q'.1 Q
      ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q'.1)).mp q'.2)
      (h (Place.ofFinite q'.1))

/-! ### The norm map on unit idèles -/

/-- The **norm map on unit idèles** `∏_w 𝒪_wˣ → ∏_v 𝒪_vˣ`, `a ↦ (v ↦ ∏_{w | v} N(a_w))`. -/
noncomputable def unitNormMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    ((w : Place L) → ↥(Place.localUnits L w)) → ((v : Place K) → ↥(Place.localUnits K v)) :=
  fun a v => ⟨Idele.normIdeleFun K L (unitIdeles L a) v,
    normIdeleFun_mem_localUnits (unitIdeles L a) (fun w => (a w).2) v⟩

theorem unitNormMap_one : unitNormMap K L 1 = 1 := by
  funext v
  refine Subtype.ext ?_
  have hone : unitIdeles L (1 : (w : Place L) → ↥(Place.localUnits L w)) = 1 :=
    unitIdeles_one_eq_one L
  show Idele.normIdeleFun K L (unitIdeles L 1) v = (1 : (Place.localField K v)ˣ)
  rw [hone, Norm.globalCFT_normIdeleFun_one]

/-- The unit-idèle norm is the idèlic norm on unit idèles. -/
theorem unitIdeles_unitNormMap (a : (w : Place L) → ↥(Place.localUnits L w)) :
    unitIdeles K (unitNormMap K L a) = Idele.normIdeleHom K L (unitIdeles L a) := by
  refine Idele.ext fun v => ?_
  rw [Idele.normIdeleHom_apply]
  rfl

/-! ### Continuity of the unit-idèle norm -/

/-- **The norm map on unit idèles is continuous.**  Under the product topology on both sides, each
component `a ↦ ∏_{w | v} N_{L_w/K_v}(a_w)` is a finite product of continuous local norms composed
with the (continuous) coordinate projections. -/
theorem continuous_unitNormMap_of_local
    (hfin : ∀ (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
      (h : q.asIdeal.LiesOver Q.asIdeal), Continuous (Place.localNormFinite q Q h))
    (hinf : ∀ (w : InfinitePlace L) (v : InfinitePlace K) [w.LiesOver v],
      Continuous (Place.localNormInfinite w v)) :
    Continuous (unitNormMap K L) := by
  rw [continuous_pi_iff]
  intro v
  cases v with
  | inl w =>
    refine Continuous.subtype_mk ?_ _
    simp only [Idele.normIdeleFun_ofInfinite]
    refine continuous_finsetProd _ ?_
    intro w' hw'
    exact (@hinf w'.1 w ((Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp
      w'.2)).comp (continuous_subtype_val.comp (continuous_apply (Place.ofInfinite w'.1)))
  | inr Q =>
    refine Continuous.subtype_mk ?_ _
    simp only [Idele.normIdeleFun_ofFinite]
    refine continuous_finsetProd _ ?_
    intro q' hq'
    exact (hfin q'.1 Q
        ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q'.1)).mp q'.2)).comp
      (continuous_subtype_val.comp (continuous_apply (Place.ofFinite q'.1)))

/-! ### Continuity of the idèlic norm -/

/-- **The idèlic norm `N_{L/K} : 𝕀 L →* 𝕀 K` is continuous.**

Given a neighbourhood `W` of `1` in `𝕀 K`, its preimage under the "unit idèle" map
`∏_v 𝒪_vˣ → 𝕀 K` is a neighbourhood of `1` in `∏_v 𝒪_vˣ`; by continuity of `unitNormMap` its
preimage under `unitNormMap` is a neighbourhood of `1` in `∏_w 𝒪_wˣ`; and this last set is exactly
the preimage of `W` under the composite `∏_w 𝒪_wˣ → 𝕀 L → 𝕀 K`.  Since `∏_w 𝒪_wˣ → 𝕀 L` is a
homeomorphism onto an open subset, this says that `N^{-1}(W)` is a neighbourhood of `1` in
`𝕀 L`. -/
theorem continuous_normIdeleHom_of_local
    (hfin : ∀ (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
      (h : q.asIdeal.LiesOver Q.asIdeal), Continuous (Place.localNormFinite q Q h))
    (hinf : ∀ (w : InfinitePlace L) (v : InfinitePlace K) [w.LiesOver v],
      Continuous (Place.localNormInfinite w v)) :
    Continuous (Idele.normIdeleHom K L) := by
  have hθ : Continuous (unitNormMap K L) := continuous_unitNormMap_of_local hfin hinf
  have hθ1 : unitNormMap K L 1 = 1 := unitNormMap_one
  refine continuous_of_continuousAt_one _ ?_
  intro W hW
  have hW1 : W ∈ 𝓝 (1 : Idele K) := by simpa only [map_one] using hW
  have hW' : unitIdeles K ⁻¹' W ∈ 𝓝 (1 : (v : Place K) → ↥(Place.localUnits K v)) := by
    rw [nhds_one_eq_map_unitIdeles K] at hW1
    exact Filter.mem_map.mp hW1
  have ht : Filter.Tendsto (unitNormMap K L)
      (𝓝 (1 : (w : Place L) → ↥(Place.localUnits L w)))
      (𝓝 (1 : (v : Place K) → ↥(Place.localUnits K v))) := by
    simpa only [hθ1] using hθ.tendsto (1 : (w : Place L) → ↥(Place.localUnits L w))
  have hmem : unitNormMap K L ⁻¹' (unitIdeles K ⁻¹' W) ∈
      𝓝 (1 : (w : Place L) → ↥(Place.localUnits L w)) := Filter.mem_map.mp (ht hW')
  have hset : unitIdeles L ⁻¹' (Idele.normIdeleHom K L ⁻¹' W) =
      unitNormMap K L ⁻¹' (unitIdeles K ⁻¹' W) := by
    ext a
    simp only [Set.mem_preimage]
    rw [unitIdeles_unitNormMap]
  have hmemL : unitIdeles L ⁻¹' (Idele.normIdeleHom K L ⁻¹' W) ∈
      𝓝 (1 : (w : Place L) → ↥(Place.localUnits L w)) := by
    refine Filter.mem_of_superset hmem ?_
    intro a ha
    rw [hset]
    exact ha
  rw [nhds_one_eq_map_unitIdeles L]
  exact Filter.mem_map.mpr hmemL

/-- **The unit-idèle norm is continuous**, unconditionally. -/
theorem continuous_unitNormMap : Continuous (unitNormMap K L) :=
  continuous_unitNormMap_of_local (fun q Q h => continuous_localNormFinite q Q h)
    (fun w v => continuous_localNormInfinite w v)

/-- **The idèlic norm is continuous**, unconditionally. -/
theorem continuous_normIdeleHom : Continuous (Idele.normIdeleHom K L) :=
  continuous_normIdeleHom_of_local (fun q Q h => continuous_localNormFinite q Q h)
    (fun w v => continuous_localNormInfinite w v)

/-! ### Continuity of the norm on idèle class groups -/

/-- **The norm `N_{L/K} : C_L →* C_K` on idèle class groups is continuous.**  The quotient map
`𝕀 L → C_L` is a quotient map, so it suffices that the composite `C_L → C_K` with it is
continuous; that composite is `mk K ∘ normIdeleHom K L`, which is continuous by
`continuous_normIdeleHom`. -/
theorem continuous_normClassHom : Continuous (IdeleClassGroup.normClassHom K L) := by
  have hcomp : Continuous ((IdeleClassGroup.normClassHom K L) ∘ IdeleClassGroup.mk L) := by
    rw [show (IdeleClassGroup.normClassHom K L) ∘ IdeleClassGroup.mk L =
        (IdeleClassGroup.mk K) ∘ (Idele.normIdeleHom K L) from
      funext fun x => IdeleClassGroup.normClassHom_mk x]
    exact (QuotientGroup.continuous_mk).comp continuous_normIdeleHom
  exact (continuous_coinduced_dom (f := IdeleClassGroup.mk L)
    (g := IdeleClassGroup.normClassHom K L) (t₁ := inferInstance)).mpr hcomp

end IsOpenComapNormClassHom

/-! ### The requested lemma -/

theorem isOpen_comap_normClassHom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (N : Subgroup (NK.GlobalCFT.IdeleClassGroup K))
    (hN : IsOpen (N : Set (NK.GlobalCFT.IdeleClassGroup K))) :
    IsOpen ((N.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K L) :
      Subgroup (NK.GlobalCFT.IdeleClassGroup L)) : Set (NK.GlobalCFT.IdeleClassGroup L)) := by
  have hcont : Continuous (NK.GlobalCFT.IdeleClassGroup.normClassHom K L) :=
    IsOpenComapNormClassHom.continuous_normClassHom (K := K) (L := L)
  rw [Subgroup.coe_comap]
  exact hN.preimage hcont

end NK.NUV2.ArtinBridge
