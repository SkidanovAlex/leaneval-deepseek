import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Submission.NK.GlobalCFT.Idele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Idèles which are local units outside a finite set

For a number field `K` and an open subgroup `U` of the idèle group `𝕀 K`, there is a finite set
`F` of places such that every idèle which is a local unit at every place outside `F` and is `1`
at every place in `F` already lies in `U`.

This is the standard "the all-units piece `∏_v 𝒪_v^×` of the restricted product carries the
product topology" computation: `∏_v 𝒪_v^×` embeds into `𝕀 K` as an open subset
(`RestrictedProduct.isOpenEmbedding_structureMap`), hence `U` pulls back to a neighbourhood of
`1` in the product `∏_v 𝒪_v^×`, and in a product a neighbourhood of `1` contains a box which is
unconstrained outside a finite set of coordinates (`isOpen_pi_iff`).

The result is used to reduce statements about *arbitrary* open subgroups of `𝕀 K` (e.g. kernels
of continuous characters, or norm groups) to *finitely supported* conditions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct Topology
open Filter

noncomputable section

namespace NK.NUV2.ArtinBridge

/-- **The unit idèles of `K`**: the "all local units" piece `∏_v 𝒪_v^×` of the restricted
product, i.e. the structure map `RestrictedProduct.structureMap` of `𝕀 K`. -/
def unitIdelesFun (K : Type) [Field K] [NumberField K] :
    ((v : NK.GlobalCFT.Place K) → ↥(NK.GlobalCFT.Place.localUnits K v)) →
      NK.GlobalCFT.Idele K :=
  fun a => ⟨fun v => (a v : (NK.GlobalCFT.Place.localField K v)ˣ),
    Filter.Eventually.of_forall fun v => (a v).2⟩

@[simp] theorem unitIdelesFun_apply {K : Type} [Field K] [NumberField K]
    (a : (v : NK.GlobalCFT.Place K) → ↥(NK.GlobalCFT.Place.localUnits K v))
    (v : NK.GlobalCFT.Place K) : unitIdelesFun K a v = a v := rfl

theorem unitIdelesFun_one (K : Type) [Field K] [NumberField K] :
    unitIdelesFun K 1 = 1 := by
  refine NK.GlobalCFT.Idele.ext fun v => ?_
  rfl

/-- **A neighbourhood of `1` in `𝕀 K` is a neighbourhood of the unit idèles** in the product
`∏_v 𝒪_v^×`: the map `∏_v 𝒪_v^× → 𝕀 K` is a homeomorphism onto an open subset
(`RestrictedProduct.nhds_eq_map_structureMap`). -/
theorem nhds_one_eq_map_unitIdelesFun (K : Type) [Field K] [NumberField K] :
    𝓝 (1 : NK.GlobalCFT.Idele K) = Filter.map (unitIdelesFun K)
      (𝓝 (1 : (v : NK.GlobalCFT.Place K) → ↥(NK.GlobalCFT.Place.localUnits K v))) := by
  have h := RestrictedProduct.nhds_eq_map_structureMap
    (R := fun v : NK.GlobalCFT.Place K => (NK.GlobalCFT.Place.localField K v)ˣ)
    (A := fun v => (NK.GlobalCFT.Place.localUnits K v : Set _))
    (fun v => NK.GlobalCFT.Place.isOpen_localUnits v)
    (1 : (v : NK.GlobalCFT.Place K) → ↥(NK.GlobalCFT.Place.localUnits K v))
  rw [← unitIdelesFun_one K]
  exact h

theorem exists_finset_forall_localUnits_imp_mem {K : Type} [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : IsOpen (U : Set (NK.GlobalCFT.Idele K))) :
    ∃ F : Finset (NK.GlobalCFT.Place K), ∀ x : NK.GlobalCFT.Idele K,
      (∀ v : NK.GlobalCFT.Place K, v ∉ F → x v ∈ NK.GlobalCFT.Place.localUnits K v) →
      (∀ v ∈ F, x v = 1) → x ∈ U := by
  classical
  -- The preimage of `U` under the unit idèles map is open in the product `∏_v 𝒪_v^×`.
  have hopen : IsOpen (unitIdelesFun K ⁻¹' (U : Set (NK.GlobalCFT.Idele K))) := by
    have hcont : Continuous (unitIdelesFun K) := by
      rw [show unitIdelesFun K = RestrictedProduct.structureMap
          (fun v : NK.GlobalCFT.Place K => (NK.GlobalCFT.Place.localField K v)ˣ)
          (fun v => (NK.GlobalCFT.Place.localUnits K v : Set _)) Filter.cofinite from rfl]
      exact RestrictedProduct.isEmbedding_structureMap.continuous
    exact hU.preimage hcont
  have hone : (1 : (v : NK.GlobalCFT.Place K) → ↥(NK.GlobalCFT.Place.localUnits K v)) ∈
      unitIdelesFun K ⁻¹' (U : Set (NK.GlobalCFT.Idele K)) := by
    rw [Set.mem_preimage, unitIdelesFun_one]
    exact U.one_mem
  -- Extract a finite box around `1` inside that preimage.
  obtain ⟨F, u, hu, hbox⟩ := isOpen_pi_iff.mp hopen
    (1 : (v : NK.GlobalCFT.Place K) → ↥(NK.GlobalCFT.Place.localUnits K v)) hone
  refine ⟨F, fun x hxout hxin => ?_⟩
  have hxmem : ∀ v : NK.GlobalCFT.Place K, x v ∈ NK.GlobalCFT.Place.localUnits K v := by
    intro v
    by_cases hv : v ∈ F
    · rw [hxin v hv]
      exact Subgroup.one_mem _
    · exact hxout v hv
  let f : (v : NK.GlobalCFT.Place K) → ↥(NK.GlobalCFT.Place.localUnits K v) :=
    fun v => ⟨x v, hxmem v⟩
  have hf_id : unitIdelesFun K f = x := by
    refine NK.GlobalCFT.Idele.ext fun v => ?_
    rfl
  have hfbox : f ∈ (F : Set (NK.GlobalCFT.Place K)).pi u := by
    rw [Set.mem_pi]
    intro v hv
    have h1v : (1 : (v : NK.GlobalCFT.Place K) →
        ↥(NK.GlobalCFT.Place.localUnits K v)) v ∈ u v := (hu v hv).2
    have hfv : f v = 1 := Subtype.ext (by simp [f, hxin v hv])
    simpa [hfv] using h1v
  have hfU : f ∈ unitIdelesFun K ⁻¹' (U : Set (NK.GlobalCFT.Idele K)) := hbox hfbox
  rw [Set.mem_preimage, hf_id] at hfU
  exact hfU

end NK.NUV2.ArtinBridge
