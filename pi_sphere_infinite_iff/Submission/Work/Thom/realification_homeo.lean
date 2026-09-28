import Mathlib
import Submission.Work.Thom.realification
import Submission.Work.Thom.IsoPunct

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The total spaces of a complex bundle and of its realification agree topologically
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {ι : Type}

/-- The underlying functions of the preferred trivialisations of a complex bundle and of its
realification agree. -/
theorem localTriv_realification_coe (Z : VectorBundleCore ℂ B F ι) (i : ι) :
    ⇑(Z.localTriv i) = ⇑((realification Z).localTriv i) := by
  funext p
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply,
    realification_indexAt, realification_coordChange]

/-- The identity is continuous from a complex bundle's total space to its realification. -/
theorem continuous_id_realification (Z : VectorBundleCore ℂ B F ι) :
    @Continuous Z.TotalSpace (realification Z).TotalSpace _ _ id := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := Z.indexAt p.1 with hi
  have hp : p ∈ (Z.localTriv i).source :=
    (VectorBundleCore.mem_localTriv_source Z i p).mpr (Z.mem_baseSet_at p.1)
  refine (((realification Z).localTriv i).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    ?_).2 ?_
  · rw [Set.preimage_id]
    have hsrc : ((realification Z).localTriv i).source = (Z.localTriv i).source := by
      ext q
      rw [VectorBundleCore.mem_localTriv_source, VectorBundleCore.mem_localTriv_source,
        realification_baseSet]
    rw [hsrc]
    exact (Z.localTriv i).open_source.mem_nhds hp
  · have hcomp : ⇑((realification Z).localTriv i) ∘ id = ⇑(Z.localTriv i) := by
      funext q
      simp only [Function.comp_apply, id_eq]
      exact (congrFun (localTriv_realification_coe Z i) q).symm
    rw [show (↑((realification Z).localTriv i).toOpenPartialHomeomorph : Z.TotalSpace → B × F)
        = ⇑((realification Z).localTriv i) from rfl, hcomp]
    exact (Z.localTriv i).continuousOn.continuousAt ((Z.localTriv i).open_source.mem_nhds hp)

/-- The identity is continuous from a realification's total space to the complex bundle's. -/
theorem continuous_id_realification_symm (Z : VectorBundleCore ℂ B F ι) :
    @Continuous (realification Z).TotalSpace Z.TotalSpace _ _ id := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := Z.indexAt p.1 with hi
  have hp : p ∈ ((realification Z).localTriv i).source := by
    rw [VectorBundleCore.mem_localTriv_source]
    rw [realification_baseSet]
    exact Z.mem_baseSet_at p.1
  refine ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    ?_).2 ?_
  · rw [Set.preimage_id]
    have hsrc : (Z.localTriv i).source = ((realification Z).localTriv i).source := by
      ext q
      rw [VectorBundleCore.mem_localTriv_source, VectorBundleCore.mem_localTriv_source,
        realification_baseSet]
    rw [hsrc]
    exact ((realification Z).localTriv i).open_source.mem_nhds hp
  · have hcomp : ⇑(Z.localTriv i) ∘ id = ⇑((realification Z).localTriv i) := by
      funext q
      simp only [Function.comp_apply, id_eq]
      exact congrFun (localTriv_realification_coe Z i) q
    rw [show (↑(Z.localTriv i).toOpenPartialHomeomorph : (realification Z).TotalSpace → B × F)
        = ⇑(Z.localTriv i) from rfl, hcomp]
    exact ((realification Z).localTriv i).continuousOn.continuousAt
      (((realification Z).localTriv i).open_source.mem_nhds hp)

/-- **The total space of a complex bundle and that of its realification are the same topological
space** (via the identity). -/
def realificationHomeomorph (Z : VectorBundleCore ℂ B F ι) :
    Z.TotalSpace ≃ₜ (realification Z).TotalSpace where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id_realification Z
  continuous_invFun := continuous_id_realification_symm Z

/-- The punctured total spaces: the realification changes nothing. -/
noncomputable def zeroComplementHomeomorph (Z : VectorBundleCore ℂ B F ι) :
    ↥(zeroComplement (realification Z)) ≃ₜ ↥(zeroComplementCore Z) where
  toFun p := ⟨(p : (realification Z).TotalSpace), p.2⟩
  invFun p := ⟨(p : Z.TotalSpace), p.2⟩
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := ((continuous_id_realification_symm Z).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_id_realification Z).comp continuous_subtype_val).subtype_mk _

/-- The punctured total spaces of two isomorphic complex bundles are homeomorphic (via the
induced map, transported across the realification). -/
noncomputable def punctHomeo {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (e : BundleIso Z Z') :
    ↥(zeroComplement (realification Z)) ≃ₜ ↥(zeroComplement (realification Z')) :=
  (zeroComplementHomeomorph Z).trans
    (e.punctHomeomorph.trans (zeroComplementHomeomorph Z').symm)

/-- `Work.Thom.punctHomeo` fixes the base point. -/
theorem punctHomeo_proj {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (e : BundleIso Z Z') (p : ↥(zeroComplement (realification Z))) :
    ((punctHomeo Z Z' e p : ↥(zeroComplement (realification Z'))) :
      (realification Z').TotalSpace).1 = (p : (realification Z).TotalSpace).1 := by
  show (e.punctHomeomorph (zeroComplementHomeomorph Z p) : Z'.TotalSpace).1
    = ((p : (realification Z).TotalSpace) : Z.TotalSpace).1
  rw [BundleIso.punctHomeomorph_apply, BundleIso.punctMap_apply]
  rfl

end

end Work.Thom
