import Mathlib
import Submission.Work.Whitney.ConjDefs
import Submission.Work.Thom.realification
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The total space of `Z` and of its conjugate `Z̄`

The conjugate bundle `Work.Whitney.conjCore Z` has the same model fibre as `Z` and the same cover
and index map, so the *underlying set* of its total space is the same sigma type; the two bundle
structures differ by the fibrewise complex conjugation.  The natural identification of the total
spaces is therefore **not** the identity but the conjugation map on the fibre,

  `Φ p = ⟨p.1, conjC p.2⟩`,

which is a homeomorphism (its own inverse, since conjugation is an involution) and restricts to the
complements of the zero section.  This module proves that; the fibre-coordinate formula

  `((conjCore Z).localTriv i) (Φ p) = (p.1, conjC (((Z.localTriv i) p).2))`

is the technical heart (it is what makes `Φ` continuous, and later what identifies the tautological
quotients of `Z` and of `Z̄`).
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-! ## The core-level conjugation map -/

/-- **The conjugation map of total spaces** `Z.TotalSpace → (conjCore Z).TotalSpace`, fibrewise
`conjC`.  It is its own inverse. -/
def conjTotalSpace {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Z.TotalSpace → (conjCore Z).TotalSpace :=
  fun p => ⟨p.1, conjC m p.2⟩

@[simp] theorem conjTotalSpace_apply {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (p : Z.TotalSpace) :
    conjTotalSpace Z p = ⟨p.1, conjC m p.2⟩ := rfl

/-- **The fibre-coordinate formula for the conjugation map** in the preferred trivialisation. -/
theorem localTriv_conjCore_conjTotalSpace {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι) (p : Z.TotalSpace) :
    ((conjCore Z).localTriv i) (conjTotalSpace Z p)
      = (p.1, conjC m (((Z.localTriv i) p).2)) := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  simp only [conjTotalSpace_apply, conjCore_indexAt, conjCore_coordChange, conjCLM_apply]
  rw [conjC_involutive]

/-- **The conjugation map of total spaces is continuous.** -/
theorem continuous_conjTotalSpace {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) : Continuous (conjTotalSpace Z) := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := Z.indexAt p.1 with hi
  have hp : p ∈ (Z.localTriv i).source :=
    (VectorBundleCore.mem_localTriv_source Z i p).mpr (Z.mem_baseSet_at p.1)
  refine (((conjCore Z).localTriv i).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    ?_).2 ?_
  · have hsrc : (conjTotalSpace Z) ⁻¹' ((conjCore Z).localTriv i).source = (Z.localTriv i).source := by
      ext q
      rw [Set.mem_preimage, VectorBundleCore.mem_localTriv_source,
        VectorBundleCore.mem_localTriv_source, conjCore_baseSet]
      rfl
    rw [hsrc]
    exact (Z.localTriv i).open_source.mem_nhds hp
  · have hcomp : ⇑((conjCore Z).localTriv i) ∘ conjTotalSpace Z
        = (fun r : B × EuclideanSpace ℂ (Fin m) => (r.1, conjC m r.2)) ∘ ⇑(Z.localTriv i) := by
      funext q
      rw [Function.comp_apply, Function.comp_apply, localTriv_conjCore_conjTotalSpace,
        VectorBundleCore.localTriv_apply]
    rw [show (↑((conjCore Z).localTriv i).toOpenPartialHomeomorph :
        (conjCore Z).TotalSpace → B × EuclideanSpace ℂ (Fin m))
        = ⇑((conjCore Z).localTriv i) from rfl, hcomp]
    exact (continuous_fst.prodMk ((continuous_conjC m).comp continuous_snd)).continuousAt.comp
      ((Z.localTriv i).continuousOn.continuousAt ((Z.localTriv i).open_source.mem_nhds hp))

/-- **The inverse of the conjugation map of total spaces is continuous.** -/
theorem continuous_conjTotalSpace_symm {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Continuous (fun p : (conjCore Z).TotalSpace => (⟨p.1, conjC m p.2⟩ : Z.TotalSpace)) := by
  have h := continuous_conjTotalSpace (conjCore Z)
  rw [conjCore_conjCore] at h
  exact h

/-- **The total spaces of `Z` and of `Z̄` are homeomorphic** by the conjugation map. -/
def conjHomeomorph {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Z.TotalSpace ≃ₜ (conjCore Z).TotalSpace where
  toFun := conjTotalSpace Z
  invFun := fun p => ⟨p.1, conjC m p.2⟩
  left_inv p := by
    rcases p with ⟨b, v⟩
    show (⟨b, conjC m (conjC m v)⟩ : (conjCore Z).TotalSpace) = ⟨b, v⟩
    rw [conjC_involutive]
  right_inv p := by
    rcases p with ⟨b, v⟩
    show (⟨b, conjC m (conjC m v)⟩ : Z.TotalSpace) = ⟨b, v⟩
    rw [conjC_involutive]
  continuous_toFun := continuous_conjTotalSpace Z
  continuous_invFun := continuous_conjTotalSpace_symm Z

/-! ## The realified total spaces -/

/-- **The conjugation map between the realified total spaces**. -/
def conjRealTotalSpace {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (realification Z).TotalSpace → (realification (conjCore Z)).TotalSpace :=
  fun p => ⟨p.1, conjC m p.2⟩

@[simp] theorem conjRealTotalSpace_apply {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : (realification Z).TotalSpace) :
    conjRealTotalSpace Z p = ⟨p.1, conjC m p.2⟩ := rfl

/-- The fibre-coordinate formula for the conjugation map of realified cores. -/
theorem localTriv_realification_conjRealTotalSpace {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (p : (realification Z).TotalSpace) :
    ((realification (conjCore Z)).localTriv i) (conjRealTotalSpace Z p)
      = (p.1, conjC m (((realification Z).localTriv i) p).2) := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply,
    realification_indexAt, realification_coordChange, realification_indexAt,
    realification_coordChange]
  simp only [conjRealTotalSpace_apply, conjCore_indexAt, conjCore_coordChange, conjCLM_apply]
  rw [conjC_involutive]

/-- **The conjugation map of realified total spaces is continuous.** -/
theorem continuous_conjRealTotalSpace {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Continuous (conjRealTotalSpace Z) := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := (realification Z).indexAt p.1 with hi
  have hp : p ∈ ((realification Z).localTriv i).source :=
    (VectorBundleCore.mem_localTriv_source _ i p).mpr ((realification Z).mem_baseSet_at p.1)
  refine ((((realification (conjCore Z)).localTriv i).toOpenPartialHomeomorph
    ).continuousAt_iff_continuousAt_comp_left ?_).2 ?_
  · have hsrc : (conjRealTotalSpace Z) ⁻¹'
        ((realification (conjCore Z)).localTriv i).source
        = ((realification Z).localTriv i).source := by
      ext q
      simp only [Set.mem_preimage, VectorBundleCore.mem_localTriv_source, realification_baseSet,
        conjCore_baseSet]
      rfl
    rw [hsrc]
    exact ((realification Z).localTriv i).open_source.mem_nhds hp
  · have hcomp : ⇑((realification (conjCore Z)).localTriv i) ∘ conjRealTotalSpace Z
        = (fun r : B × EuclideanSpace ℂ (Fin m) => (r.1, conjC m r.2))
          ∘ ⇑((realification Z).localTriv i) := by
      funext q
      rw [Function.comp_apply, Function.comp_apply, localTriv_realification_conjRealTotalSpace,
        VectorBundleCore.localTriv_apply]
    rw [show (↑((realification (conjCore Z)).localTriv i).toOpenPartialHomeomorph :
        (realification (conjCore Z)).TotalSpace → B × EuclideanSpace ℂ (Fin m))
        = ⇑((realification (conjCore Z)).localTriv i) from rfl, hcomp]
    exact (continuous_fst.prodMk ((continuous_conjC m).comp continuous_snd)).continuousAt.comp
      (((realification Z).localTriv i).continuousOn.continuousAt
        (((realification Z).localTriv i).open_source.mem_nhds hp))

/-- The inverse of `conjRealTotalSpace` is continuous. -/
theorem continuous_conjRealTotalSpace_symm {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Continuous (fun p : (realification (conjCore Z)).TotalSpace =>
      (⟨p.1, conjC m p.2⟩ : (realification Z).TotalSpace)) := by
  have h := continuous_conjRealTotalSpace (conjCore Z)
  rw [conjCore_conjCore] at h
  exact h

/-! ## The punctured total spaces -/

/-- Conjugation does not vanish. -/
theorem conjC_ne_zero_iff {m : ℕ} (v : EuclideanSpace ℂ (Fin m)) : conjC m v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro h hv
    exact h (by rw [hv, map_zero])
  · intro h hv
    refine h ?_
    rw [show v = conjC m (conjC m v) from (conjC_involutive m v).symm, hv, map_zero]

/-- **The conjugation map on the punctured total space**: a map `Z∖0 → Z̄∖0`. -/
def conjPunct {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ↥(zeroComplement (realification Z)) →
      ↥(zeroComplement (realification (conjCore Z))) :=
  fun p => ⟨conjRealTotalSpace Z (p : (realification Z).TotalSpace),
    (conjC_ne_zero_iff (m := m) p.1.2).mpr p.2⟩

@[simp] theorem conjPunct_coe {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    ((conjPunct Z p : ↥(zeroComplement (realification (conjCore Z)))) :
      (realification (conjCore Z)).TotalSpace)
      = conjRealTotalSpace Z (p : (realification Z).TotalSpace) := rfl

theorem continuous_conjPunct {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) : Continuous (conjPunct Z) :=
  Continuous.subtype_mk
    ((continuous_conjRealTotalSpace Z).comp continuous_subtype_val)
    (fun p => (conjC_ne_zero_iff (m := m) p.1.2).mpr p.2)

/-- **The conjugation map on the punctured total space, as a continuous map**
`Z∖0 → Z̄∖0`. -/
def conjPunctCM {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    C(↥(zeroComplement (realification Z)),
      ↥(zeroComplement (realification (conjCore Z)))) :=
  ⟨conjPunct Z, continuous_conjPunct Z⟩

@[simp] theorem conjPunctCM_apply {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    conjPunctCM Z p = conjPunct Z p := rfl

/-- The inverse of `conjPunct`. -/
def conjPunctInv {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ↥(zeroComplement (realification (conjCore Z))) →
      ↥(zeroComplement (realification Z)) :=
  fun p => ⟨(⟨p.1.1, conjC m p.1.2⟩ : (realification Z).TotalSpace),
    (conjC_ne_zero_iff (m := m) p.1.2).mpr p.2⟩

theorem continuous_conjPunctInv {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) : Continuous (conjPunctInv Z) :=
  Continuous.subtype_mk
    ((continuous_conjRealTotalSpace_symm Z).comp continuous_subtype_val)
    (fun p => (conjC_ne_zero_iff (m := m) p.1.2).mpr p.2)

/-- The inverse of `conjPunct` as a continuous map. -/
def conjPunctInvCM {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    C(↥(zeroComplement (realification (conjCore Z))),
      ↥(zeroComplement (realification Z))) :=
  ⟨conjPunctInv Z, continuous_conjPunctInv Z⟩

@[simp] theorem conjPunctInvCM_apply {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification (conjCore Z)))) :
    conjPunctInvCM Z p = conjPunctInv Z p := rfl

/-- The conjugation of the punctured total space is a homeomorphism. -/
def conjPunctHomeomorph {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ↥(zeroComplement (realification Z)) ≃ₜ
      ↥(zeroComplement (realification (conjCore Z))) where
  toFun := conjPunct Z
  invFun := conjPunctInv Z
  left_inv p := by
    rcases p with ⟨⟨b, v⟩, hv⟩
    refine Subtype.ext ?_
    show (⟨b, conjC m (conjC m v)⟩ : (realification Z).TotalSpace) = ⟨b, v⟩
    rw [conjC_involutive]
  right_inv p := by
    rcases p with ⟨⟨b, v⟩, hv⟩
    refine Subtype.ext ?_
    show (⟨b, conjC m (conjC m v)⟩ :
      (realification (conjCore Z)).TotalSpace) = ⟨b, v⟩
    rw [conjC_involutive]
  continuous_toFun := continuous_conjPunct Z
  continuous_invFun := continuous_conjPunctInv Z

end

end Work.Whitney
