import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The fibre projections of a Whitney sum are continuous on the total spaces

The Whitney sum `Work.Whitney.whitneySum Z₁ Z₂` of two complex gluing-data bundles lives over the
product cover `ι₁ × ι₂`, in the standard fibre `ℂ^{m₁+m₂}`; its fibre is the direct sum of the two
fibres of `Z₁` and `Z₂`, split by the explicit continuous linear equivalence
`Work.Whitney.sumFibreC m₁ m₂`.  The two projections of this splitting give the two maps

* `p ↦ ⟨p.1, ((sumFibreC m₁ m₂).symm p.2).1⟩` into `Z₁.TotalSpace`,
* `p ↦ ⟨p.1, ((sumFibreC m₁ m₂).symm p.2).2⟩` into `Z₂.TotalSpace`,

and the main theorem `Work.Whitney.continuous_tcmProj` states that both are continuous, on the
total spaces of the *realifications* (which is the form in which the Whitney formula
`c(E ⊕ F) = c(E)c(F)` for `Work.Thom.chernClass` consumes them: the Chern recursion is applied to
the realifications).

The proof is the standard local-trivialisation computation.  The technical heart is the
fibre-coordinate formula `Work.Whitney.localTriv_whitneySum_fst` (and its second-factor analogue):
in the preferred trivialisation of the target, the map simply reads off the corresponding component
of the source's trivialisation coordinates.  Continuity then follows by composing the (continuous)
source trivialisation with the (continuous) linear projection `ℂ^{m₁+m₂} → ℂ^{m₁}`, and descending
across the realification identifications `Work.Thom.continuous_id_realification`.

The `set v : ℂ^{m₁+m₂} := p.2` step in the coordinate lemmas is not cosmetic: it types the fibre
coordinate as the model fibre, so that the subsequent `simp` sees a well-typed term (the fibre
`(whitneySum Z₁ Z₂).Fiber b` is only *definitionally* the model fibre).
-/

namespace Work.Whitney

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}

/-! ## The fibre coordinates of the first projection -/

/-- **The fibre-coordinate formula for the first projection of the Whitney sum.**  For every
trivialisation index `i` of the sum, the target trivialisation of `Z₁` at `i.1` reads the first
projection as the first component of the source trivialisation. -/
theorem localTriv_whitneySum_fst
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (i : ι₁ × ι₂) (p : (whitneySum Z₁ Z₂).TotalSpace) :
    (Z₁.localTriv i.1) (⟨p.1, ((sumFibreC m₁ m₂).symm p.2).1⟩ : Z₁.TotalSpace)
      = (p.1, ((sumFibreC m₁ m₂).symm (((whitneySum Z₁ Z₂).localTriv i p).2)).1) := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  set v : EuclideanSpace ℂ (Fin (m₁ + m₂)) := p.2 with hv
  simp only [whitneySum_coordChange, whitneySum_indexAt]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  simp

/-- **The fibre-coordinate formula for the second projection of the Whitney sum.** -/
theorem localTriv_whitneySum_snd
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (i : ι₁ × ι₂) (p : (whitneySum Z₁ Z₂).TotalSpace) :
    (Z₂.localTriv i.2) (⟨p.1, ((sumFibreC m₁ m₂).symm p.2).2⟩ : Z₂.TotalSpace)
      = (p.1, ((sumFibreC m₁ m₂).symm (((whitneySum Z₁ Z₂).localTriv i p).2)).2) := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  set v : EuclideanSpace ℂ (Fin (m₁ + m₂)) := p.2 with hv
  simp only [whitneySum_coordChange, whitneySum_indexAt]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  simp

/-! ## Continuity of the two projections -/

/-- **The first projection of the Whitney sum is continuous on the total spaces.** -/
theorem continuous_whitneySum_fst
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Continuous (fun p : (whitneySum Z₁ Z₂).TotalSpace =>
      (⟨p.1, ((sumFibreC m₁ m₂).symm p.2).1⟩ : Z₁.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := (whitneySum Z₁ Z₂).indexAt p.1 with hi
  have hp : p ∈ ((whitneySum Z₁ Z₂).localTriv i).source :=
    (VectorBundleCore.mem_localTriv_source _ i p).mpr ((whitneySum Z₁ Z₂).mem_baseSet_at p.1)
  refine (((Z₁.localTriv i.1).toOpenPartialHomeomorph).continuousAt_iff_continuousAt_comp_left
    ?_).2 ?_
  · refine Filter.mem_of_superset (((whitneySum Z₁ Z₂).localTriv i).open_source.mem_nhds hp) ?_
    intro q hq
    have hq' : q.1 ∈ Z₁.baseSet i.1 := by
      rw [VectorBundleCore.mem_localTriv_source, whitneySum_baseSet] at hq
      exact hq.1
    simpa only [Set.mem_preimage, VectorBundleCore.mem_localTriv_source] using hq'
  · have hcomp : ⇑(Z₁.localTriv i.1) ∘ (fun q : (whitneySum Z₁ Z₂).TotalSpace =>
          (⟨q.1, ((sumFibreC m₁ m₂).symm q.2).1⟩ : Z₁.TotalSpace))
        = (fun r : B × EuclideanSpace ℂ (Fin (m₁ + m₂)) =>
            (r.1, ((sumFibreC m₁ m₂).symm r.2).1)) ∘ ⇑((whitneySum Z₁ Z₂).localTriv i) := by
      funext q
      show (Z₁.localTriv i.1) (⟨q.1, ((sumFibreC m₁ m₂).symm q.2).1⟩ : Z₁.TotalSpace)
        = (fun r : B × EuclideanSpace ℂ (Fin (m₁ + m₂)) =>
            (r.1, ((sumFibreC m₁ m₂).symm r.2).1)) ((whitneySum Z₁ Z₂).localTriv i q)
      rw [localTriv_whitneySum_fst, VectorBundleCore.localTriv_apply]
    rw [show (↑((Z₁.localTriv i.1).toOpenPartialHomeomorph) :
        Z₁.TotalSpace → B × EuclideanSpace ℂ (Fin m₁)) = ⇑(Z₁.localTriv i.1) from rfl, hcomp]
    exact ((continuous_fst.prodMk ((continuous_fst.comp (sumFibreC m₁ m₂).symm.continuous).comp
        continuous_snd)).continuousAt).comp
      (((whitneySum Z₁ Z₂).localTriv i).continuousOn.continuousAt
        (((whitneySum Z₁ Z₂).localTriv i).open_source.mem_nhds hp))

/-- **The second projection of the Whitney sum is continuous on the total spaces.** -/
theorem continuous_whitneySum_snd
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Continuous (fun p : (whitneySum Z₁ Z₂).TotalSpace =>
      (⟨p.1, ((sumFibreC m₁ m₂).symm p.2).2⟩ : Z₂.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := (whitneySum Z₁ Z₂).indexAt p.1 with hi
  have hp : p ∈ ((whitneySum Z₁ Z₂).localTriv i).source :=
    (VectorBundleCore.mem_localTriv_source _ i p).mpr ((whitneySum Z₁ Z₂).mem_baseSet_at p.1)
  refine (((Z₂.localTriv i.2).toOpenPartialHomeomorph).continuousAt_iff_continuousAt_comp_left
    ?_).2 ?_
  · refine Filter.mem_of_superset (((whitneySum Z₁ Z₂).localTriv i).open_source.mem_nhds hp) ?_
    intro q hq
    have hq' : q.1 ∈ Z₂.baseSet i.2 := by
      rw [VectorBundleCore.mem_localTriv_source, whitneySum_baseSet] at hq
      exact hq.2
    simpa only [Set.mem_preimage, VectorBundleCore.mem_localTriv_source] using hq'
  · have hcomp : ⇑(Z₂.localTriv i.2) ∘ (fun q : (whitneySum Z₁ Z₂).TotalSpace =>
          (⟨q.1, ((sumFibreC m₁ m₂).symm q.2).2⟩ : Z₂.TotalSpace))
        = (fun r : B × EuclideanSpace ℂ (Fin (m₁ + m₂)) =>
            (r.1, ((sumFibreC m₁ m₂).symm r.2).2)) ∘ ⇑((whitneySum Z₁ Z₂).localTriv i) := by
      funext q
      show (Z₂.localTriv i.2) (⟨q.1, ((sumFibreC m₁ m₂).symm q.2).2⟩ : Z₂.TotalSpace)
        = (fun r : B × EuclideanSpace ℂ (Fin (m₁ + m₂)) =>
            (r.1, ((sumFibreC m₁ m₂).symm r.2).2)) ((whitneySum Z₁ Z₂).localTriv i q)
      rw [localTriv_whitneySum_snd, VectorBundleCore.localTriv_apply]
    rw [show (↑((Z₂.localTriv i.2).toOpenPartialHomeomorph) :
        Z₂.TotalSpace → B × EuclideanSpace ℂ (Fin m₂)) = ⇑(Z₂.localTriv i.2) from rfl, hcomp]
    exact ((continuous_fst.prodMk ((continuous_snd.comp (sumFibreC m₁ m₂).symm.continuous).comp
        continuous_snd)).continuousAt).comp
      (((whitneySum Z₁ Z₂).localTriv i).continuousOn.continuousAt
        (((whitneySum Z₁ Z₂).localTriv i).open_source.mem_nhds hp))

/-! ## The same statements on the realifications -/

/-- **The first projection of the Whitney sum is continuous, on the realifications.** -/
theorem continuous_realification_whitneySum_fst
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Continuous (fun p : (Work.Thom.realification (whitneySum Z₁ Z₂)).TotalSpace =>
      (⟨p.1, ((sumFibreC m₁ m₂).symm p.2).1⟩ : (Work.Thom.realification Z₁).TotalSpace)) := by
  have h := (Work.Thom.continuous_id_realification Z₁).comp
    ((continuous_whitneySum_fst Z₁ Z₂).comp
      (Work.Thom.continuous_id_realification_symm (whitneySum Z₁ Z₂)))
  exact h

/-- **The second projection of the Whitney sum is continuous, on the realifications.** -/
theorem continuous_realification_whitneySum_snd
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Continuous (fun p : (Work.Thom.realification (whitneySum Z₁ Z₂)).TotalSpace =>
      (⟨p.1, ((sumFibreC m₁ m₂).symm p.2).2⟩ : (Work.Thom.realification Z₂).TotalSpace)) := by
  have h := (Work.Thom.continuous_id_realification Z₂).comp
    ((continuous_whitneySum_snd Z₁ Z₂).comp
      (Work.Thom.continuous_id_realification_symm (whitneySum Z₁ Z₂)))
  exact h

/-! ## The statement requested by the Whitney formula -/

theorem continuous_tcmProj {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Continuous (fun p : (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace =>
      (⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩ :
        (Work.Thom.realification Z₁).TotalSpace))
    ∧ Continuous (fun p : (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace =>
      (⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩ :
        (Work.Thom.realification Z₂).TotalSpace)) :=
  ⟨continuous_realification_whitneySum_fst Z₁ Z₂,
    continuous_realification_whitneySum_snd Z₁ Z₂⟩

end

end Work.Whitney
