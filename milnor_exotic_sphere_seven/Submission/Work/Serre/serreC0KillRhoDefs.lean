import Mathlib
import Submission.Work.Serre.serreC0KillHomologySets
import Submission.Work.Serre.CellStep.compressRel_cellU

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `serreC0KillRho`: the vocabulary

For `n : ℕ`, a space `Y`, an index type `ι` and attaching maps `f : ι → C(S^{n+1}, Y)`, the space
`X = KillX f = attachCells n Y ι f` is `Y` with `(n+2)`-cells glued on, and we consider the open
cover `KillU ∪ KillV` with `KillZ = KillU ∩ KillV` (the union of the shells `1/4 < ‖x‖ < 1/2` of
the attached cells).

This module fixes the two maps whose existence and properties give `Work.Serre.serreC0KillRho`:

* `killZShellMap f : (Σ i, {1/4 < ‖x‖ < 1/2}) → ↥(KillZ f)`, `(i,x) ↦ cellMap i x` — the
  parametrisation of the shell region (a homeomorphism onto `KillZ f`);
* `killUPushFun f : ↥(KillU f) → ↥(KillA f)` — the radial push of every punctured cell of `KillU`
  onto its boundary sphere, i.e. the retraction of `KillU f` onto the range of `attachIncl`, which
  on a shell point `cellMap i x` is exactly `attachIncl (f i (x / ‖x‖))`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-! ### The parametrisation of `KillZ` by the model shells -/

/-- A point of `KillZ f` produced by a point of a model shell: `(i, x) ↦ cellMap i x`. -/
def killZShellPt (f : ι → C(cellSphere n, Y)) (i : ι)
    (x : ↥(cellShellSet n (1 / 4) (1 / 2))) : ↥(KillZ f) :=
  ⟨cellMap n Y ι f i (x : cellDisk n), by
    rw [KillZ_eq_iUnion_KillQ]
    exact Set.mem_iUnion.mpr
      ⟨i, (mem_KillQ f i _).mpr ⟨(x : cellDisk n), x.2.1, x.2.2, rfl⟩⟩⟩

@[simp] theorem killZShellPt_coe (f : ι → C(cellSphere n, Y)) (i : ι)
    (x : ↥(cellShellSet n (1 / 4) (1 / 2))) :
    ((killZShellPt f i x : ↥(KillZ f)) : KillX f) = cellMap n Y ι f i (x : cellDisk n) := rfl

/-- **The parametrisation of the shell region**: the disjoint union of the model shells maps to
`KillZ f` by `(i,x) ↦ cellMap i x`.  This is the inverse of the homeomorphism whose existence is
`Work.Serre.serreC0KillRho`. -/
noncomputable def killZShellMap (f : ι → C(cellSphere n, Y)) :
    C(Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2)), ↥(KillZ f)) where
  toFun p := killZShellPt f p.1 p.2
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact Continuous.subtype_mk
      ((cellMap n Y ι f i).continuous.comp continuous_subtype_val)
      (fun x => (killZShellPt f i x).2)

@[simp] theorem killZShellMap_apply (f : ι → C(cellSphere n, Y))
    (p : Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2))) :
    ((killZShellMap f p : ↥(KillZ f)) : KillX f) = cellMap n Y ι f p.1 (p.2 : cellDisk n) := rfl

/-! ### The saturated preimage of `KillU` and the radial push -/

/-- The saturated preimage of `KillU f` in the disjoint union `Y ⊕ (ι × D^{n+2})`. -/
abbrev KillUpre (f : ι → C(cellSphere n, Y)) : Set (Y ⊕ (Σ _ : ι, cellDisk n)) :=
  (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))) ⁻¹' KillU f

/-- Every cell centre lies in the union of the images of the closed balls of radius `1/4`. -/
theorem cellOrigin_mem_cellBallImg (f : ι → C(cellSphere n, Y)) (i : ι) :
    cellOrigin n Y ι f i ∈ cellBallImg f (1 / 4) :=
  (mem_cellBallImg f).mpr ⟨i, cellDiskCentre n, by simp, rfl⟩

/-- The saturated preimage of `KillU f` misses every cell centre, so the radial push is defined
on it. -/
theorem KillUpre_subset_pushDomain (f : ι → C(cellSphere n, Y)) :
    KillUpre f ⊆ pushDomain n Y ι f := by
  intro a ha
  rw [KillUpre, Set.mem_preimage] at ha
  rw [pushDomain, Set.mem_preimage, Set.mem_compl_iff]
  rintro ⟨i, hi⟩
  exact ha (hi.symm ▸ cellOrigin_mem_cellBallImg f i)

/-- The quotient map of the saturated preimage of `KillU f` onto `KillU f`. -/
noncomputable def killUQuot (f : ι → C(cellSphere n, Y)) : ↥(KillUpre f) → ↥(KillU f) :=
  (KillU f).restrictPreimage (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)))

theorem killUQuot_apply (f : ι → C(cellSphere n, Y)) (a : ↥(KillUpre f)) :
    ((killUQuot f a : ↥(KillU f)) : KillX f) =
      (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
        (a : Y ⊕ (Σ _ : ι, cellDisk n))) := rfl

/-- The quotient map of the saturated preimage of `KillU f` is a quotient map. -/
theorem killUQuot_isQuotientMap (f : ι → C(cellSphere n, Y)) :
    Topology.IsQuotientMap (killUQuot f) :=
  Topology.IsQuotientMap.restrictPreimage_isOpen
    (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)))
    (isOpen_KillU f)

theorem killUQuot_surjective (f : ι → C(cellSphere n, Y)) :
    Function.Surjective (killUQuot f) :=
  (killUQuot_isQuotientMap f).surjective

/-- The radial push of `KillU f`, as a function of the quotient, of the representative chosen by
`Classical.choose` and of the time.  Its continuity (`Continuous (killUPushRaw f)`, obtained by
descending `pushGarbage` through the quotient) is the point of the construction. -/
noncomputable def killUPushRaw (f : ι → C(cellSphere n, Y)) : ↥(KillU f) × I → ↥(KillU f) :=
  fun p => ⟨pushGarbage n Y ι f
      ((Classical.choose (killUQuot_surjective f p.1) : ↥(KillUpre f)) :
        Y ⊕ (Σ _ : ι, cellDisk n)) p.2,
    Work.Serre.CellStep.pushGarbage_mem_cellU f (by norm_num) (by norm_num)
      (Classical.choose (killUQuot_surjective f p.1)).2 p.2⟩

/-- **The retraction of `KillU f` onto `KillA f`**: the radial push of every punctured cell of
`KillU f` onto its boundary sphere, at time `1`. -/
noncomputable def killUPushFun (f : ι → C(cellSphere n, Y)) : ↥(KillU f) → ↥(KillA f) :=
  fun v => ⟨(killUPushRaw f (v, 1) : ↥(KillU f)), by
    show pushGarbage n Y ι f
        ((Classical.choose (killUQuot_surjective f v) : ↥(KillUpre f)) :
          Y ⊕ (Σ _ : ι, cellDisk n)) 1
      ∈ Set.range (attachIncl n Y ι f)
    exact pushGarbage_one_mem (KillUpre_subset_pushDomain f
      (Classical.choose (killUQuot_surjective f v)).2)⟩

@[simp] theorem killUPushFun_apply (f : ι → C(cellSphere n, Y)) (v : ↥(KillU f)) :
    ((killUPushFun f v : ↥(KillA f)) : KillX f) = pushGarbage n Y ι f
        ((Classical.choose (killUQuot_surjective f v) : ↥(KillUpre f)) :
          Y ⊕ (Σ _ : ι, cellDisk n)) 1 := rfl

end

end Work.Serre
