import Mathlib
import Submission.Work.RatHurewicz.AttachPush.Defs
import Submission.Work.RatHurewicz.AttachPush.PushOffAux

/-!
# The image of a closed ball of radius `< 1` in an attached cell is closed

For the push-off step of `Work.RatHurewicz.compressRel_attachCells_range` one needs that the part of
an attached cell lying at distance `≤ ρ < 1` from its centre is a *closed* subset of the attachment
`attachCells n Y ι f`.  This module proves it.

The point is that the preimage of `cellMap i '' {y | ‖y‖ ≤ ρ}` under the quotient map
`Y ⊕ (Σ i, D^{n+2}) → attachCells n Y ι f` is *exactly* the part of the `i`-th summand over the
closed `ρ`-ball: since `ρ < 1` that ball lies in the open model cell, where classes are singletons
(`Work.RatHurewicz.eq_of_eqvGen_inr_cellInner`).  That part of the summand is closed, and the
quotient map is coinducing, so the image is closed.
-/

open scoped Topology

namespace Work.AttachPush

/-- For a **closed** subset `U` of the model cell, the part of the `i`-th summand lying over `U`
is closed in the disjoint union `Y ⊕ (Σ i, D^{n+2})`. -/
theorem isClosed_sigmaOver {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
    {i : ι} {U : Set (Work.RatHurewicz.cellDisk n)} (hU : IsClosed U) :
    IsClosed (Work.RatHurewicz.sigmaOver (Y := Y) (ι := ι) i U) := by
  rw [isClosed_sum_iff]
  constructor
  · rw [show Sum.inl ⁻¹'
        Work.RatHurewicz.sigmaOver (Y := Y) (ι := ι) i U = ∅ from by
      ext y
      simp only [Set.mem_preimage, Work.RatHurewicz.sigmaOver, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, -, h⟩
      exact absurd h Sum.inl_ne_inr]
    exact isClosed_empty
  · rw [isClosed_sigma_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      rw [show Sigma.mk j ⁻¹'
          (Sum.inr ⁻¹' Work.RatHurewicz.sigmaOver (Y := Y) (ι := ι) j U) = U from by
        ext x
        constructor
        · rintro ⟨x', hx', h⟩
          have h1 : (⟨j, x⟩ : Σ _ : ι, Work.RatHurewicz.cellDisk n) = ⟨j, x'⟩ :=
            Sum.inr.inj h
          have h2 : x = x' := by
            simpa using congrArg (fun p : Σ _ : ι, Work.RatHurewicz.cellDisk n => p.2) h1
          rw [h2]
          exact hx'
        · intro hx
          exact ⟨x, hx, rfl⟩]
      exact hU
    · rw [show Sigma.mk j ⁻¹'
          (Sum.inr ⁻¹' Work.RatHurewicz.sigmaOver (Y := Y) (ι := ι) i U) = ∅ from by
        ext x
        simp only [Set.mem_preimage, Work.RatHurewicz.sigmaOver, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨x', -, h⟩
        have h1 : (⟨j, x⟩ : Σ _ : ι, Work.RatHurewicz.cellDisk n) = ⟨i, x'⟩ :=
          Sum.inr.inj h
        exact hji (congrArg (fun p : Σ _ : ι, Work.RatHurewicz.cellDisk n => p.1) h1)]
      exact isClosed_empty

theorem isClosed_cellMap_image_closedBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) {ρ : ℝ} (hρ : ρ < 1) :
    IsClosed (Work.RatHurewicz.cellMap n Y ι f i ''
      {y : Work.RatHurewicz.cellDisk n | ‖(y : Work.RatHurewicz.CellVec n)‖ ≤ ρ}) := by
  classical
  set U : Set (Work.RatHurewicz.cellDisk n) :=
    {y | ‖(y : Work.RatHurewicz.CellVec n)‖ ≤ ρ} with hUdef
  have hUsub : U ⊆ Work.RatHurewicz.cellInner n := fun y hy => lt_of_le_of_lt hy hρ
  have hUcl : IsClosed U :=
    isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const
  have hpre := Work.RatHurewicz.preimage_cellMap_image (n := n) (Y := Y) (ι := ι) (f := f)
    (i := i) (U := U) hUsub
  have hScl : IsClosed (Work.RatHurewicz.sigmaOver (Y := Y) (ι := ι) i U) :=
    isClosed_sigmaOver hUcl
  refine ((isQuotientMap_quotient_mk'
    (X := Y ⊕ (Σ _ : ι, Work.RatHurewicz.cellDisk n))
    (s := Relation.EqvGen.setoid (Work.RatHurewicz.attachRel n Y ι f))).isCoinducing.isClosed_preimage
    (s := {z : Work.RatHurewicz.attachCells n Y ι f |
      ∃ x ∈ U, Work.RatHurewicz.cellMap n Y ι f i x = z})).mp ?_
  rw [hpre]
  exact hScl

end Work.AttachPush
