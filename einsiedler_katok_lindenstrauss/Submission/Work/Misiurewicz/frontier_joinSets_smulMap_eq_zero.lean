import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.Misiurewicz.frontier_finite_subset
import Submission.Work.Misiurewicz.vMove_lt_iff

/-!
# Null frontier is preserved by the joins `⋁_{k<M} (g^k)^{-1} P`

`x ↦ g • x` is a homeomorphism of `X₃ = SL₃(ℝ)/SL₃(ℤ)` (`Homeomorph.smul`), and
`smulMap g = ⇑(Homeomorph.smul g)` by definition.  Hence for every `k`

`frontier ((smulMap g)^[k] ⁻¹' A) = (smulMap g)^[k] ⁻¹' frontier A`,

and if `ν` is `smulMap g`-invariant then `ν ((smulMap g)^[k] ⁻¹' B) = 0` as soon as `ν B = 0`
(`MeasurePreserving.preimage_null`).  Since the frontier of a finite intersection is contained in
the union of the frontiers (`frontier_iInter_subset`), every member of the join
`joinSets (smulMap g) P M w = ⋂_{k<M} (smulMap g)^[k] ⁻¹' P.parts (w k)` has frontier of measure
`≤ ∑_{k<M} ν (frontier (P.parts (w k))) = 0`.
-/

namespace Work.Misiurewicz

open Work.EKLContract Work.EKLComp MeasureTheory

/-- The frontier of a pullback along the homeomorphism `x ↦ g • x` is the pullback of the
frontier. -/
theorem frontier_iterate_smulMap_preimage (g : SL3) (k : ℕ) (A : Set X3) :
    frontier ((smulMap g)^[k] ⁻¹' A) = (smulMap g)^[k] ⁻¹' frontier A := by
  rw [smulMap_iterate]
  exact (Homeomorph.preimage_frontier (Homeomorph.smul (α := X3) (g ^ k)) A).symm

theorem frontier_joinSets_smulMap_eq_zero (ν : MeasureTheory.Measure Work.EKLContract.X3)
    (g : Work.EKLContract.SL3)
    (hνinv : MeasureTheory.MeasurePreserving (Work.EKLComp.smulMap g) ν ν)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3)
    (hP : ∀ i, ν (frontier (P.parts i)) = 0) :
    ∀ (M : ℕ) (w : Fin M → Fin P.n), ν (frontier (Work.EKLContract.joinSets (Work.EKLComp.smulMap g) P M w)) = 0 := by
  intro M w
  -- every member of the join has null frontier
  have hmember : ∀ k : Fin M, ν ((smulMap g)^[(k : ℕ)] ⁻¹' frontier (P.parts (w k))) = 0 :=
    fun k => (hνinv.iterate (k : ℕ)).preimage_null (hP (w k))
  -- the frontier of the join lies in the union of the frontiers of its members
  have hsubset : frontier (joinSets (smulMap g) P M w) ⊆
      ⋃ k : Fin M, (smulMap g)^[(k : ℕ)] ⁻¹' frontier (P.parts (w k)) := by
    have h1 : frontier (joinSets (smulMap g) P M w) ⊆
        ⋃ k : Fin M, frontier ((smulMap g)^[(k : ℕ)] ⁻¹' P.parts (w k)) :=
      frontier_iInter_subset (fun k : Fin M => (smulMap g)^[(k : ℕ)] ⁻¹' P.parts (w k))
    refine h1.trans (Set.iUnion_mono fun k => ?_)
    exact le_of_eq (frontier_iterate_smulMap_preimage g (k : ℕ) (P.parts (w k)))
  have hzero : ν (⋃ k : Fin M, (smulMap g)^[(k : ℕ)] ⁻¹' frontier (P.parts (w k))) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ν (⋃ k : Fin M, (smulMap g)^[(k : ℕ)] ⁻¹' frontier (P.parts (w k)))
        ≤ ∑ k : Fin M, ν ((smulMap g)^[(k : ℕ)] ⁻¹' frontier (P.parts (w k))) :=
          measure_iUnion_fintype_le ν _
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          exact hmember k
  exact measure_mono_null hsubset hzero

end Work.Misiurewicz
