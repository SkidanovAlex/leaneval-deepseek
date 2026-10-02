import Mathlib
import Submission.Work.StemsB.Rat.CollarDefs
import Submission.Work.StemsB.Rat.CollarSqGeom
import Submission.Work.StemsB.Rat.CollarSqEmpty
import Submission.Work.StemsB.Rat.collarSuspClassAuxRat
import Submission.Work.StemsB.serreSphere_collar_les_degenerates
import Submission.Work.StemsB.Rat.CollarSplit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.StemsB.Rat

-- HINT. This is the ℚ-coefficient analogue of `Work.StemsB.collarSuspensionClass_sq`
-- (`Submission/Work/StemsB/collarSuspensionClass_sq.lean`), whose ℤ proof is a good template.
-- Over ℚ one shortcut exists: the Thom class is available directly from
-- `Work.StemsB.collarThomRat` (proved, in `Submission/Work/StemsB/collarThomRat.lean`), so the
-- ℤ-only construction `collarThom_delta_of` can be replaced.  The two cheap conjuncts come from
-- pulling back a class `gen` of the collar over `PUnit` along `Work.StemsB.collarDropSub`
-- (`cupH'` of the pullback is the pullback of `cupH'`, and `H^{2(b-1)}(sphLoopCollar b;ℚ) = 0`),
-- and `σ^* s = 0` from `collarDropSub ∘ collarSection = const`.  The hard conjunct is
-- `CollarThom τ` for `τ = δ s`; the ℤ argument (`collarThom_delta_of`) factors the Thom map as
-- `Φ_{τ₀} ∘ (x ↦ u ⌣ x)` with `u ∈ H⁰(Y;ℚ)`, and over ℚ the condition `u ⌣ u = 1` must be
-- replaced by "`u` is a unit" (all point evaluations nonzero), proved from the fibre computation
-- `h0Ev_y u * Φ₁(fibre_y τ₀) = Φ₁(fibre_y τ)` together with `fibre_y τ₀ ≠ 0`.
theorem collarSuspClass_sq_rat (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] :
    ∃ (s : (Work.Cohomology.singularCochainComplex ℚ
              (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))).homology (b - 1))
      (τ : Work.Thom.RelCoh ℚ b (↥(Work.StemsB.sphLoopBig b) × Y)
            (Work.StemsB.sphLoopCollarProd b Y)),
      Work.StemsB.Rat.CollarThom (Y := Y) b τ ∧
      Work.StemsB.Rat.CollarTransgresses (Y := Y) b (by omega) s τ ∧
      Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj
          (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))) (b - 1) (b - 1) s s = 0 ∧
      (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
          (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))
          (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0 := by
  classical
  by_cases hY : Nonempty Y
  · obtain ⟨y₀⟩ := hY
    obtain ⟨τ₀, hτ₀⟩ := exists_collarThom b (by omega) Y
    obtain ⟨eZ⟩ := nonempty_RelCoh_collar_pt_top b (by omega)
    let Φ₁ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit) ≃ₗ[ℚ] ℚ :=
      eZ.toLinearEquiv
    obtain ⟨gen, hgen⟩ := serreSphere_collar_delta_surjective (R := ℚ) (Y := PUnit) b (by omega) (b - 1)
      ((relDegEquiv (sphLoopCollarProd b PUnit) (by omega : b - 1 + 1 = b)).symm (Φ₁.symm 1))
    obtain ⟨τ, hτ, htr⟩ := collarThom_delta_of b hb Y y₀ Φ₁ gen hgen
    refine ⟨(Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen, τ, hτ, htr, ?_, ?_⟩
    · -- `s ⌣ s = 0`
      rw [show Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of ↥(sphLoopCollarProd b Y)))
            (b - 1) (b - 1) ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen)
            ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen)
          = (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ ((b - 1) + (b - 1))).hom
              (Work.Cohomology.cupH' ℚ
                (TopCat.toSSet.obj (TopCat.of ↥(sphLoopCollarProd b PUnit)))
                (b - 1) (b - 1) gen gen) from
        (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarDropSub (Y := Y) b))
          (b - 1) (b - 1) gen gen).symm]
      rw [show Work.Cohomology.cupH' ℚ
            (TopCat.toSSet.obj (TopCat.of ↥(sphLoopCollarProd b PUnit)))
            (b - 1) (b - 1) gen gen = 0 from
        @Subsingleton.elim _ (subsingleton_Coh_collar_pt_middle b hb) _ _]
      exact map_zero _
    · -- `σ^* s = 0`
      have hb1 : 1 ≤ b := by omega
      have hcomp : (collarDropSub (Y := Y) b).comp (collarSection (Y := Y) b hb1) =
          (⟨fun _ => (⟨(collarShellPt b hb1, PUnit.unit),
              sphShellPt_mem_sphLoopCollar b hb1⟩ : ↥(sphLoopCollarProd b PUnit)),
            continuous_const⟩ : C(PUnit, ↥(sphLoopCollarProd b PUnit))).comp
          (⟨fun _ => PUnit.unit, continuous_const⟩ : C(Y, PUnit)) := by
        apply ContinuousMap.ext
        intro y
        apply Subtype.ext
        apply Prod.ext <;> rfl
      haveI hpt : Subsingleton (Work.Thom.Coh ℚ (b - 1) PUnit) := by
        have h := Work.Cohomology.punit ℚ ((b - 1) - 1)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ b - 1)] at h
        exact ModuleCat.subsingleton_of_isZero h
      have hsplit := Work.Thom.CohMap_linear_comp
        (⟨fun _ => PUnit.unit, continuous_const⟩ : C(Y, PUnit))
        (⟨fun _ => (⟨(collarShellPt b hb1, PUnit.unit),
            sphShellPt_mem_sphLoopCollar b hb1⟩ : ↥(sphLoopCollarProd b PUnit)),
          continuous_const⟩ : C(PUnit, ↥(sphLoopCollarProd b PUnit))) ℚ (b - 1)
      have hval : (Work.Thom.CohMap
          (⟨fun _ => (⟨(collarShellPt b hb1, PUnit.unit),
              sphShellPt_mem_sphLoopCollar b hb1⟩ : ↥(sphLoopCollarProd b PUnit)),
            continuous_const⟩ : C(PUnit, ↥(sphLoopCollarProd b PUnit))) ℚ (b - 1)).hom gen = 0 :=
        @Subsingleton.elim _ hpt _ _
      have key : (Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (b - 1)).hom
          ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen) = 0 := by
        rw [show (Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (b - 1)).hom
              ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen)
            = ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (b - 1)).hom.comp
                (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom) gen from rfl]
        rw [Work.Thom.CohMap_linear_comp (collarSection (Y := Y) b hb1)
          (collarDropSub (Y := Y) b) ℚ (b - 1)]
        rw [CohMap_congr hcomp ℚ (b - 1)]
        rw [← hsplit]
        exact (congrArg (fun w => (Work.Thom.CohMap
            (⟨fun _ => PUnit.unit, continuous_const⟩ : C(Y, PUnit)) ℚ (b - 1)).hom w) hval).trans
          (map_zero _)
      exact key
  · -- empty base
    haveI hY' : IsEmpty Y := ⟨fun y => hY ⟨y⟩⟩
    haveI hYc : IsEmpty ↥(sphLoopCollarProd b Y) := ⟨fun z => hY ⟨z.1.2⟩⟩
    obtain ⟨s, τ, hτ, htr⟩ := collarSuspensionClass' b (by omega) Y
    exact ⟨s, τ, hτ, htr,
      @Subsingleton.elim _
        (subsingleton_Coh_of_isEmpty ↥(sphLoopCollarProd b Y) hYc ((b - 1) + (b - 1))) _ _,
      @Subsingleton.elim _ (subsingleton_Coh_of_isEmpty Y hY' (b - 1)) _ _⟩

end Work.StemsB.Rat
