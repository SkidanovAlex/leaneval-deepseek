import Mathlib
import Submission.Work.Serre.discPairCellVanishing
import Submission.Work.Serre.DiscPair.discCellStep
import Submission.Work.Serre.attachRelCohVanishingHigh

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1000000

/-- One degree more of the vanishing of the new-cell groups: discPairCellVanishing with the bound j ≤ N + 1 widened to j ≤ N + 2 (needed by the five-step ladder of thomCylCellStepAlt). -/
theorem discPairCellVanishingSucc (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D) {Γ : Type}
    [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (j : ℕ) (hj : j ≤ N + 2) (hjr : j ≠ D + r + 1) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j (Work.Serre.cyl q)
      ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)
        ∪ Set.range (Work.Serre.cylIncl q))) := by
  classical
  -- it suffices to prove the vanishing of the relative *homology*
  refine Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH _ j ?_
  have hne : ∀ i : ι, Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)) :=
    fun i => (hpc _).nonempty
  by_cases hDj : D ≤ j
  · -- **above the cell dimension**: the cell step exhibits the group as a direct sum over the
    -- attached cells of the shifted reduced homology of the fibre, which is concentrated
    obtain ⟨e⟩ := Work.Serre.DiscPair.discCellStep D hD Γ ι f q hq hne j hDj
    refine IsZero.of_iso ?_ e
    refine Work.Serre.DiscPair.isZero_directSum (fun i => ?_)
    haveI hpcF : PathConnectedSpace
      (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)) := hpc _
    rcases Nat.eq_zero_or_pos (j - D) with h0 | hpos
    · rw [h0]
      exact Work.Serre.DiscPair.centreConePairZero D hD Γ ι f q hq hne i
    · -- the cone pair of a cell centre is the reduced homology of the fibre, shifted
      obtain ⟨e1⟩ := Work.Serre.DiscPair.centreConePair D Γ ι f q hq i
        (Classical.choice (hne i)) (j - D) (by omega)
      refine IsZero.of_iso ?_ e1
      rcases Nat.eq_zero_or_pos (j - D - 1) with hk0 | hkpos
      · rw [hk0]
        exact Work.Serre.DiscPair.isZero_relChainsR_point_zero _
          (Classical.choice (hne i))
      · exact Work.Serre.DiscPair.isZero_relChainsR_point_of_isZero_ratH _
          (Classical.choice (hne i)) (j - D - 1) (by omega)
          (hvan (Work.Serre.csrCentre (D - 2) Γ ι f i) (j - D - 1) hkpos (by omega) (by omega))
  · -- **below the cell dimension**
    push_neg at hDj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- degree `0`: the cylinder is path connected and meets the subspace
      subst hj0
      haveI hΓ' : PathConnectedSpace (Work.RatHurewicz.attachCells (D - 2) Γ ι f) :=
        Work.Serre.CWModel.pathConnectedSpace_attachCells (D - 2) Γ ι f
      haveI hXpc : PathConnectedSpace X := pathConnectedSpace_of_isSerreFibration q hq hpc
      haveI hMpc : PathConnectedSpace (Work.Serre.cyl q) := pathConnectedSpace_cyl q
      obtain ⟨γ₀⟩ := hΓ.nonempty
      obtain ⟨x₀⟩ := (hpc (Work.RatHurewicz.attachIncl (D - 2) Γ ι f γ₀)).nonempty
      haveI hA₂ : Nonempty ↥((Work.Serre.cylRetract q) ⁻¹'
          Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f) ∪ Set.range (Work.Serre.cylIncl q)) :=
        ⟨⟨Work.Serre.cylIncl q x₀.1, Or.inr ⟨x₀.1, rfl⟩⟩⟩
      exact Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int (TopCat.of (Work.Serre.cyl q)) _ 0
        (ModuleCat.isZero_iff_subsingleton.mpr
          (Work.RatHurewicz.Cofibre.subsingleton_homology_zero_relChains
            (TopCat.of (Work.Serre.cyl q)) _))
    · -- degrees `1 ≤ j < D`: the cofibre splitting `coker × ker` has both factors zero
      obtain ⟨e⟩ := Work.Serre.DiscPair.cylPairCofibre D Γ ι f q hq j (by omega)
      refine IsZero.of_iso ?_ e
      refine Work.Serre.DiscPair.isZero_prod ?_ ?_
      · refine isZero_cokernel_of_isZero_tgt _ ?_
        exact Work.Serre.DiscPair.isZero_relChainsR_homology_self_of_lt (D - 2) Γ ι f j (by omega)
      · refine Work.Serre.DiscPair.isZero_kernel_of_isZero_src _ ?_
        exact Work.Serre.DiscPair.isZero_relChainsR_homology_preimage_of_lt (D - 2) Γ ι f q hq
          (j - 1) (by omega)

end

end Work.Serre
