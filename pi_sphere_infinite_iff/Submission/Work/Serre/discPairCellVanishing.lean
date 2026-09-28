import Mathlib
import Submission.Work.Serre.DiscPair.discPairCohVanishing
import Submission.Work.Serre.DiscPair.cellStepVanishing
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.DiscPair.discCellStep
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.CWModel.Defs
import Submission.Work.Serre.exists_path_pullbackFst
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.ThomCylDefs

/-!
# The disc-pair cell vanishing

The relative cohomology of the disc-pair bundle
`(cyl q, (cylRetract q)⁻¹ (old part) ∪ range (cylIncl q))` of a Serre fibration `q` over a space
obtained by attaching `D`-cells vanishes in every degree `j ≤ N + 1` except the fibre degree
`j = D + r + 1`, under the hypothesis that the fibres of `q` are path connected and rationally
acyclic in degrees `0 < t ≤ N`, `t ≠ r`.

This is the cohomological form of the disc-pair cell step (`Work.Serre.DiscPair.discCellStep`) in
the range of the fibre: in degree `j < D` the group vanishes because it is *below* the cell
dimension (`Work.Serre.DiscPair.cylPairCofibre`), and in degrees `D ≤ j ≤ N + 1` it is the direct
sum of the shifted reduced homologies of the fibres, which are concentrated in the fibre degree.
The passage from homology to cohomology over `ℚ` is the universal coefficient theorem
(`Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH`).
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Two connectivity lemmas -/

/-- **The total space of a Serre fibration over a path connected base with path connected fibres is
path connected**: a path in the base is lifted from a prescribed point, and the endpoint is joined
to the target inside the (path connected) fibre. -/
theorem pathConnectedSpace_of_isSerreFibration {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (q : C(E, B)) (hq : Work.StemsB.IsSerreFibration q)
    [PathConnectedSpace B] (hF : ∀ b, PathConnectedSpace (Work.StemsB.fibre q b)) :
    PathConnectedSpace E := by
  obtain ⟨b⟩ := (inferInstance : PathConnectedSpace B).nonempty
  obtain ⟨w⟩ := (hF b).nonempty
  refine ⟨⟨w.1⟩, fun x y => ?_⟩
  obtain ⟨γ⟩ := PathConnectedSpace.joined (q x) (q y)
  obtain ⟨z, hz, ⟨α⟩⟩ := Work.Serre.exists_path_lift_of_isSerreFibration q hq rfl γ
  haveI : PathConnectedSpace {x : E // q x = q y} := hF (q y)
  obtain ⟨β⟩ := PathConnectedSpace.joined (⟨z, hz⟩ : {x : E // q x = q y}) ⟨y, rfl⟩
  exact ⟨α.trans (β.map (Work.StemsB.fibreIncl q (q y)).continuous)⟩

/-- **The mapping cylinder of a map between path connected spaces is path connected.**  Every point
of the cylinder is joined to the bottom copy of the source (`Work.Serre.cylConnected`), which is
path connected. -/
theorem pathConnectedSpace_cyl {P B : Type} [TopologicalSpace P] [TopologicalSpace B]
    (g : C(P, B)) [PathConnectedSpace P] [PathConnectedSpace B] :
    PathConnectedSpace (Work.Serre.cyl g) := by
  obtain ⟨x₀⟩ := (inferInstance : PathConnectedSpace P).nonempty
  refine ⟨⟨Work.Serre.cylIncl g x₀⟩, fun x y => ?_⟩
  obtain ⟨a, ⟨pa⟩⟩ := Work.Serre.cylConnected g x
  obtain ⟨u, hu⟩ := a.2
  rw [← hu] at pa
  obtain ⟨b, ⟨pb⟩⟩ := Work.Serre.cylConnected g y
  obtain ⟨v, hv⟩ := b.2
  rw [← hv] at pb
  obtain ⟨γ⟩ := PathConnectedSpace.joined u v
  exact ⟨pa.trans ((γ.map (Work.Serre.cylIncl g).continuous).trans pb.symm)⟩

/-- A cokernel whose target is a zero module is zero. -/
theorem isZero_cokernel_of_isZero_tgt {X Y : ModuleCat ℚ} (f : X ⟶ Y) (hY : IsZero Y) :
    IsZero (cokernel f) := by
  haveI : Subsingleton ↥Y := ModuleCat.isZero_iff_subsingleton.mp hY
  haveI : Epi f :=
    (ModuleCat.epi_iff_surjective f).mpr fun y => ⟨0, Subsingleton.elim _ _⟩
  exact Limits.isZero_cokernel_of_epi f

/-! ## The main theorem -/

set_option maxHeartbeats 1000000 in
theorem discPairCellVanishing (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D) {Γ : Type}
    [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (j : ℕ) (hj : j ≤ N + 1) (hjr : j ≠ D + r + 1) :
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
