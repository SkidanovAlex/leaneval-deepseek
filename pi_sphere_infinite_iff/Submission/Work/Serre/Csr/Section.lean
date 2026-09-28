import Mathlib
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.DiscPair
import Submission.Work.Serre.Csr.Target
import Submission.Work.Serre.Csr.relChainsCubeDisc
import Submission.Work.Serre.cubeRelIso

/-!
# A section of `q` over the cell disc and over the open half-ball

A Serre fibration over the contractible cube `I^{n+2}` has a section as soon as its total space is
nonempty (`Work.Serre.exists_section_cubePullback`).  Transporting along the homeomorphism
`cubeDiscHomeo n` and the two pullback homeomorphisms of `Work.Serre.Csr.DiscPair` gives a section of
the projection of `Pullback q (cellMap i)` over the whole closed model cell; restricting along the
continuous inverse `cellInterior_section i` of `cellMap i` on the cell interior then gives a section
of `q` over the open half-ball `csrOpenBall i`.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.Csr

noncomputable section

/-- **A section of the pullback fibration over the closed model cell.** -/
theorem csrDiscSection (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (i : ι)
    (hne : Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i))) :
    ∃ s : C(Work.RatHurewicz.cellDisk n, csrPull f q i),
      (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i)).comp s
        = ContinuousMap.id (Work.RatHurewicz.cellDisk n) := by
  obtain ⟨z₀⟩ := hne
  obtain ⟨sig, hsig⟩ := Work.Serre.exists_section_cubePullback (n+2)
    (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
    (fun d => Work.StemsB.hasHLP_pullback q (Work.RatHurewicz.cellMap n Y ι f i) (hq d))
    (homeoToCM (cubeDiscHomeo n))
    (⟨(⟨(z₀.1, Work.RatHurewicz.cellDiskCentre n), z₀.2⟩,
      (cubeDiscHomeo n).symm (Work.RatHurewicz.cellDiskCentre n)), by
        show Work.RatHurewicz.cellDiskCentre n =
          homeoToCM (cubeDiscHomeo n) ((cubeDiscHomeo n).symm (Work.RatHurewicz.cellDiskCentre n))
        rw [homeoToCM_apply, Homeomorph.apply_symm_apply]⟩)
  let gs : C(Work.Stems.Cubical.IC (n+2), csrPull f q i) :=
    (homeoToCM (pullbackHomeo q (Work.RatHurewicz.cellMap n Y ι f i) (cubeDiscHomeo n))).comp
      ((homeoToCM (pullbackAssocHomeo q (Work.RatHurewicz.cellMap n Y ι f i)
        (homeoToCM (cubeDiscHomeo n)))).comp sig)
  have hgs : ∀ t : Work.Stems.Cubical.IC (n+2),
      Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) (gs t)
        = homeoToCM (cubeDiscHomeo n) t := by
    intro t
    have h1 : (sig t).1.2 = t := congrFun (congrArg DFunLike.coe hsig) t
    show homeoToCM (cubeDiscHomeo n) ((sig t).1.2) = homeoToCM (cubeDiscHomeo n) t
    rw [h1]
  refine ⟨gs.comp (homeoToCM ((cubeDiscHomeo n).symm)), ?_⟩
  apply ContinuousMap.ext
  intro v
  show Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i)
    (gs ((cubeDiscHomeo n).symm v)) = v
  rw [hgs ((cubeDiscHomeo n).symm v), homeoToCM_apply, Homeomorph.apply_symm_apply]

/-- **A section of `q` over the open half-ball around a cell centre.** -/
theorem csrOpenBallSection' (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (i : ι)
    (hne : Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i))) :
    ∃ s : C(↥(csrOpenBall n Y ι f i), ↥(q ⁻¹' (csrOpenBall n Y ι f i))),
      (csrRestrict q (csrOpenBall n Y ι f i)).comp s
        = ContinuousMap.id ↥(csrOpenBall n Y ι f i) := by
  obtain ⟨s', hs'⟩ := csrDiscSection n Y ι f q hq i hne
  have hsec : ∀ v : Work.RatHurewicz.cellDisk n,
      Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) (s' v) = v :=
    fun v => congrFun (congrArg DFunLike.coe hs') v
  refine ⟨⟨fun w => ⟨(s' (fromBall n Y ι f i w)).1.1, ?_⟩, ?_⟩, ?_⟩
  · show q ((s' (fromBall n Y ι f i w)).1.1) ∈ csrOpenBall n Y ι f i
    have h1 : q ((s' (fromBall n Y ι f i w)).1.1) =
        Work.RatHurewicz.cellMap n Y ι f i (fromBall n Y ι f i w) := by
      rw [(s' (fromBall n Y ι f i w)).2]
      exact congrArg (fun y : Work.RatHurewicz.cellDisk n =>
        Work.RatHurewicz.cellMap n Y ι f i y) (hsec (fromBall n Y ι f i w))
    rw [h1, cellMap_fromBall]
    exact w.2
  · refine Continuous.subtype_mk (f := fun w : ↥(csrOpenBall n Y ι f i) =>
      (s' (fromBall n Y ι f i w)).1.1) ?_ _
    exact continuous_fst.comp (continuous_subtype_val.comp
      (s'.continuous.comp (continuous_fromBall n Y ι f i)))
  · apply ContinuousMap.ext
    intro w
    apply Subtype.ext
    show q ((s' (fromBall n Y ι f i w)).1.1) = (w : Work.RatHurewicz.attachCells n Y ι f)
    rw [show q ((s' (fromBall n Y ι f i w)).1.1) =
        Work.RatHurewicz.cellMap n Y ι f i (fromBall n Y ι f i w) from by
      rw [(s' (fromBall n Y ι f i w)).2]
      exact congrArg (fun y : Work.RatHurewicz.cellDisk n =>
        Work.RatHurewicz.cellMap n Y ι f i y) (hsec (fromBall n Y ι f i w))]
    exact cellMap_fromBall n Y ι f i w

end

end Work.Serre.Csr
