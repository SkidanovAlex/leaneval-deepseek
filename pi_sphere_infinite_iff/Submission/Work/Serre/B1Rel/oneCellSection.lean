import Mathlib
import Submission.Work.Serre.B1Rel.Defs
import Submission.Work.Serre.cubeRelIso
import Submission.Work.StemsB.hasHLP_pullback

/-!
# A section of a Serre fibration over the interior of an attached `1`-cell

Let `Z = attachOneCells Y ι f` be the space obtained from `Y` by attaching the intervals
`D¹ = [-1,1]` along the maps `f : ι → C(S⁰, Y)`, and let `q : E → Z` be a Serre fibration whose
fibre over the centre of the `i`-th cell is nonempty.  Then `q` has a continuous section over the
open `i`-th cell `oᵢ = cellInteriorOne Y ι f i`:

  `∃ s : C(oᵢ, q⁻¹'oᵢ), csrRestrict q oᵢ ∘ s = id`.

The proof is the classical one for fibrations over a contractible base, made effective by the fact
that the open cell sits inside the *model* interval `D¹`, which is homeomorphic to the cube `I¹`:

* the pullback `pullbackSnd q (oneCellMap i)` of `q` along the characteristic map is a Serre
  fibration over the model interval (`Work.StemsB.hasHLP_pullback`);
* a Serre fibration over the cube has a section as soon as its total space is nonempty
  (`Work.Serre.exists_section_cubePullback`, via the contraction of the cube), and transporting
  along the homeomorphism `icOneDiskOneHomeo : I¹ ≃ₜ D¹` produces a section `s'` of
  `pullbackSnd q (oneCellMap i)` over the whole model interval `D¹`;
* the chart `Work.Serre.OneCell.exists_chart` of the open cell (a continuous right inverse of the
  characteristic map) turns `w ↦ (s' (S w)).1.1` into a continuous section of `q` over `oᵢ`.

The statement is the `D = 1` analogue of `Work.Serre.Csr.csrOpenBallSection` (the closed half-ball
around the centre of a cell of dimension `n + 2 ≥ 2`).
-/

open scoped Topology unitInterval
open CategoryTheory

namespace Work.Serre.B1Rel

noncomputable section

/-- The homeomorphism `I¹ ≃ₜ D¹ = [-1,1]` (the `1`-dimensional case of
`Work.Serre.cubeDiscHomeo`). -/
def icOneDiskOneHomeo : Work.Stems.Cubical.IC 1 ≃ₜ Work.Serre.cellDiskOne :=
  (Homeomorph.funUnique (Fin 1) unitInterval).trans
    ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm.trans
      (Homeomorph.setCongr (by rw [Real.closedBall_eq_Icc (x := 0) (r := 1)]; norm_num)))

/-- **A section of the pullback fibration over the closed model interval.**  For a Serre fibration
`q : E → attachOneCells Y ι f` whose fibre over the centre of the `i`-th cell is nonempty, the
pullback `pullbackSnd q (oneCellMap i)` over the model interval `D¹ = [-1,1]` admits a section:
`D¹` is homeomorphic to the cube `I¹`, over which the pullback of any Serre fibration with
nonempty total space has a section (`Work.Serre.exists_section_cubePullback`). -/
theorem oneCellSectionDisc (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (i : ι)
    (hne : Nonempty (Work.StemsB.fibre q (Work.Serre.OneCell.oneCellCentreOne Y ι f i))) :
    ∃ s : C(Work.Serre.cellDiskOne,
        Work.StemsB.Pullback q (Work.Serre.oneCellMap Y ι f i)),
      (Work.StemsB.pullbackSnd q (Work.Serre.oneCellMap Y ι f i)).comp s
        = ContinuousMap.id Work.Serre.cellDiskOne := by
  classical
  obtain ⟨z₀⟩ := hne
  set e : Work.Stems.Cubical.IC 1 ≃ₜ Work.Serre.cellDiskOne := icOneDiskOneHomeo with he
  set p : C(Work.Serre.cellDiskOne, Work.Serre.attachOneCells Y ι f) :=
    Work.Serre.oneCellMap Y ι f i with hp
  set tau : C(Work.Stems.Cubical.IC 1, Work.Serre.cellDiskOne) := ⟨e, e.continuous⟩ with htau
  have htau_apply : ∀ u, tau u = e u := fun u => rfl
  -- the point of the total space over the centre of the cell, paired with a cube point mapping to it
  set w0 : Work.StemsB.Pullback q p :=
    ⟨(z₀.1, Work.Serre.OneCell.cellDiskOneCentreOne), z₀.2⟩ with hw0def
  have hw0 : Work.StemsB.pullbackSnd q p w0 = tau (e.symm (Work.StemsB.pullbackSnd q p w0)) := by
    show Work.Serre.OneCell.cellDiskOneCentreOne
      = tau (e.symm Work.Serre.OneCell.cellDiskOneCentreOne)
    rw [htau_apply, Homeomorph.apply_symm_apply]
  -- the section of the projection over the cube
  obtain ⟨sig, hsig⟩ := Work.Serre.exists_section_cubePullback 1 (Work.StemsB.pullbackSnd q p)
    (fun d => Work.StemsB.hasHLP_pullback q p (hq d)) tau
      ⟨(w0, e.symm (Work.StemsB.pullbackSnd q p w0)), hw0⟩
  have hsig' : ∀ u : Work.Stems.Cubical.IC 1, (sig u).1.2 = u :=
    fun u => congrFun (congrArg DFunLike.coe hsig) u
  refine ⟨⟨fun v => (sig (e.symm v)).1.1, ?_⟩, ?_⟩
  · have h1 : Continuous fun x : Work.StemsB.Pullback (Work.StemsB.pullbackSnd q p) tau =>
        x.1.1 := continuous_fst.comp continuous_subtype_val
    exact h1.comp (sig.continuous.comp e.symm.continuous)
  · apply ContinuousMap.ext
    intro v
    show Work.StemsB.pullbackSnd q p ((sig (e.symm v)).1.1) = v
    rw [show Work.StemsB.pullbackSnd q p ((sig (e.symm v)).1.1)
        = tau ((sig (e.symm v)).1.2) from (sig (e.symm v)).2]
    rw [hsig' (e.symm v), htau_apply, Homeomorph.apply_symm_apply]

/-- **A section of `q` over the open `i`-th `1`-cell.** -/
theorem oneCellSection (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (i : ι)
    (hne : Nonempty (Work.StemsB.fibre q (Work.Serre.OneCell.oneCellCentreOne Y ι f i))) :
    ∃ s : C(↥(Work.Serre.OneCell.cellInteriorOne Y ι f i),
        ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i)),
      (Work.Serre.csrRestrict q (Work.Serre.OneCell.cellInteriorOne Y ι f i)).comp s
        = ContinuousMap.id ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i) := by
  classical
  obtain ⟨s', hs'⟩ := oneCellSectionDisc Y ι f q hq i hne
  obtain ⟨S, hS1, hS2⟩ := Work.Serre.OneCell.exists_chart (Y := Y) (ι := ι) f i
  -- `s'` is a section of the projection: its second coordinate is the point of the model interval
  have hsec : ∀ v : Work.Serre.cellDiskOne,
      (s' v).1.2 = v := fun v => congrFun (congrArg DFunLike.coe hs') v
  -- the section property, computed in the model interval
  have hq' : ∀ w : ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i),
      q ((s' (S w)).1.1) = (w : Work.Serre.attachOneCells Y ι f) := by
    intro w
    calc q ((s' (S w)).1.1)
        = Work.Serre.oneCellMap Y ι f i ((s' (S w)).1.2) := (s' (S w)).2
      _ = Work.Serre.oneCellMap Y ι f i (S w) := by rw [hsec (S w)]
      _ = (w : Work.Serre.attachOneCells Y ι f) := hS1 w
  refine ⟨⟨fun w => ⟨(s' (S w)).1.1, ?_⟩, ?_⟩, ?_⟩
  · show q ((s' (S w)).1.1) ∈ Work.Serre.OneCell.cellInteriorOne Y ι f i
    rw [hq' w]
    exact w.2
  · refine Continuous.subtype_mk
      (f := fun w : ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i) => (s' (S w)).1.1) ?_ _
    have h1 : Continuous fun w : ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i) => s' (S w) :=
      s'.continuous.comp (continuous_subtype_val.comp S.continuous)
    have h2 : Continuous fun x : Work.StemsB.Pullback q (Work.Serre.oneCellMap Y ι f i) =>
        (x.1.1 : E) := continuous_fst.comp continuous_subtype_val
    exact h2.comp h1
  · apply ContinuousMap.ext
    intro w
    apply Subtype.ext
    show q ((s' (S w)).1.1) = (w : Work.Serre.attachOneCells Y ι f)
    rw [hq' w]

end

end Work.Serre.B1Rel
