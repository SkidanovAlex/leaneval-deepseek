import Mathlib
import Submission.Work.ThomBordism.TubeGenAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

open scoped unitInterval

theorem tubeGen_continuous_thetaHomotopy {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R δ : ℝ}
    (hboxδ : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R - δ)
    (hopen : IsOpen {t : Fin (8 + k) → unitInterval |
      t ∈ Cube.boundary (Fin (8 + k))
        ∨ ∃ j : Fin (8 + k), Work.ThomBordism.TubeGen.thresh R δ
            < |Work.Stems.cubeCoords (8 + k) t j|})
    (hest : ∀ (s : unitInterval) (t : Fin (8 + k) → unitInterval),
      (∃ j : Fin (8 + k), Work.ThomBordism.TubeGen.thresh R δ
        < |Work.Stems.cubeCoords (8 + k) t j|) →
      ∃ j : Fin (8 + k), R - δ
        ≤ |Work.ThomBordism.TubeGen.theta R (s : ℝ)
            (Work.Stems.cubeCoords (8 + k) t) j|) :
    Continuous (Work.ThomBordism.TubeGen.thetaHomotopyFun C g R) := by
  classical
  -- The "good set" of cube points: the boundary together with the cube points whose
  -- collapsed coordinates are large.  It is open by hypothesis.
  set S : Set (Fin (8 + k) → unitInterval) :=
    {t | t ∈ Cube.boundary (Fin (8 + k)) ∨
      ∃ j : Fin (8 + k), Work.ThomBordism.TubeGen.thresh R δ
        < |Work.Stems.cubeCoords (8 + k) t j|} with hS
  have hSopen : IsOpen S := by rw [hS]; exact hopen
  -- The source is covered by the two open sets: the points off the boundary of the cube,
  -- and the points of the good set.
  set Vset : Set (unitInterval × (Fin (8 + k) → unitInterval)) :=
    {p | p.2 ∉ Cube.boundary (Fin (8 + k))} with hVset
  set Wset : Set (unitInterval × (Fin (8 + k) → unitInterval)) :=
    {p | p.2 ∈ S} with hWset
  have hVopen : IsOpen Vset := by
    rw [hVset]
    exact (Work.Stems.isClosed_cubeBoundary (8 + k)).isOpen_compl.preimage continuous_snd
  have hWopen : IsOpen Wset := by
    rw [hWset]
    exact hSopen.preimage continuous_snd
  -- On `Vset` the map is the explicit composition with `g`, hence continuous.
  have hVcont : ContinuousOn (Work.ThomBordism.TubeGen.thetaHomotopyFun C g R) Vset := by
    have h1 : ContinuousOn (fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
        (p.1 : ℝ)) Vset :=
      (continuous_subtype_val.comp continuous_fst).continuousOn
    have h2 : ContinuousOn (fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
        Work.Stems.cubeCoords (8 + k) p.2) Vset := by
      intro p hp
      rw [hVset] at hp
      exact (Work.Stems.continuousAt_cubeCoords_of_not_mem_boundary (8 + k) hp).comp_continuousWithinAt
        continuous_snd.continuousWithinAt
    have hpair : ContinuousOn (fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
        ((p.1 : ℝ), Work.Stems.cubeCoords (8 + k) p.2)) Vset := h1.prodMk h2
    have hT : ContinuousOn (fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
        Work.ThomBordism.TubeGen.theta R (p.1 : ℝ)
          (Work.Stems.cubeCoords (8 + k) p.2)) Vset :=
      (Work.ThomBordism.TubeGen.continuous_theta R).comp_continuousOn hpair
    have hsome : ContinuousOn (fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
        (OnePoint.some (Work.ThomBordism.TubeGen.theta R (p.1 : ℝ)
          (Work.Stems.cubeCoords (8 + k) p.2)) :
            OnePoint (Work.Tubular.Euc (8 + k)))) Vset :=
      OnePoint.continuous_coe.comp_continuousOn hT
    refine (g.continuous.comp_continuousOn hsome).congr ?_
    intro p hp
    rw [hVset] at hp
    exact Work.ThomBordism.TubeGen.thetaHomotopyFun_apply_of_notMem C g R p.1 p.2 hp
  -- On `Wset` the map is constantly `∞`: the interpolation has left the tube.
  have hWcont : ContinuousOn (Work.ThomBordism.TubeGen.thetaHomotopyFun C g R) Wset := by
    refine (continuousOn_const (c := (OnePoint.infty : OnePoint (Work.Tubular.NormalTotal E)))).congr ?_
    intro p hp
    rw [hWset] at hp
    by_cases hb : p.2 ∈ Cube.boundary (Fin (8 + k))
    · exact Work.ThomBordism.TubeGen.thetaHomotopyFun_apply_of_mem C g R p.1 p.2 hb
    · rw [hS] at hp
      rcases hp with hb' | ⟨j, hj⟩
      · exact absurd hb' hb
      · rw [Work.ThomBordism.TubeGen.thetaHomotopyFun_apply_of_notMem C g R p.1 p.2 hb]
        refine hg _ ?_
        intro hmem
        obtain ⟨j', hj'⟩ := hest p.1 p.2 ⟨j, hj⟩
        exact absurd (hboxδ _ (C.openTube_subset_U hmem) j') (not_lt.mpr hj')
  -- The two open pieces cover the source.
  have hcover : Vset ∪ Wset = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rw [hVset, hWset, hS]
    by_cases hb : p.2 ∈ Cube.boundary (Fin (8 + k))
    · exact Or.inr (Or.inl hb)
    · exact Or.inl hb
  have hunion : ContinuousOn (Work.ThomBordism.TubeGen.thetaHomotopyFun C g R)
      (Vset ∪ Wset) := hVcont.union_of_isOpen hWcont hVopen hWopen
  rw [hcover] at hunion
  exact continuousOn_univ.mp hunion

end Work.ThomBordism
