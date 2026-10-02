import Mathlib
import Submission.Work.ThomBordism.Port.PdGoodUnivChart
import Submission.Work.ThomBordism.Port.Glue
import Submission.Work.ThomBordism.Port.PdGoodIUnion
import Submission.Work.ThomBordism.Port.PdGoodOpenSubsetChart
import Submission.Work.Cohomology.good_empty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Compactly supported duality for an *arbitrary open* subset of a compact charted space

`Work.Cohomology.Good N c W hW` is the elementwise form of Poincaré–Lefschetz duality for the open
set `W` (see `Work.Cohomology.pd_good`), and `Work.Cohomology.pd_good_univ_chart` (under the
clash-free port `Submission/Work/ThomBordism/Port/PdGoodUnivChart.lean`) assembles it for the whole
space `W = Set.univ` from local generation of `c ∈ H_N(M;ℤ)`.

Here we do the same for **every** open `U ⊆ M`: `M` is compact, so it is covered by finitely many
coordinate balls `B z` (`z ∈ t`), each small enough to lie inside one chart and to satisfy `Good`
(`Work.Cohomology.pd_good_open_subset_chartBall_chart'`).  Then `U = ⋃_{z ∈ t} (U ∩ B z)` is a
finite union of open subsets of coordinate balls, hence `Good` by the gluing induction, each
pairwise intersection lying inside a single chart (`Work.Cohomology.glue_of_chart`).

This is the "compactly supported duality for open subsets" input used by the relative-duality
chapter (`Work.ThomBordism.RelDuality`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.RelDuality

/-- **Compactly supported duality for an arbitrary open subset.**  If `M` is a compact Hausdorff
space charted over `ℝ^N` and `c ∈ H_N(M;ℤ)` is a local generator at every point, then
`Good N c U hU` holds for every open set `U ⊆ M`. -/
theorem goodOfOpen {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ {(HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N c)} = ⊤)
    (hN : 1 ≤ N) :
    ∀ (U : Set M) (hU : IsOpen U), Work.Cohomology.Good N c U hU := by
  intro U hU
  classical
  -- a chart radius at every point
  have hrad : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) x) x) r
        ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) x).target := by
    intro x
    exact Metric.mem_nhds_iff.mp
      (((chartAt (EuclideanSpace ℝ (Fin N)) x).open_target).mem_nhds
        ((chartAt (EuclideanSpace ℝ (Fin N)) x).map_source (mem_chart_source _ x)))
  choose ρ hρpos hρsub using hrad
  -- the coordinate balls
  let B : M → Set M := fun z =>
    ((chartAt (EuclideanSpace ℝ (Fin N)) z) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) z) z) (ρ z / 2))
      ∩ (chartAt (EuclideanSpace ℝ (Fin N)) z).source
  have hBopen : ∀ z, IsOpen (B z) := fun z => by
    show IsOpen (((chartAt (EuclideanSpace ℝ (Fin N)) z) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) z) z) (ρ z / 2))
      ∩ (chartAt (EuclideanSpace ℝ (Fin N)) z).source)
    rw [Set.inter_comm]
    exact (chartAt (EuclideanSpace ℝ (Fin N)) z).isOpen_inter_preimage Metric.isOpen_ball
  have hBself : ∀ z, z ∈ B z := fun z => by
    constructor
    · exact Metric.mem_ball_self (half_pos (hρpos z))
    · exact mem_chart_source _ z
  have hBsub : ∀ z, B z ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) z).source :=
    fun z _ hy => hy.2
  -- finitely many balls cover `M`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover B hBopen
    (fun z _ => Set.mem_iUnion.mpr ⟨z, hBself z⟩)
  -- the pieces `W z = U ∩ B z
  let W : M → Set M := fun z => U ∩ B z
  have hWopen : ∀ z, IsOpen (W z) := fun z => hU.inter (hBopen z)
  -- each piece is `Good`, being an open subset of the coordinate ball `B z`
  have hWgood : ∀ z, Work.Cohomology.Good N c (W z) (hWopen z) := by
    intro z
    exact Work.Cohomology.pd_good_open_subset_chartBall_chart' c hc hN z (ρ z)
      (hρpos z) (hρsub z)
      (fun {_U _V} hU' hV' hI hsub => Work.Cohomology.glue_of_chart hU' hV' hI z hsub)
      (Work.Cohomology.good_empty N c) (W z) (fun y hy => ⟨hy.2.1, hy.2.2⟩)
      (hWopen z) (hWopen z)
  -- the finite unions of the pieces
  have main : ∀ u : Finset M, Work.Cohomology.Good N c (Work.Cohomology.covUnion W u)
      (Work.Cohomology.isOpen_covUnion hWopen u) := by
    intro u
    induction u using Finset.induction with
    | empty =>
        have hEq : Work.Cohomology.covUnion W (∅ : Finset M) = (∅ : Set M) := by
          simp only [Work.Cohomology.covUnion, Finset.coe_empty, Set.image_empty,
            Set.sUnion_empty]
        exact Work.Cohomology.good_of_set_eq hEq.symm isOpen_empty
          (Work.Cohomology.isOpen_covUnion hWopen ∅) (Work.Cohomology.good_empty N c)
    | insert z u hz ih =>
        have hzopen : IsOpen (W z) := hWopen z
        have huopen : IsOpen (Work.Cohomology.covUnion W u) :=
          Work.Cohomology.isOpen_covUnion hWopen u
        have hIopen : IsOpen (Work.Cohomology.covUnion W u ∩ W z) := huopen.inter hzopen
        have hI'open : IsOpen (W z ∩ Work.Cohomology.covUnion W u) := hzopen.inter huopen
        have hinter : Work.Cohomology.Good N c
            (Work.Cohomology.covUnion W u ∩ W z) hIopen := by
          exact Work.Cohomology.pd_good_open_subset_chartBall_chart' c hc hN z (ρ z)
            (hρpos z) (hρsub z)
            (fun {_U _V} hU' hV' hI hsub => Work.Cohomology.glue_of_chart hU' hV' hI z hsub)
            (Work.Cohomology.good_empty N c)
            (Work.Cohomology.covUnion W u ∩ W z)
            (fun y hy => ⟨hy.2.2.1, hy.2.2.2⟩) hIopen hIopen
        have hgood : Work.Cohomology.Good N c (W z ∪ Work.Cohomology.covUnion W u)
            (hzopen.union huopen) :=
          Work.Cohomology.glue_of_chart hzopen huopen hI'open z
            (fun x hx => hBsub z (Set.inter_subset_left hx).2)
            (hWgood z)
            (Work.Cohomology.good_of_open_eq _ _ ih)
            (Work.Cohomology.good_of_set_eq (Set.inter_comm _ _) hIopen hI'open hinter)
        exact Work.Cohomology.good_of_set_eq (Work.Cohomology.covUnion_insert W z u).symm
          (hzopen.union huopen) (Work.Cohomology.isOpen_covUnion hWopen (insert z u)) hgood
  -- the union of all the pieces is `U`
  have hcov : Work.Cohomology.covUnion W t = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hx
      obtain ⟨z, -, rfl⟩ := (Set.mem_image W ((t : Set M)) s).mp hs
      exact hxs.1
    · intro hx
      have hx' := ht (Set.mem_univ x)
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨z, hzt, hxz⟩ := hx'
      exact Set.mem_sUnion.mpr
        ⟨W z, (Set.mem_image W ((t : Set M)) (W z)).mpr ⟨z, by simpa using hzt, rfl⟩,
          ⟨hx, hxz⟩⟩
  exact Work.Cohomology.good_of_set_eq hcov (Work.Cohomology.isOpen_covUnion hWopen t) hU
    (main t)

end Work.ThomBordism.RelDuality
