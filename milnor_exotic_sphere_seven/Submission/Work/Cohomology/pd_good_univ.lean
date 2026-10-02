import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_good_list_pieces
import Submission.Work.Cohomology.pd_good_open_subset_chartBall

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Good` for a compact manifold: the finite coordinate cover

`Work.Cohomology.Good N c W hW` is the elementwise form of Poincaré–Lefschetz duality for the open
set `W` (see `Work.Cohomology.pd_good`).  This file assembles the proof for the whole space:

* the compact charted space `M` is covered by finitely many coordinate balls `B z`
  (`z` in a finite set `t`), each of which satisfies `Good` by the base case;
* the union of a finite subfamily is built up one ball at a time; the gluing step is the hypothesis
  `glue` (Hatcher's five lemma, `Work.Cohomology.pd_good_union`), and the intersection of the
  already constructed union with a new ball is an open subset of that coordinate ball, to which
  `Work.Cohomology.pd_good_open_subset_chartBall` applies.

The result is `Good N c Set.univ isOpen_univ`, from which
`Work.Cohomology.pd_middleDegree_of_good` deduces Poincaré duality in the middle degree.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The union of the balls of a finite family. -/
def covUnion {M : TopCat} (B : M → Set M) (u : Finset M) : Set M := ⋃₀ (B '' (u : Set M))

/-- The union of balls of a finite family is open. -/
theorem isOpen_covUnion {M : TopCat} {B : M → Set M} (hB : ∀ z, IsOpen (B z)) (u : Finset M) :
    IsOpen (covUnion B u) :=
  isOpen_sUnion (fun t ht => by
    obtain ⟨z, -, rfl⟩ := (Set.mem_image B ((u : Set M)) t).mp ht
    exact hB z)

/-- Splitting off the last ball. -/
theorem covUnion_insert {M : TopCat} [DecidableEq M] (B : M → Set M) (z : M) (u : Finset M) :
    covUnion B (insert z u) = B z ∪ covUnion B u := by
  rw [covUnion, covUnion, Finset.coe_insert, Set.image_insert_eq, Set.sUnion_insert]

/-- **`Good` for the whole compact manifold.** -/
theorem pd_good_univ {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) :
    (∀ {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V)),
        Good N c U hU → Good N c V hV → Good N c (U ∩ V) hI →
        Good N c (U ∪ V) (hU.union hV)) →
    Good N c (∅ : Set M) isOpen_empty →
    Good N c (Set.univ : Set M) isOpen_univ := by
  intro glue hempty
  classical
  -- a radius for the chart at each point
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
  -- finitely many balls cover `M`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover B hBopen
    (fun z _ => Set.mem_iUnion.mpr ⟨z, hBself z⟩)
  -- the balls satisfy `Good`
  have hBgood : ∀ z : M, Good N c (B z) (hBopen z) := by
    intro z
    have h := good_piece c hc hN z (ρ z) (hρpos z) (hρsub z) hempty
      (Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) z) z) (ρ z / 2))
      Metric.isOpen_ball (convex_ball _ _)
      (Metric.ball_subset_ball (half_le_self (le_of_lt (hρpos z))))
    exact good_of_open_eq _ _ h
  -- the finite unions
  have main : ∀ u : Finset M, Good N c (covUnion B u) (isOpen_covUnion hBopen u) := by
    intro u
    induction u using Finset.induction with
    | empty =>
        have hEq : covUnion B (∅ : Finset M) = (∅ : Set M) := by
          simp only [covUnion, Finset.coe_empty, Set.image_empty, Set.sUnion_empty]
        exact good_of_set_eq hEq.symm isOpen_empty (isOpen_covUnion hBopen ∅) hempty
    | insert z u hz ih =>
        have hzopen : IsOpen (B z) := hBopen z
        have huopen : IsOpen (covUnion B u) := isOpen_covUnion hBopen u
        have hIopen : IsOpen (covUnion B u ∩ B z) := huopen.inter hzopen
        have hI'open : IsOpen (B z ∩ covUnion B u) := hzopen.inter huopen
        have hinter : Good N c (covUnion B u ∩ B z) hIopen := by
          have h := pd_good_open_subset_chartBall c hc hN z (ρ z) (hρpos z)
            (hρsub z) glue hempty (covUnion B u ∩ B z) ?_ hIopen hIopen
          · exact h
          · rintro y ⟨-, hy⟩
            exact hy
        have hgood : Good N c (B z ∪ covUnion B u) (hzopen.union huopen) :=
          glue hzopen huopen hI'open
            (good_of_open_eq _ _ (hBgood z))
            (good_of_open_eq _ _ ih)
            (good_of_set_eq (Set.inter_comm _ _) hIopen hI'open hinter)
        exact good_of_set_eq (covUnion_insert B z u).symm (hzopen.union huopen)
          (isOpen_covUnion hBopen (insert z u)) hgood
  -- the union of all the balls is everything
  have hcov : covUnion B t = (Set.univ : Set M) := by
    refine Set.eq_univ_iff_forall.mpr (fun x => ?_)
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨z, hzt, hxz⟩ := hx
    exact Set.mem_sUnion.mpr
      ⟨B z, (Set.mem_image B ((t : Set M)) (B z)).mpr ⟨z, by simpa using hzt, rfl⟩, hxz⟩
  exact good_of_set_eq hcov (isOpen_covUnion hBopen t) isOpen_univ (main t)

end

end Work.Cohomology
