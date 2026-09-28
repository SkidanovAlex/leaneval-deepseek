import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.ThomBordism.Port.PdGoodOpenSubsetChart
import Submission.Work.Cohomology.pd_good_univ

set_option synthInstance.maxHeartbeats 400000

/-!
# `PdGoodUnivChart` — import shim of the ISLANDS2 subproject

This file used to declare a **duplicate copy** of the module

* `Submission.Work.Cohomology.pd_good_univ`

(the declarations were verbatim copies: same names, same statements, same proofs).  The duplicate
made the two copies mutually unimportable — Lean refuses an environment that contains two
declarations with the same name — so the copies could not meet in the final assembly
(`Submission/Work/Islands2/AllCritical.lean`).

The ISLANDS2 subproject has removed the duplicate: this module is now a thin **shim** that simply
imports the original, so every name it used to export is still available under exactly the same
name and with exactly the same statement.  Nothing else changed; no consumer needs to be updated.
See `Submission/Work/Islands2/README.md` for the full inventory of duplicates.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem pd_good_univ_chart' {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) :
    (∀ {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V)) (cc : M),
        U ∩ V ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc).source →
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
          have h := pd_good_open_subset_chartBall_chart' c hc hN z (ρ z) (hρpos z)
            (hρsub z) (fun hU hV hI hsub => glue hU hV hI z hsub) hempty
            (covUnion B u ∩ B z) ?_ hIopen hIopen
          · exact h
          · rintro y ⟨-, hy⟩
            exact hy
        have hgood : Good N c (B z ∪ covUnion B u) (hzopen.union huopen) :=
          glue hzopen huopen hI'open z
            (fun x hx => (Set.inter_subset_left hx).2)
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
