import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.level_eq_subset_sidesO
import Submission.Work.Top.isPreconnected_gt_potential

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The bounded side of a ray polygon lies below its equipotential level

Let `ps` be a list of co-landing pairs of rays of the dynamical plane of `T_c` and let `1 < R`.
The polygonal curve `Work.EL.polyCurve ps R` is (for an admissible `ps`) a Jordan curve whose
boundary pieces are the ray pieces below level `R`, the landing points (in the filled Julia set)
and the equipotential arcs at level exactly `R`.  Every one of these pieces lies in the sublevel
set `{pot ≤ log R}`.

Given *any* pair of sides `S` of that curve (i.e. any decomposition of the complement into a
bounded and an unbounded preconnected open piece with the curve as common frontier), the bounded
side is contained in the *strict* sublevel set `{pot < log R}`:

* the superlevel set `{log R < pot}` is preconnected (`Work.Top.isPreconnected_gt_potential`) and
  unbounded, and it misses `polyCurve ps R`; hence it is contained in the *unbounded* side `O`
  (`Work.Top.Sides.subset_O_of_unbounded`);

* so a point of the bounded side `I` cannot have potential `> log R` (it would lie in `O`), and
  it cannot have potential exactly `log R` either: such a point lies in the closure of the
  superlevel set (`Work.ELTop.mem_closure_gt_pot`), hence in `closure O = O ∪ polyCurve`, i.e.
  in `O` or on the curve — both excluded for a point of `I`.

This is the statement `Work.ELTop.sides_I_subset_pot_lt`.
-/

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

theorem sides_I_subset_pot_lt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) {R : ℝ} (hR : 1 < R)
    (S : Work.Top.Sides (Work.EL.polyCurve ps R)) :
    S.I ⊆ {z : ℂ | Work.EL.pot hN z < Real.log R} := by
  intro z hz
  change Work.EL.pot hN z < Real.log R
  by_contra hcon
  rw [not_lt] at hcon
  -- the superlevel set of the potential misses the polygon
  have hAsub : {w : ℂ | Real.log R < Work.EL.pot hN w} ⊆ (Work.EL.polyCurve ps R)ᶜ := by
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwC
    have h1 : Work.EL.pot hN w ≤ Real.log R := polyCurve_subset_pot_le hN ps hR hwC
    exact not_le.mpr hw h1
  -- it is preconnected and unbounded, hence lies in the unbounded side
  have hApre : IsPreconnected {w : ℂ | Real.log R < Work.EL.pot hN w} :=
    Work.Top.isPreconnected_gt_potential hN hR
  have hAunb : ∀ n : ℕ, ∃ w ∈ {w : ℂ | Real.log R < Work.EL.pot hN w}, (n : ℝ) ≤ ‖w‖ := by
    intro n
    obtain ⟨ρ, hρ⟩ := hN.tendsto_potential (Real.log R + 1)
    have hnn : (0 : ℝ) ≤ max ρ (n : ℝ) := le_trans (Nat.cast_nonneg n) (le_max_right _ _)
    have hpos : (0 : ℝ) < max ρ (n : ℝ) + 1 := by linarith
    have hnorm : ‖(((max ρ (n : ℝ) + 1 : ℝ)) : ℂ)‖ = max ρ (n : ℝ) + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hle : ρ ≤ ‖(((max ρ (n : ℝ) + 1 : ℝ)) : ℂ)‖ := by
      rw [hnorm]; linarith [le_max_left ρ (n : ℝ)]
    refine ⟨(((max ρ (n : ℝ) + 1 : ℝ)) : ℂ), ?_, ?_⟩
    · rw [Set.mem_ofPred_eq, Work.EL.pot_apply]
      have h := hρ _ hle
      linarith
    · rw [hnorm]
      linarith [le_max_right ρ (n : ℝ)]
  have hAO : {w : ℂ | Real.log R < Work.EL.pot hN w} ⊆ S.O :=
    S.subset_O_of_unbounded hApre hAsub hAunb
  rcases lt_or_eq_of_le hcon with hlt | heq
  · -- potential strictly above the level: the point lies in the unbounded side
    exact S.notMem_O_of_mem_I hz (hAO hlt)
  · -- potential exactly at the level: the point is in the closure of the unbounded side
    have hzcl : z ∈ closure {w : ℂ | Real.log R < Work.EL.pot hN w} :=
      mem_closure_gt_pot hN hR heq.symm
    have hcl : closure S.O = S.O ∪ Work.EL.polyCurve ps R := by
      rw [closure_eq_self_union_frontier, S.frontier_O]
    have hzc : z ∈ S.O ∪ Work.EL.polyCurve ps R := by
      rw [← hcl]
      exact closure_mono hAO hzcl
    rcases hzc with h | h
    · exact S.notMem_O_of_mem_I hz h
    · exact S.notMem_C_of_mem_I hz h

end Work.ELTop
