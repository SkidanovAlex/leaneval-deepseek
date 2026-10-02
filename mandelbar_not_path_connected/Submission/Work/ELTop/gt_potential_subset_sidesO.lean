import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.level_eq_subset_sidesO
import Submission.Work.Top.Jordan
import Submission.Work.Top.isPreconnected_gt_potential

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The superlevel set of the potential lies in the unbounded side of a ray polygon

Let `ps` be a list of co-landing pairs of rays of the dynamical plane and let `1 < R`.  The
boundary `Work.EL.polyCurve ps R` of the associated ray polygon consists of ray pieces below
level `R`, of the landing points (which lie in the filled Julia set), and of equipotential
arcs at level exactly `R`; hence it is contained in the sublevel set `{pot ≤ log R}`
(`Work.ELTop.polyCurve_subset_pot_le`).

The superlevel set `{log R < pot}` is therefore contained in the complement of the Jordan
curve `polyCurve ps R`.  It is preconnected (`Work.Top.isPreconnected_gt_potential`) and
unbounded (the potential tends to `+∞` at infinity, while `{pot ≤ log R}` is compact), so it
lies in the unbounded side `O` of the curve.
-/

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

theorem gt_potential_subset_sidesO {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) {R : ℝ} (hR : 1 < R)
    (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    {z : ℂ | Real.log R < Work.EL.pot hN z} ⊆
      (hJ.sides (Work.EL.polyCurve ps R) hC).O := by
  intro z hz
  set S := hJ.sides (Work.EL.polyCurve ps R) hC with hS
  have hmain : {w : ℂ | Real.log R < Work.EL.pot hN w} ⊆ S.O := by
    refine S.subset_O_of_unbounded (Work.Top.isPreconnected_gt_potential hN hR) ?_ ?_
    · intro w hw
      rw [Set.mem_compl_iff]
      intro hwC
      have hle : Work.EL.pot hN w ≤ Real.log R := polyCurve_subset_pot_le hN ps hR hwC
      exact (not_le.mpr hw) hle
    · intro n
      obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp
        (Work.EL.isCompact_le_pot hN (Real.log R)).isBounded
      refine ⟨((max D (n : ℝ) + 1 : ℝ) : ℂ), ?_, ?_⟩
      · show Real.log R < Work.EL.pot hN (((max D (n : ℝ) + 1 : ℝ)) : ℂ)
        by_contra hcon
        have hle : Work.EL.pot hN (((max D (n : ℝ) + 1 : ℝ)) : ℂ) ≤ Real.log R :=
          not_lt.mp hcon
        have hcontra : ‖(((max D (n : ℝ) + 1 : ℝ)) : ℂ)‖ ≤ D := hD _ hle
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < max D (n : ℝ) + 1)] at hcontra
        linarith [le_max_left D (n : ℝ)]
      · rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < max D (n : ℝ) + 1)]
        linarith [le_max_right D (n : ℝ)]
  exact hmain hz

end Work.ELTop
