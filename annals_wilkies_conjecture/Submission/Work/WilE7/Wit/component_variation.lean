import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.eventually_mem_fiber_of_good
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE7.fiber_germ_subset_component
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE7.Wit.exists_levelSet_point_ne_self

open Set Filter Topology
open scoped Topology

namespace Work.WilE7.Wit

open WilkiesDesign WilkiesDesign.E

/-! ## Component variation of the fibre of a good stratum

Let `S` be a `Good` stratum over the first `p` coordinates with `S.j < q`: the `j` defining
equations `S.h` vanish on `S.X.set`, their fibrewise Jacobian has rank `S.j` at every point of
`S.X.set`, and near every point of `S.X.set` the fibre coincides with the level set of the
fibre map.  Since the fibrewise derivative of the fibre map is a surjection onto `ℝ^{S.j}` out of
`ℝ^q` and `S.j < q`, its kernel is non-trivial, so (by the implicit-function-theorem chart of the
level set, `Work.WilE7.Aux.levelSetChart`) the level set — and hence the fibre — contains points
arbitrarily close to `projSnd p q z` and different from it.

The lemma `fiber_germ_subset_component` says that every fibre point close enough to
`projSnd p q z` lies in the connected component of `projSnd p q z` in the fibre.  Combining the
two facts gives a point of that connected component differing from `projSnd p q z` in some
coordinate. -/

theorem component_variation {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good)
    (hj : S.j < q) (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) :
    ∃ (l : Fin q) (w : Fin q → ℝ),
      w ∈ WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z) ∧
      w ∈ connectedComponentIn
          (WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z))
          (WilkiesDesign.E.projSnd p q z) ∧
      w l ≠ WilkiesDesign.E.projSnd p q z l := by
  classical
  -- the fibre germ of `projSnd p q z` is contained in its connected component
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := fiber_germ_subset_component S hGood z hz
  -- near `projSnd p q z`, the level set of the fibre map is contained in the fibre
  have hsplit : Fin.append (projFirst p q z) (projSnd p q z) = z := append_projFirst_projSnd z
  have hzS : Fin.append (projFirst p q z) (projSnd p q z) ∈ S.X.set := by
    rw [hsplit]; exact hz
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.mem_nhds_iff.mp
    (Work.WilE7.eventually_mem_fiber_of_good S hGood (projFirst p q z) (projSnd p q z) hzS)
  -- the fibre map vanishes at `projSnd p q z`, and its derivative there is surjective
  have hgz : fgFibreMap S (projFirst p q z) (projSnd p q z) = 0 := by
    funext a
    show eaEval S.X.c (S.h a) (Fin.append (projFirst p q z) (projSnd p q z)) = 0
    rw [hsplit]
    exact Work.WilE5.Stratum.good_eqs hGood hz a
  have hsurj : (fderiv ℝ (fgFibreMap S (projFirst p q z)) (projSnd p q z)).range = ⊤ :=
    Work.WilE7.range_fderiv_fgFibreMap S hGood _ _ hzS
  -- a point of the level set, hence of the fibre, different from `projSnd p q z`
  obtain ⟨y, hy0, hyne, hydist⟩ := exists_levelSet_point_ne_self (fgFibreMap S (projFirst p q z))
    (projSnd p q z) (Work.WilE7.analyticAt_fgFibreMap S _ _) hgz hsurj hj (min ε₁ ε₂)
    (lt_min hε₁pos hε₂pos)
  have hyfib : y ∈ fiber S.X.set (projFirst p q z) :=
    hε₂ (Metric.mem_ball.mpr (lt_of_lt_of_le hydist (min_le_right _ _)))
      (fun a => congrFun hy0 a)
  have hycomp : y ∈ connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z) :=
    hε₁ y (lt_of_lt_of_le hydist (min_le_left _ _)) hyfib
  -- `y` differs from `projSnd p q z` in some coordinate
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hyne
  exact ⟨l, y, hyfib, hycomp, hl⟩

end Work.WilE7.Wit
