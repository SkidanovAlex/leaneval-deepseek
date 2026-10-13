import Mathlib
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false

open Filter Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- The map `y' ↦ Fin.append x y'` (append a fixed first block) is continuous. -/
theorem continuous_finAppend_right {p q : ℕ} (x : Fin p → ℝ) :
    Continuous (fun y' : Fin q → ℝ => Fin.append x y') :=
  (Fin.continuous_append (X := ℝ) p q).comp
    (continuous_const.prodMk continuous_id :
      Continuous fun y' : Fin q → ℝ => (x, y'))

/-- **Local `Good`-ness is inherited along a fibre.**  A point `z = (x, y)` of a good stratum
`S` has a neighbourhood on which "the equations `h = 0` hold" implies "one is in `S.X.set`"
(that is the third clause of `Stratum.Good`).  Restricting the full space `ℝ^{p+q}` to the slice
`y' ↦ Fin.append x y'` -- which is continuous and keeps the first `p` coordinates equal to `x` --
turns this into the corresponding statement in the fibre over `x`: near `y`, every solution of
`h(x, ·) = 0` lies in `fiber S.X.set x`. -/
theorem eventually_mem_fiber_of_good {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good)
    (x : Fin p → ℝ) (y : Fin q → ℝ) (hz : Fin.append x y ∈ S.X.set) :
    Filter.Eventually (fun y' : Fin q → ℝ => (∀ a, WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append x y') = 0) →
      y' ∈ WilkiesDesign.E.fiber S.X.set x) (nhds y) := by
  obtain ⟨-, -, hev⟩ := hGood (Fin.append x y) hz
  -- Pull back the neighbourhood of `Fin.append x y` along the continuous slice map.
  filter_upwards [(continuous_finAppend_right x).continuousAt.eventually hev] with y' hy'
  intro hy0
  -- The first `p` coordinates of `Fin.append x y'` are `x`, as for `Fin.append x y`.
  have hproj : projFirst p q (Fin.append x y') = projFirst p q (Fin.append x y) := by
    funext i
    exact (Fin.append_left x y' i).trans (Fin.append_left x y i).symm
  have hmem : Fin.append x y' ∈ S.X.set := hy' hproj hy0
  simpa only [WilkiesDesign.E.fiber, Set.mem_ofPred_eq] using hmem

end Work.WilE7
