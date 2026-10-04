import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

open scoped BigOperators

/-- The `i`-th partial derivative of the periodization `x ↦ ∑' m, f (x + m)` of a smooth function
`f` supported in the open unit cube agrees, at every point `x` of the open unit cube, with the
`i`-th partial derivative of `f` itself.

Indeed the periodization agrees with `f` on the *whole* open unit cube (every multi-index `m ≠ 0`
contributes `0` there, because `f` is supported in the cube), and `x` is an interior point of that
cube; so the two functions are equal on a neighbourhood of `x` and hence have the same Fréchet
derivative at `x`. -/
theorem pd_periodization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) (i : ι) :
    ∀ x : ι → ℝ, (∀ j, x j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      Work.Diff.STE.pd i (fun y : ι → ℝ => ∑' m : ι → ℤ, f (y + fun i => (m i : ℝ))) x
        = Work.Diff.STE.pd i f x := by
  intro x hx
  -- the open unit cube is a neighbourhood of `x`
  have hBopen : IsOpen (Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hxB : x ∈ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    rw [Set.mem_pi]
    intro j _
    exact hx j
  -- on the whole open unit cube the periodization coincides with `f`
  have hev : (fun y : ι → ℝ => ∑' m : ι → ℤ, f (y + fun j => (m j : ℝ))) =ᶠ[nhds x] f := by
    refine Filter.eventually_of_mem (hBopen.mem_nhds hxB) ?_
    intro y hy
    exact periodization_eq_self hsupp (fun j => Set.mem_pi.mp hy j (Set.mem_univ j))
  have hfe : fderiv ℝ (fun y : ι → ℝ => ∑' m : ι → ℤ, f (y + fun j => (m j : ℝ))) x
      = fderiv ℝ f x := hev.fderiv_eq
  simp only [pd]
  rw [hfe]

end Work.Diff.STE
