import Mathlib
import Submission.Work.Smooth.Morse.Defs

/-!
# Local injectivity of the parametrisation of the surface `F = ψ(S¹×S¹)`

The parametrisation of the challenge's surface is `param ψ p = ψ (torusMap p.1 p.2)`, where
`torusMap : ℝ × ℝ → ℝ³` is the standard parametrisation of the torus of revolution and `ψ` is a
diffeomorphism of `ℝ³`.  This file proves that `param ψ` is **locally injective**: every point of
the parameter plane has a ball on which `param ψ` is injective.

The only input about the standard torus is the classical description of its fibres,
`Work.Core.torusMap_eq_iff`:

`torusMap θ φ = torusMap θ' φ'`  iff  `θ - θ' ∈ 2πℤ` and `φ - φ' ∈ 2πℤ`,

equivalently: the difference of two parameters with the same image is a nonzero element of the
period lattice `2πℤ²` whenever it is nonzero, and every nonzero element of that lattice has norm
at least `2π` (`Work.TorusCover.lattice_norm_ge`).  Hence, on a ball of radius `< π`, two
parameters with the same image must already be equal.  Injectivity of `ψ` then transfers this to
`param ψ = ψ ∘ torusMap`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.Surface

/-- **The parametrisation of the surface `F = ψ(standard torus)` is locally injective.**

For every parameter point `p` there is `ε > 0` such that `param ψ` is injective on the ball of
radius `ε` around `p`.  (The proof works for any `ε ≤ π`; we take `ε = 1`.) -/
theorem param_local_injective (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ Set.InjOn (Work.Smooth.Morse.param ψ) (Metric.ball p ε) := by
  refine ⟨1, one_pos, ?_⟩
  intro x hx y hy hxy
  rw [Metric.mem_ball] at hx hy
  -- `ψ` is injective, so equal images under `param ψ` means equal images under `torusMap`
  have ht : Work.Core.torusMap x.1 x.2 = Work.Core.torusMap y.1 y.2 := ψ.injective hxy
  -- the fibres of the standard parametrisation are the cosets of the period lattice `2πℤ²`
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := (Work.Core.torusMap_eq_iff x.1 x.2 y.1 y.2).mp ht
  by_contra hne
  -- the difference of two parameters with the same image is a lattice vector
  have hmem : x - y ∈ Work.TorusCover.lattice := by
    rw [Work.TorusCover.mem_lattice_iff]
    refine ⟨(k, l), ?_⟩
    ext <;> simp [Work.TorusCover.periodShift] <;> linarith
  have hne0 : x - y ≠ 0 := sub_ne_zero.mpr hne
  -- ... so it has norm at least `2π`, but it is the distance between two points of a ball of
  -- radius `1`
  have hge : 2 * Real.pi ≤ ‖x - y‖ := Work.TorusCover.lattice_norm_ge hmem hne0
  have hlt : ‖x - y‖ < 2 * Real.pi := by
    rw [← dist_eq_norm]
    calc dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
      _ = dist x p + dist y p := by rw [dist_comm p y]
      _ < 1 + 1 := by linarith
      _ = 2 := by norm_num
      _ < 2 * Real.pi := by linarith [Real.pi_gt_three]
  linarith

end Work.Smooth.Morse.Surface
