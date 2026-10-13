import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.H2.T1Q

/-!
# The derivative of `Real.smoothTransition`

`Real.smoothTransition` is Mathlib's `C^∞` function which is `0` on `(-∞, 0]` and `1` on
`[1, ∞)` (defined as `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`).

This file records the elementary consequences for its derivative `deriv Real.smoothTransition`:

* it vanishes on `(-∞, 0]`;
* it vanishes on `[1, ∞)`;
* it is bounded.

The first two statements are proved pointwise: away from the two junction points `0` and `1`
the function is *locally constant*, so `Filter.EventuallyEq.deriv_eq` applies; at `0` (resp.
`1`) the function is constant on the half line `Iic 0` (resp. `Ici 1`), so the within-derivative
there is `0`, and since `smoothTransition` is differentiable at the point, the within-derivative
on a set with `UniqueDiffWithinAt` agrees with the ordinary derivative.

For the boundedness we use that `deriv Real.smoothTransition` is continuous (as
`smoothTransition` is `C^∞`), hence bounded on the compact interval `[0,1]`, while it vanishes
off `[0,1]`.
-/

/-- `deriv Real.smoothTransition` vanishes strictly to the left of `0`, where the function is
locally `0`. -/
private lemma deriv_smoothTransition_of_lt_zero {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 x := Iio_mem_nhds hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hmem] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [heq.deriv_eq, deriv_const]

/-- `deriv Real.smoothTransition 0 = 0`: the function is `0` on the half line `Iic 0`. -/
private lemma deriv_smoothTransition_at_zero : deriv Real.smoothTransition 0 = 0 := by
  have hdiff : DifferentiableAt ℝ Real.smoothTransition (0 : ℝ) := by fun_prop
  have h2 : HasDerivWithinAt Real.smoothTransition (deriv Real.smoothTransition 0)
      (Set.Iic 0) 0 := hdiff.hasDerivAt.hasDerivWithinAt
  have h1 : HasDerivWithinAt Real.smoothTransition 0 (Set.Iic 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Set.Iic 0) (0 : ℝ)).congr
      (fun y hy => Real.smoothTransition.zero_of_nonpos hy) (by simp)
  have hd1 := h1.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  have hd2 := h2.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  exact hd2.symm.trans hd1

/-- `deriv Real.smoothTransition` vanishes strictly to the right of `1`, where the function is
locally `1`. -/
private lemma deriv_smoothTransition_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hmem : Set.Ioi (1 : ℝ) ∈ 𝓝 x := Ioi_mem_nhds hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [hmem] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [heq.deriv_eq, deriv_const]

/-- `deriv Real.smoothTransition 1 = 0`: the function is `1` on the half line `Ici 1`. -/
private lemma deriv_smoothTransition_at_one : deriv Real.smoothTransition 1 = 0 := by
  have hdiff : DifferentiableAt ℝ Real.smoothTransition (1 : ℝ) := by fun_prop
  have h2 : HasDerivWithinAt Real.smoothTransition (deriv Real.smoothTransition 1)
      (Set.Ici 1) 1 := hdiff.hasDerivAt.hasDerivWithinAt
  have h1 : HasDerivWithinAt Real.smoothTransition 0 (Set.Ici 1) 1 :=
    (hasDerivWithinAt_const (1 : ℝ) (Set.Ici 1) (1 : ℝ)).congr
      (fun y hy => Real.smoothTransition.one_of_one_le hy) (by simp)
  have hd1 := h1.derivWithin (uniqueDiffWithinAt_Ici (1 : ℝ))
  have hd2 := h2.derivWithin (uniqueDiffWithinAt_Ici (1 : ℝ))
  exact hd2.symm.trans hd1

theorem SmoothTransitionDeriv :
    (∀ x : ℝ, x ≤ 0 → deriv Real.smoothTransition x = 0) ∧
    (∀ x : ℝ, 1 ≤ x → deriv Real.smoothTransition x = 0) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M) := by
  have hleft : ∀ x : ℝ, x ≤ 0 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx with h | h
    · exact deriv_smoothTransition_of_lt_zero h
    · rw [h]; exact deriv_smoothTransition_at_zero
  have hright : ∀ x : ℝ, 1 ≤ x → deriv Real.smoothTransition x = 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx with h | h
    · exact deriv_smoothTransition_of_one_lt h
    · rw [← h]; exact deriv_smoothTransition_at_one
  refine ⟨hleft, hright, ?_⟩
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rcases le_or_gt x 0 with hx | hx
  · rw [hleft x hx, abs_zero]
    exact le_max_right _ _
  · rcases le_or_gt 1 x with hx1 | hx1
    · rw [hright x hx1, abs_zero]
      exact le_max_right _ _
    · have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx, le_of_lt hx1⟩
      have hb := hC x hxI
      rw [Real.norm_eq_abs] at hb
      exact le_trans hb (le_max_left _ _)

end Work.H2.T1Q
