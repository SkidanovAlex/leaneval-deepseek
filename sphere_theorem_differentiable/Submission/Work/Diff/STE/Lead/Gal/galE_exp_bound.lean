import Mathlib
import Submission.Work.Diff.STE.gronwall_linear_bound
import Submission.Work.Diff.STE.flat.energy_apriori

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

/-- The linear comparison step underlying `galE_exp_bound`: if `y` has derivative `y'` on `[0,T)`
and `y' ≤ M` there, then `t ↦ M * t - y t` is nondecreasing on `[0,T)`, whence
`y t ≤ y 0 + M * t` for every `t ∈ [0,T)`. -/
private lemma galE_linear_bound {y y' : ℝ → ℝ} {T M : ℝ}
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Ico (0 : ℝ) T, y' t ≤ M) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, y t ≤ y 0 + M * t := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt ht0 ht.2
  -- The auxiliary function `s ↦ M * s - y s` and its derivative on `[0,T)`.
  have hderiv_aux : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => M * s - y s) (M - y' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => M * s) M s := by
      simpa using (hasDerivAt_id s).const_mul M
    exact h1.sub (hderiv s hs)
  have hcont : ContinuousOn (fun s : ℝ => M * s - y s) (Set.Ico (0 : ℝ) T) :=
    fun s hs => ((hderiv_aux s hs).continuousAt).continuousWithinAt
  have hdw : ∀ s ∈ interior (Set.Ico (0 : ℝ) T),
      HasDerivWithinAt (fun s : ℝ => M * s - y s) (M - y' s) (interior (Set.Ico (0 : ℝ) T)) s :=
    fun s hs => (hderiv_aux s (interior_subset hs)).hasDerivWithinAt
  have hnonneg : ∀ s ∈ interior (Set.Ico (0 : ℝ) T), 0 ≤ M - y' s := by
    intro s hs
    have hs' : y' s ≤ M := hineq s (interior_subset hs)
    linarith
  have hmono : MonotoneOn (fun s : ℝ => M * s - y s) (Set.Ico (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 T) hcont hdw hnonneg
  have h0mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_refl 0, hT0⟩
  have h := hmono h0mem ht ht0
  -- `h : M * 0 - y 0 ≤ M * t - y t`
  linarith

/-- **The exponential bound from a one-sided constant bound on the derivative.**  If
`y : ℝ → ℝ` is differentiable on `[0,T)` with derivative `y'`, satisfies the *one-sided constant*
differential inequality `y' t ≤ M` there with `0 ≤ M` (a growth rate), and has `y 0 ≥ 0`, then

  `y t ≤ (y 0 + 1) * Real.exp (M * t) - 1`   for every `t ∈ Set.Ico 0 T`.

This is the comparison step of the a priori energy estimate `galE_apriori`: the energy
`y = galE (c ·)` of the Galerkin trajectory grows at most linearly with the uniform rate `M`, and the
target conclusion is the exponential form with `C = M`.

Proof: `t ↦ y t - M * t` is nonincreasing on `[0,T)` (its derivative `y' t - M ≤ 0`; use the
`HasDerivAt` monotonicity lemmas, e.g. `monotoneOn_of_deriv_nonneg` on `fun t => -(y t - M * t)`, or
`Convex.norm_image_sub_le`-style), so `y t ≤ y 0 + M * t`; and `M * t + y 0 + 1 ≤ (y 0 + 1) * exp (M*t)`
because for `s = M * t ≥ 0` one has `exp s - 1 ≥ s` and `y 0 + 1 ≥ 1`, so
`M t = s ≤ (y 0 + 1) * (exp s - 1)`.  (Both `HasDerivAt`-on-`Ico` hypotheses match the consumer; the
`hM : 0 ≤ M` hypothesis is essential: `y t = 1 - t`, `M = -1` is a counterexample without it.) -/
theorem galE_exp_bound {y y' : ℝ → ℝ} {T M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Ico (0 : ℝ) T, y' t ≤ M)
    (h0 : 0 ≤ y 0) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, y t ≤ (y 0 + 1) * Real.exp (M * t) - 1 := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have hlin : y t ≤ y 0 + M * t := galE_linear_bound hderiv hineq t ht
  -- `M * t ≥ 0` and `M * t ≤ exp (M * t) - 1`.
  have hMt : 0 ≤ M * t := mul_nonneg hM ht0
  have hexp_ge : M * t ≤ Real.exp (M * t) - 1 := by
    have := Real.add_one_le_exp (M * t)
    linarith
  have hnonneg : 0 ≤ Real.exp (M * t) - 1 := le_trans hMt hexp_ge
  have hone : (1 : ℝ) ≤ y 0 + 1 := by linarith
  have hkey : M * t ≤ (y 0 + 1) * (Real.exp (M * t) - 1) :=
    calc M * t ≤ Real.exp (M * t) - 1 := hexp_ge
      _ = 1 * (Real.exp (M * t) - 1) := (one_mul _).symm
      _ ≤ (y 0 + 1) * (Real.exp (M * t) - 1) :=
          mul_le_mul_of_nonneg_right hone hnonneg
  have hid : (y 0 + 1) * (Real.exp (M * t) - 1) + y 0
      = (y 0 + 1) * Real.exp (M * t) - 1 := by ring
  linarith

end Work.Diff.STE.Lead.Gal
