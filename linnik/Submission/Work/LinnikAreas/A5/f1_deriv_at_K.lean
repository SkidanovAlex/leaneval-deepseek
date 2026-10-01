import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

open Filter
open scoped Topology

namespace Work.LinnikAreas.A5

/-
HB's test function `f₁` (Lemma 13.3) is

  `f1 K lam t = sinh ((K - t) * lam)` for `t ≤ K`, and `0` for `t ≥ K`.

For `lam ≠ 0` this has a genuine *corner* at `t = K`:

* from the left, `f1 K lam` agrees on `(-∞,K)` with `t ↦ sinh ((K-t)*lam)`, whose
  derivative at `K` is `-lam` (the chain rule: `cosh 0 · (-lam) = -lam`);
* from the right, `f1 K lam` is identically `0`, so the right-hand slope is `0`.

Two different one-sided limits `-lam ≠ 0` mean `f1 K lam` is **not** differentiable at
`K`, and Mathlib's `deriv` — a total function returning `0` off the differentiability
set — therefore vanishes there: `deriv (f1 K lam) K = 0`.

The proof below makes this precise: assuming differentiability, the two-sided
`HasDerivAt` splits (`hasDerivAt_iff_tendsto_slope_left_right`) into a left and a right
slope limit, which we identify as `-lam` and `0` respectively, contradicting `lam ≠ 0`.
-/

/-- Left-substitution form of the chain rule used for `f₁`: the derivative of
`t ↦ sinh ((K - t) * lam)` at `t = K` is `-lam`. -/
lemma hasDerivAt_sinh_comp (K lam : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sinh ((K - t) * lam)) (-lam) K := by
  have h1 : HasDerivAt (fun t : ℝ => K - t) (-1) K := (hasDerivAt_id K).const_sub K
  have h2 : HasDerivAt (fun t : ℝ => (K - t) * lam) (-lam) K := by
    simpa using h1.mul_const lam
  have h3 := (Real.hasDerivAt_sinh ((K - K) * lam)).comp K h2
  rw [show (K - K) * lam = 0 by ring] at h3
  simpa only [Function.comp_def, Real.cosh_zero, one_mul] using h3

theorem f1_deriv_at_K (K lam : ℝ) (hlam : lam ≠ 0) :
    deriv (Work.LinnikAreas.A5.f1 K lam) K = 0 := by
  -- Every `lam ≠ 0` makes `K` a corner of `f₁`, hence a non-differentiability point.
  have hnd : ¬ DifferentiableAt ℝ (f1 K lam) K := by
    intro hd
    obtain ⟨hleft, hright⟩ := hasDerivAt_iff_tendsto_slope_left_right.mp hd.hasDerivAt
    -- Right side: on `(K, ∞)` the function is identically `0`, so its slope is too.
    have hr : Tendsto (slope (f1 K lam) K) (𝓝[>] K) (𝓝 0) := by
      have he : (fun t => slope (f1 K lam) K t) =ᶠ[𝓝[>] K] (fun _ => (0:ℝ)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [slope_def_field, f1_of_ge (le_of_lt ht), f1_of_ge le_rfl, sub_zero, zero_div]
      exact tendsto_const_nhds.congr' he.symm
    -- Hence the (two-sided) derivative would be `0`.
    have hc0 : deriv (f1 K lam) K = 0 := tendsto_nhds_unique hright hr
    -- Left side: on `(-∞, K)` the function is `t ↦ sinh ((K-t)*lam)`, slope limit `-lam`.
    have hgl : Tendsto (slope (fun t : ℝ => Real.sinh ((K - t) * lam)) K) (𝓝[<] K)
        (𝓝 (-lam)) :=
      (hasDerivAt_iff_tendsto_slope_left_right.mp (hasDerivAt_sinh_comp K lam)).1
    have heq : (fun t => slope (f1 K lam) K t)
        =ᶠ[𝓝[<] K] (fun t => slope (fun s : ℝ => Real.sinh ((K - s) * lam)) K t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field, slope_def_field, f1_of_le (le_of_lt ht), f1_of_ge le_rfl]
      simp
    have hl : Tendsto (slope (f1 K lam) K) (𝓝[<] K) (𝓝 (-lam)) := hgl.congr' heq.symm
    -- Hence the same derivative would be `-lam`, and `-lam ≠ 0` contradicts `hc0`.
    have hc1 : deriv (f1 K lam) K = -lam := tendsto_nhds_unique hleft hl
    rw [hc0] at hc1
    exact hlam (by linarith)
  exact deriv_zero_of_not_differentiableAt hnd

end Work.LinnikAreas.A5
