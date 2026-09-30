import Mathlib
import Submission.Work.BMF.smoothing_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory

/-- Change of variables `s = t / A` for the total-variation integral of the derivative of the
smooth bump `Work.BMF.bumpFn` from `Submission/Work/BMF/smoothing_exists.lean`.

`Work.BMF.bumpFn` is smooth, is `1` on `[1/2, 2]` and vanishes identically outside `[1/4, 4]`, so
`deriv bumpFn s = 0` for every `s > 4` (lemma `deriv_bumpFn_eq_zero_of_gt`).  Hence for `A > 0` and
`N ≥ 4A` (so that `N/A ≥ 4`) the integral over `0..N` of `‖deriv bumpFn (t/A)‖ / A` — the total
variation of `t ↦ bumpFn (t/A)` over `[0,N]` — collapses to the fixed constant
`∫_0^4 ‖deriv bumpFn s‖ ds`, independent of `A` and `N`. -/
theorem deriv_bumpFn_weighted_integral_eq (A N : ℝ) (hA : 0 < A) (hN : 4 * A ≤ N) :
    ∫ t in (0 : ℝ)..N, ‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A
      = ∫ s in (0 : ℝ)..4, ‖(deriv Work.BMF.bumpFn s : ℝ)‖ := by
  have hcd : Continuous (deriv Work.BMF.bumpFn) :=
    (Work.BMF.bumpFn_contDiff 1).continuous_deriv (by norm_num)
  have hcont : Continuous (fun s : ℝ => ‖(deriv Work.BMF.bumpFn s : ℝ)‖) := by
    simpa using hcd.norm
  have hzero : ∀ s : ℝ, 4 < s → ‖(deriv Work.BMF.bumpFn s : ℝ)‖ = 0 := by
    intro s hs
    rw [Work.BMF.deriv_bumpFn_eq_zero_of_gt hs, norm_zero]
  have hle : (4 : ℝ) ≤ N / A := (le_div_iff₀ hA).mpr hN
  have hstep1 : (∫ t in (0 : ℝ)..N, ‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A)
      = (∫ t in (0 : ℝ)..N, ‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖) / A := by
    rw [intervalIntegral.integral_div]
  have hstep2 : (∫ t in (0 : ℝ)..N, ‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖) / A
      = ∫ s in (0 : ℝ)..(N / A), ‖(deriv Work.BMF.bumpFn s : ℝ)‖ := by
    rw [intervalIntegral.integral_comp_div
      (f := fun s : ℝ => ‖(deriv Work.BMF.bumpFn s : ℝ)‖) hA.ne']
    rw [zero_div, smul_eq_mul, mul_div_cancel_left₀ _ hA.ne']
  have htail : (∫ x in (4 : ℝ)..(N / A), ‖(deriv Work.BMF.bumpFn x : ℝ)‖) = 0 := by
    have hcongr := intervalIntegral.integral_congr_ae (μ := MeasureTheory.volume) (a := (4 : ℝ))
      (b := N / A) (f := fun x : ℝ => ‖(deriv Work.BMF.bumpFn x : ℝ)‖)
      (g := fun _ : ℝ => (0 : ℝ))
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Set.uIoc_of_le hle] at hx
        exact hzero x hx.1))
    rw [hcongr]; simp
  have hstep3 : (∫ s in (0 : ℝ)..(N / A), ‖(deriv Work.BMF.bumpFn s : ℝ)‖)
      = ∫ s in (0 : ℝ)..4, ‖(deriv Work.BMF.bumpFn s : ℝ)‖ := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 4)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 4 (N / A))
    rw [htail, add_zero] at hsplit
    exact hsplit.symm
  rw [hstep1, hstep2, hstep3]

end Work.BMF.mr_direct
