import Mathlib

namespace Work.SimplyConnected.ABS

open Filter Asymptotics
open scoped Topology

/-- **The second-order Taylor remainder of a function analytic at a point.**
If `g : ℂ → ℂ` is complex analytic at `w₀`, then the first-order Taylor remainder
`g (w₀ + v) - g w₀ - deriv g w₀ * v` is `O (‖v‖ ^ 2)` near `v = 0`: there is `C` with
`‖g (w₀ + v) - g w₀ - deriv g w₀ * v‖ ≤ C * ‖v‖ ^ 2` for `v` close to `0`. -/
theorem quadraticRemainder_of_analyticAt {g : ℂ → ℂ} {w₀ : ℂ} (hg : AnalyticAt ℂ g w₀) :
    ∃ C : ℝ, ∀ᶠ v in nhds (0 : ℂ),
      ‖g (w₀ + v) - g w₀ - deriv g w₀ * v‖ ≤ C * ‖v‖ ^ 2 := by
  rcases hg with ⟨p, hp⟩
  -- `hp.isBigO_image_sub_norm_mul_norm_sub` bounds `g y - g z - p 1 (y - z)` by
  -- `‖(y,z) - (w₀,w₀)‖ * ‖y - z‖`; evaluate at `(w₀ + v, w₀)`.
  have hmain := hp.isBigO_image_sub_norm_mul_norm_sub
  rw [Asymptotics.isBigO_iff] at hmain
  obtain ⟨C, hC⟩ := hmain
  refine ⟨C, ?_⟩
  have hcont : Continuous fun v : ℂ => (w₀ + v, w₀) := by fun_prop
  have hmap : Tendsto (fun v : ℂ => (w₀ + v, w₀)) (𝓝 0) (𝓝 (w₀, w₀)) := by
    simpa using hcont.tendsto 0
  filter_upwards [hmap.eventually hC] with v hv
  simp only [add_sub_cancel_left, Prod.mk_sub_mk, sub_self, norm_zero, Prod.norm_def,
    max_eq_left (norm_nonneg v)] at hv
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg v))] at hv
  -- identify the first-order term `p 1 (fun _ => v)` with `deriv g w₀ * v`
  have h1 : p 1 (fun _ => v) = deriv g w₀ * v := by
    have hfin : (fun _ : Fin 1 => v) = Fin.snoc 0 v := by
      funext i; fin_cases i; simp
    rw [hfin, ← continuousMultilinearCurryFin1_apply (𝕜 := ℂ) (p 1) v, ← hp.fderiv_eq]
    rw [← toSpanSingleton_deriv]
    simp [ContinuousLinearMap.toSpanSingleton_apply]
    ring
  rw [h1] at hv
  calc ‖g (w₀ + v) - g w₀ - deriv g w₀ * v‖
      ≤ C * (‖v‖ * ‖v‖) := hv
    _ = C * ‖v‖ ^ 2 := by ring

end Work.SimplyConnected.ABS
