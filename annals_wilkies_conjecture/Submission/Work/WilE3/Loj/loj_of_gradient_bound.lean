import Mathlib
import Submission.Work.WilE3.Loj.loj_tools
import Submission.Work.WilE3.Loj.infDist_le_of_descent_steps
import Submission.Work.WilE3.Loj.step_of_gradient_bound
import Submission.Work.WilE3.Loj.loj_bound_rpow

namespace Work.WilE3.Loj

set_option autoImplicit false
open Classical Topology Metric Filter
open scoped Topology

/-- For `0 ≤ R < d` there is `ε ∈ (0,1)` with `R / (1 - ε) < d`. -/
theorem exists_eps_div_one_sub_lt {R d : ℝ} (hR : 0 ≤ R) (hRd : R < d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ R / (1 - ε) < d := by
  have hd : 0 < d := lt_of_le_of_lt hR hRd
  have h2d : 0 < 2 * d := by linarith
  refine ⟨(d - R) / (2 * d), by positivity, ?_, ?_⟩
  · rw [div_lt_one h2d]
    linarith
  · have h1ε : 1 - (d - R) / (2 * d) = (d + R) / (2 * d) := by
      field_simp
      ring
    rw [h1ε, div_lt_iff₀ (by positivity)]
    have hmul : d * ((d + R) / (2 * d)) = (d + R) / 2 := by
      field_simp
    rw [hmul]
    linarith

/-- **Gabrielov 1995, p. 15: the gradient inequality integrates to the Łojasiewicz inequality.**
If a `C¹` function `g` with `g y = 0` satisfies `|∇g (x)| ≥ c |g x| ^ κ` near `y`, where `0 ≤ κ < 1`
and `c > 0`, then `|g x| ≥ a · dist (x, {g = 0}) ^ (1 / (1 - κ))` near `y`, with
`a ^ (1 - κ) = c * (1 - κ)`.  (Steepest descent along `-∇g / |∇g|`: the value drops like
`-c |g|^κ`, so the time — and hence the length — needed to reach `{g = 0}` is at most
`c⁻¹ (1-κ)⁻¹ |g x|^{1-κ}`.) -/
theorem loj_of_gradient_bound {k : ℕ} {g : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} (hgC1 : ContDiff ℝ 1 g)
    (hy : g y = 0) {c κ : ℝ} (hc : 0 < c) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hgrad : ∀ᶠ x in 𝓝 y, c * |g x| ^ κ ≤ ‖fderiv ℝ g x‖) :
    ∃ a : ℝ, 0 < a ∧ a ^ (1 - κ) = c * (1 - κ) ∧
      ∀ᶠ x in 𝓝 y, a * Metric.infDist x {z : Fin k → ℝ | g z = 0} ^ (1 / (1 - κ)) ≤ |g x| := by
  have hκp : 0 < 1 - κ := by linarith
  have hμ : 0 < c * (1 - κ) := mul_pos hc hκp
  obtain ⟨r, hr, hgrad'⟩ := Metric.eventually_nhds_iff.mp hgrad
  -- the value of `g` at the point of interest, and its zero set
  refine ⟨(c * (1 - κ)) ^ (1 / (1 - κ)), Real.rpow_pos_of_pos hμ _, ?_, ?_⟩
  · rw [← Real.rpow_mul (le_of_lt hμ), show (1 / (1 - κ)) * (1 - κ) = 1 by field_simp,
      Real.rpow_one]
  · rw [Metric.eventually_nhds_iff]
    refine ⟨r / 2, by linarith, fun x hx => ?_⟩
    -- `hx : dist x y < r / 2`
    have hexp : 0 < 1 / (1 - κ) := by positivity
    by_cases hgx : g x = 0
    · -- `x` is already a zero of `g`
      have hxZ : x ∈ {z : Fin k → ℝ | g z = 0} := hgx
      have h0 : Metric.infDist x {z : Fin k → ℝ | g z = 0} = 0 := by
        refine le_antisymm ?_ Metric.infDist_nonneg
        have := Metric.infDist_le_dist_of_mem (x := x) (y := x) hxZ
        simpa using this
      rw [h0, hgx]
      have hexp' : (1 : ℝ) / (1 - κ) ≠ 0 := ne_of_gt (by positivity)
      rw [Real.zero_rpow hexp', mul_zero, abs_zero]
    · -- the hard case: `g x ≠ 0`
      have hux : 0 < |g x| := abs_pos.mpr hgx
      have hZne : ({z : Fin k → ℝ | g z = 0} : Set (Fin k → ℝ)).Nonempty := ⟨y, hy⟩
      -- the descent bound: the zero set meets the ball of radius `|g x|^{1-κ} / (c(1-κ))`
      have hmain : Metric.infDist x {z : Fin k → ℝ | g z = 0} ≤
          |g x| ^ (1 - κ) / (c * (1 - κ)) := by
        by_contra hcon
        rw [not_le] at hcon
        -- notation
        set U : ℝ := |g x| ^ (1 - κ) with hU
        set d : ℝ := Metric.infDist x {z : Fin k → ℝ | g z = 0} with hd
        have hUpos : 0 < U := by rw [hU]; exact Real.rpow_pos_of_pos hux _
        have hUnn : 0 ≤ U := hUpos.le
        have hRnn : 0 ≤ U / (c * (1 - κ)) := div_nonneg hUnn hμ.le
        have hRd : U / (c * (1 - κ)) < d := hcon
        have hdnn : 0 ≤ d := by rw [hd]; exact Metric.infDist_nonneg
        -- a small slack so that the descent lands inside the zero-free ball
        obtain ⟨ε, hε0, hε1, hεd⟩ := exists_eps_div_one_sub_lt hRnn hRd
        have h1ε : 0 < 1 - ε := by linarith
        set μ' : ℝ := c * (1 - κ) * (1 - ε) with hμ'
        have hμ'pos : 0 < μ' := by rw [hμ']; positivity
        set R' : ℝ := U / μ' with hR'
        have hR'nn : 0 ≤ R' := by rw [hR']; exact div_nonneg hUnn hμ'pos.le
        have hR'd : R' < d := by
          rw [hR', hμ', hU]
          rw [show |g x| ^ (1 - κ) / (c * (1 - κ) * (1 - ε))
              = (|g x| ^ (1 - κ) / (c * (1 - κ))) / (1 - ε) from by rw [div_div]]
          exact hεd
        set δ' : ℝ := (R' + d) / 2 with hδ'
        have hδ'pos : 0 < δ' := by rw [hδ']; linarith
        have hR'δ' : R' < δ' := by rw [hδ']; linarith
        have hδ'd : δ' < d := by rw [hδ']; linarith
        -- `g` has no zeros in the ball `B̄(x,δ')`
        have hnz : ∀ z ∈ Metric.closedBall x δ', g z ≠ 0 := by
          intro z hz hgz
          have h1 : d ≤ dist x z := by
            rw [hd]
            exact Metric.infDist_le_dist_of_mem hgz
          have h2 : dist x z ≤ δ' := by simpa [Metric.mem_closedBall, dist_comm] using hz
          linarith
        -- the gradient bound holds on `B̄(x,δ')`
        have hgrad'' : ∀ z ∈ Metric.closedBall x δ', c * |g z| ^ κ ≤ ‖fderiv ℝ g z‖ := by
          intro z hz
          have h2 : dist x z ≤ δ' := by simpa [Metric.mem_closedBall, dist_comm] using hz
          have hdist : dist z y < r := by
            have hdy : dist x y < r / 2 := hx
            have hdx : d ≤ dist x y := by
              rw [hd]
              exact Metric.infDist_le_dist_of_mem hy
            calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
              _ = dist x z + dist x y := by rw [dist_comm z x]
              _ < δ' + r / 2 := by linarith
              _ < r / 2 + r / 2 := by linarith
              _ = r := by ring
          exact hgrad' hdist
        -- the uniform descent step
        obtain ⟨h₀, hh₀pos, -, hstep⟩ := step_of_gradient_bound (g := g) (y := x) (δ := δ')
          (s := R') (c := c) (κ := κ) (ε := ε) hgC1 hc hκ0 hκ1 hε0 hε1 hR'nn hR'δ' hnz hgrad''
        -- the greedy descent reaches the zero set within `R'`
        have habs := infDist_le_of_descent_steps (F := fun z : Fin k → ℝ => |g z| ^ (1 - κ))
          (Z := {z : Fin k → ℝ | g z = 0}) (x := x) (ρ := R') (h₀ := h₀)
          (μ' := c * (1 - κ) * (1 - ε)) hμ'pos hh₀pos (le_of_eq rfl)
          (fun z => Real.rpow_nonneg (abs_nonneg _) _) (fun z hz => by
            have h := Real.rpow_eq_zero (abs_nonneg (g z)) (ne_of_gt hκp)
            rw [h] at hz
            exact (abs_eq_zero.mp hz)) (fun z hz hzpos => by
              obtain ⟨dd, hdd1, -, hdd3⟩ := hstep z hz
              exact ⟨h₀, ⟨hh₀pos, le_rfl⟩, dd, hdd1, hdd3, Or.inl rfl⟩)
        rw [← hR'] at habs
        linarith [habs, hR'd, hd]
      exact loj_bound_rpow hc hκ0 hκ1 (abs_nonneg (g x)) Metric.infDist_nonneg hmain

end Work.WilE3.Loj
