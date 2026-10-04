import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A Sturm/Wronskian lower bound for the logarithmic derivative

Let `r > 0` satisfy the differential *inequality* `r'' + c² r ≥ 0` on `(0,T)`, and suppose that the
Wronskian of `r` against the model solution `sin (c t)` of the equation `y'' + c² y = 0`,

`W t = r' t * sin (c t) - r t * (c * cos (c t))`,

tends to `0` at `0⁺`.  Then, on `(0,T)`,

`c * cot (c * t) ≤ r' t / r t`,

i.e. `(log r)' ≥ (log sin (c ·))'` there: `r` grows at least as fast as the model solution.

This is the classical Wronskian comparison ("Sturm" / Riccati comparison) in the form used for the
Rauch comparison theorem.  The proof: differentiating the Wronskian gives

`W' t = sin (c t) * (r'' t + c² r t) ≥ 0`  on `(0,T)`

(since `0 < c * t < π` there), so `W` is monotone on `(0,T)`; as `W → 0` at `0⁺`, `W ≥ 0` on `(0,T)`
(monotonicity plus the limit).  Dividing by `r t * sin (c t) > 0` concludes.

Note the hypothesis on the boundary behaviour is only `W → 0`: no normalisation of `r` at `0` is
assumed (compare `Commons.Analysis.ODE.sturm_model_lower_bound_general`, which additionally needs
`r / (sin (c·)/c) → 1`).
-/

namespace Work.Diff.C

/-- **Log-derivative comparison with `cot`.**  See the module docstring. -/
theorem log_deriv_lower {r r' : ℝ → ℝ} {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hcT : c * T ≤ Real.pi)
    (hr : ∀ t ∈ Set.Ioo 0 T, HasDerivAt r (r' t) t)
    (hr2 : ∀ t ∈ Set.Ioo 0 T, HasDerivAt r' (deriv r' t) t)
    (hpos : ∀ t ∈ Set.Ioo 0 T, 0 < r t)
    (hineq : ∀ t ∈ Set.Ioo 0 T, 0 ≤ deriv r' t + c ^ 2 * r t)
    (hlim : Filter.Tendsto
      (fun t : ℝ => r' t * Real.sin (c * t) - r t * (c * Real.cos (c * t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ t ∈ Set.Ioo 0 T, c * Real.cot (c * t) ≤ r' t / r t := by
  intro t ht
  -- `W` is the Wronskian of `r` against the model solution `t ↦ sin (c t)`.
  let N : ℝ → ℝ := fun s => r' s * Real.sin (c * s) - r s * (c * Real.cos (c * s))
  -- `sin (c s) > 0` on `(0,T)`, because `0 < c * s < c * T ≤ π`.
  have hsinpos : ∀ s ∈ Set.Ioo 0 T, 0 < Real.sin (c * s) := by
    intro s hs
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1, hc]) (by nlinarith [hs.2, hc, hcT])
  -- `W' s = sin (c s) * (r'' s + c² r s)`.
  have hN : ∀ s ∈ Set.Ioo 0 T,
      HasDerivAt N (Real.sin (c * s) * (deriv r' s + c ^ 2 * r s)) s := by
    intro s hs
    have hlin : HasDerivAt (fun z : ℝ => c * z) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    have hsin : HasDerivAt (fun z : ℝ => Real.sin (c * z)) (Real.cos (c * s) * c) s :=
      (Real.hasDerivAt_sin (c * s)).comp s hlin
    have hcos : HasDerivAt (fun z : ℝ => Real.cos (c * z)) (-Real.sin (c * s) * c) s :=
      (Real.hasDerivAt_cos (c * s)).comp s hlin
    have h1 : HasDerivAt (fun z : ℝ => r' z * Real.sin (c * z))
        (deriv r' s * Real.sin (c * s) + r' s * (Real.cos (c * s) * c)) s :=
      (hr2 s hs).mul hsin
    have h2 : HasDerivAt (fun z : ℝ => r z * (c * Real.cos (c * z)))
        (r' s * (c * Real.cos (c * s)) + r s * (c * (-Real.sin (c * s) * c))) s :=
      (hr s hs).mul (hcos.const_mul c)
    convert h1.sub h2 using 1
    ring
  -- hence `W` is nondecreasing on `(0,T)`.
  have hmono : MonotoneOn N (Set.Ioo 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 T) ?_ ?_ ?_
    · intro x hx
      exact (hN x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      intro x hx
      exact (hN x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro x hx
      rw [(hN x hx).deriv]
      exact mul_nonneg (le_of_lt (hsinpos x hx)) (hineq x hx)
  -- monotonicity on `(0,T)` together with the limit `W → 0` at `0⁺` forces `W ≥ 0` on `(0,T)`.
  have hNt : 0 ≤ N t := by
    have hIio : Set.Iio t ∈ nhdsWithin 0 (Set.Ioi 0) := nhdsWithin_le_nhds (Iio_mem_nhds ht.1)
    have hev : ∀ᶠ y in (nhdsWithin 0 (Set.Ioi 0)), N y ≤ N t := by
      filter_upwards [hIio, self_mem_nhdsWithin] with y hyt hypos
      exact hmono ⟨hypos, lt_trans hyt ht.2⟩ ht (le_of_lt hyt)
    exact le_of_tendsto hlim hev
  have hNt' : 0 ≤ r' t * Real.sin (c * t) - r t * (c * Real.cos (c * t)) := hNt
  -- divide `W ≥ 0` by `r t * sin (c t) > 0` to get the claim
  rw [Real.cot_eq_cos_div_sin, ← mul_div_assoc]
  rw [div_le_div_iff₀ (hsinpos t ht) (hpos t ht)]
  rw [mul_comm (c * Real.cos (c * t)) (r t)]
  linarith [hNt']

end Work.Diff.C
