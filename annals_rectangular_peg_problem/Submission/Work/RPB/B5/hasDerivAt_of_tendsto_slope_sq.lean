import Mathlib

namespace Work.RPB.B5

/-- If `Q` is differentiable at `0` and the slope of `Q` at `0` evaluated on
squares `r ↦ r ^ 2` tends to `d` along `r → 0⁺`, then the derivative of `Q`
at `0` is `d`.

The hypothesis only probes `Q` at points `r ^ 2 ≥ 0`, i.e. it controls the
right-hand difference quotient.  Since `Q` is differentiable at `0`, the
two-sided difference quotient has a limit; restricting it to `x → 0⁺` and
substituting `x = r ^ 2` shows that this limit equals `d`. -/
lemma hasDerivAt_of_tendsto_slope_sq {Q : ℝ → ℝ} {d : ℝ} (hQ : DifferentiableAt ℝ Q 0)
    (h : Filter.Tendsto (fun r : ℝ => (Q (r ^ 2) - Q 0) / r ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)) :
    HasDerivAt Q d 0 := by
  -- Rewrite the hypothesis as the right-hand limit of the difference quotient.
  have hright : Filter.Tendsto (fun x : ℝ => (Q x - Q 0) / x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d) := by
    have hcomp : Filter.Tendsto
        ((fun x : ℝ => (Q x - Q 0) / x) ∘ fun r : ℝ => r ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d) := h
    -- `r ↦ √x` sends `0⁺` to `0⁺`
    have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Filter.Tendsto Real.sqrt (nhds (0:ℝ)) (nhds (0:ℝ)) := by
          simpa using (Real.continuous_sqrt.continuousAt (x := (0:ℝ))).tendsto
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact Real.sqrt_pos.mpr hx
    have hcomp2 : Filter.Tendsto
        (((fun x : ℝ => (Q x - Q 0) / x) ∘ fun r : ℝ => r ^ 2) ∘ fun x : ℝ => Real.sqrt x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d) := hcomp.comp hsqrt
    -- `(√x) ^ 2 = x` on `0⁺`
    refine Filter.Tendsto.congr' ?_ hcomp2
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Function.comp_apply]
    rw [Real.sq_sqrt hx.le]
  -- The (two-sided) difference quotient of `Q` at `0` also has a right-hand limit.
  have hleft : Filter.Tendsto (fun x : ℝ => (Q x - Q 0) / x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv Q 0)) := by
    have hm : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) ({0} : Set ℝ)ᶜ :=
      nhdsWithin_mono _ (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx)
    have hs : Filter.Tendsto (fun t : ℝ => t⁻¹ • (Q (0 + t) - Q 0))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (deriv Q 0)) :=
      hQ.hasDerivAt.tendsto_slope_zero.mono_left hm
    refine Filter.Tendsto.congr (fun x => ?_) hs
    rw [zero_add, div_eq_inv_mul, smul_eq_mul]
  -- Uniqueness of limits gives `d = Q'(0)`.
  have hd : d = deriv Q 0 := tendsto_nhds_unique hright hleft
  rw [hd]
  exact hQ.hasDerivAt

end Work.RPB.B5
