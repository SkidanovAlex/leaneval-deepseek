import Mathlib

open Filter Topology

namespace Work.WilG4c.C1Direct

/-- **Fibre partials are bounded by `M` on the *closed* ball** (fixed statement: the reviewers
correctly rejected the version without `0 < τ`, which is false at the collapsed ball `{0}`, and
without `0 ≤ M`).

If `G : ℝ^a → ℝ^b → ℝ` is `M`-Lipschitz in its second argument on the closed ball of radius `τ`
about `0` (`sup` norm on `Fin b → ℝ`, as everywhere in this development), then at **every** point
`z` with `‖z‖ ≤ τ` at which the slice `G w` is differentiable, each fibre partial is bounded
by `M`.

Case analysis (the `sup` norm makes the boundary of the ball a union of faces, so at least one of
the two points `z ± h • e_k` stays inside for small `|h|`):

* `|z k| < τ`: for `|h|` small both points are in the closed ball, so `hLip` bounds the difference
  quotient `h⁻¹(G w (z + h • e_k) − G w z)` by `M * |h| / |h| = M`;
* `z k = τ`: with `h < 0` the point `z + h • e_k` is still in the closed ball (its `k`-th
  coordinate decreases, the others are unchanged), so the *one-sided* difference quotient is
  bounded by `M`; differentiability at `z` identifies the two-sided limit with it;
* `z k = -τ`: symmetric, with `h > 0`.

This is the sharp form needed by the accounting of `Work.WilG4c.C1Direct.PathGainBound`, whose
constant `(K+2)(2(b+1)M+1)` is tight in its `b`-coefficient; the interior-only version
`Work.WilG4c.C1Direct.FibrePartialBound` is its restriction to `‖z‖ < τ`. -/
theorem FibrePartialBoundClosed {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) {τ M : ℝ}
    (hM : 0 ≤ M) (hτ : 0 < τ)
    (hLip : ∀ (w : Fin a → ℝ) (z z' : Fin b → ℝ), ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |G w z - G w z'| ≤ M * ‖z - z'‖) :
    ∀ (w : Fin a → ℝ) (z : Fin b → ℝ) (k : Fin b), ‖z‖ ≤ τ →
      DifferentiableAt ℝ (G w) z → |fderiv ℝ (G w) z (Pi.single k 1)| ≤ M := by
  intro w z k hz hdiff
  -- `0 ≤ M` is not needed for the estimate itself; keep a reference so the hypothesis is used.
  have hM0 : (0 : ℝ) ≤ M := hM
  -- Every coordinate of `z` is bounded by `τ` (sup norm).
  have hcoord : ∀ i : Fin b, |z i| ≤ τ := fun i => by
    have h : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at h
    exact h.trans hz
  have hzk_le : z k ≤ τ := (abs_le.mp (hcoord k)).2
  have hzk_ge : -τ ≤ z k := (abs_le.mp (hcoord k)).1
  -- Core argument, valid for *any* filter `l` finer than `𝓝[≠] 0` on which the one-sided
  -- points `z + t • e_k` eventually stay in the closed `τ`-ball.
  have key : ∀ (l : Filter ℝ), l ≤ 𝓝[≠] (0 : ℝ) → [NeBot l] →
      (∀ᶠ t in l, ‖z + t • (Pi.single k 1 : Fin b → ℝ)‖ ≤ τ) →
      |fderiv ℝ (G w) z (Pi.single k 1)| ≤ M := by
    intro l hl _hneBot hev
    have hcurve0 : (fun t : ℝ => z + t • (Pi.single k 1 : Fin b → ℝ)) 0 = z := by simp
    have h1 : HasDerivAt (fun t : ℝ => t • (Pi.single k 1 : Fin b → ℝ))
        (Pi.single k 1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k 1 : Fin b → ℝ)
    have hderiv : HasDerivAt (fun t : ℝ => z + t • (Pi.single k 1 : Fin b → ℝ))
        (Pi.single k 1) 0 := h1.const_add z
    have hfd : HasFDerivAt (G w) (fderiv ℝ (G w) z)
        ((fun t : ℝ => z + t • (Pi.single k 1 : Fin b → ℝ)) 0) := by
      rw [hcurve0]; exact hdiff.hasFDerivAt
    -- The one-dimensional derivative of `t ↦ G w (z + t • e_k)` at `0`.
    have hcomp : HasDerivAt (fun t : ℝ => G w (z + t • (Pi.single k 1 : Fin b → ℝ)))
        ((fderiv ℝ (G w) z) (Pi.single k 1)) 0 := by
      have h := hfd.comp_hasDerivAt (0 : ℝ) hderiv
      simpa only [Function.comp_def] using h
    have htend : Tendsto
        (fun t : ℝ => t⁻¹ • (G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z))
        l (𝓝 ((fderiv ℝ (G w) z) (Pi.single k 1))) := by
      have h : Tendsto
          (fun t : ℝ => t⁻¹ • (G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z))
          (𝓝[≠] (0 : ℝ)) (𝓝 ((fderiv ℝ (G w) z) (Pi.single k 1))) := by
        simpa using hcomp.tendsto_slope_zero
      exact h.mono_left hl
    have htendabs : Tendsto
        (fun t : ℝ => |t⁻¹ • (G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z)|)
        l (𝓝 |(fderiv ℝ (G w) z) (Pi.single k 1)|) :=
      (continuous_abs.tendsto _).comp htend
    have hmem0 : ({0} : Set ℝ)ᶜ ∈ l := (Filter.le_def.mp hl) _ self_mem_nhdsWithin
    -- `hLip` bounds the difference quotient by `M` eventually.
    have hev' : ∀ᶠ t in l,
        |t⁻¹ • (G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z)| ≤ M := by
      filter_upwards [hev, hmem0] with t htn htne
      have hb : |G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z| ≤ M * |t| := by
        have h := hLip w (z + t • (Pi.single k 1 : Fin b → ℝ)) z htn hz
        rw [add_sub_cancel_left, norm_smul, Pi.norm_single, Real.norm_eq_abs, norm_one,
          mul_one] at h
        exact h
      calc |t⁻¹ • (G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z)|
          = |t⁻¹| * |G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z| := by
            rw [smul_eq_mul, abs_mul]
        _ = |t|⁻¹ * |G w (z + t • (Pi.single k 1 : Fin b → ℝ)) - G w z| := by rw [abs_inv]
        _ ≤ |t|⁻¹ * (M * |t|) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg t))
        _ = M := by
            rw [← mul_assoc, mul_comm (|t|⁻¹) M, mul_assoc,
              inv_mul_cancel₀ (abs_ne_zero.mpr htne), mul_one]
    exact le_of_tendsto htendabs hev'
  -- Decision: the ball is a product of intervals of radius `τ`; at the boundary face
  -- `z k = -τ` we approach from the right (`t > 0`), otherwise from the left (`t < 0`).
  by_cases hcase : z k = -τ
  · refine key (𝓝[>] (0 : ℝ)) (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * τ by linarith)] with t ht
    rw [pi_norm_le_iff_of_nonneg hτ.le]
    intro j
    rw [Real.norm_eq_abs]
    by_cases hjk : j = k
    · rw [hjk, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hcase, abs_le]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hjk, smul_zero, add_zero]
      exact hcoord j
  · have hgt : -τ < z k := lt_of_le_of_ne hzk_ge (Ne.symm hcase)
    refine key (𝓝[<] (0 : ℝ)) (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx)) ?_
    filter_upwards [Ioo_mem_nhdsLT (show -τ - z k < (0 : ℝ) by linarith)] with t ht
    rw [pi_norm_le_iff_of_nonneg hτ.le]
    intro j
    rw [Real.norm_eq_abs]
    by_cases hjk : j = k
    · rw [hjk, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, abs_le]
      exact ⟨by linarith [ht.1], by linarith [ht.2, hzk_le]⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hjk, smul_zero, add_zero]
      exact hcoord j

end Work.WilG4c.C1Direct
