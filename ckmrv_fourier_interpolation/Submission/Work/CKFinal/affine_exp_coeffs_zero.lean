import Mathlib

namespace Work.CKFinal

open Filter

/-- **Affine (degree ≤ 1) complex functions cannot vanish at `+∞`.**
If `t ↦ u + t • v` tends to `0` along `t → +∞`, then `u = v = 0`.
(Compare the values at `t + 1` and `t`: their difference is the constant `v`.) -/
lemma affine_complex_tendsto_zero {u v : ℂ}
    (h : Tendsto (fun t : ℝ => u + (t : ℂ) * v) atTop (nhds 0)) : u = 0 ∧ v = 0 := by
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have h1 : Tendsto (fun t : ℝ => u + ((t + 1 : ℝ) : ℂ) * v) atTop (nhds 0) := h.comp hshift
  have hsub := h1.sub h
  rw [sub_zero] at hsub
  have hv : Tendsto (fun _ : ℝ => v) atTop (nhds 0) :=
    hsub.congr (fun t => by push_cast; ring)
  have hv0 : v = 0 := tendsto_const_nhds_iff.mp hv
  have hu : Tendsto (fun _ : ℝ => u) atTop (nhds 0) :=
    h.congr (fun t => by rw [hv0, mul_zero, add_zero])
  exact ⟨tendsto_const_nhds_iff.mp hu, hv0⟩

/-- `t ↦ exp (-(k * t))` tends to `0` at `+∞` for `k > 0`. -/
lemma exp_neg_mul_tendsto_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => Real.exp (-(k * t))) atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 k hk
  simpa [Real.rpow_zero, neg_mul] using h

/-- `t ↦ t * exp (-(k * t))` tends to `0` at `+∞` for `k > 0`. -/
lemma mul_exp_neg_mul_tendsto_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => t * Real.exp (-(k * t))) atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 k hk
  simpa [Real.rpow_one, neg_mul] using h

/-- An affine complex function times a decaying exponential tends to `0` at `+∞`. -/
lemma poly_exp_tendsto_zero (A B : ℂ) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => (A + (t : ℂ) * Complex.I * B) * Complex.exp (-(↑(k * t) : ℂ)))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto (fun t : ℝ => (‖A‖ + |t| * ‖B‖) * Real.exp (-(k * t))) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => ‖A‖ * Real.exp (-(k * t))) atTop (nhds 0) := by
      simpa using (exp_neg_mul_tendsto_zero hk).const_mul ‖A‖
    have h2 : Tendsto (fun t : ℝ => |t| * Real.exp (-(k * t))) atTop (nhds 0) := by
      refine (mul_exp_neg_mul_tendsto_zero hk).congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [abs_of_nonneg ht]
    have h3 : Tendsto (fun t : ℝ => ‖B‖ * (|t| * Real.exp (-(k * t)))) atTop (nhds 0) := by
      simpa using h2.const_mul ‖B‖
    have h4 := h1.add h3
    rw [add_zero] at h4
    refine h4.congr (fun t => ?_)
    ring
  refine squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) ?_ hg
  refine Eventually.of_forall (fun t => ?_)
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc ‖A + (t : ℂ) * Complex.I * B‖ ≤ ‖A‖ + ‖(t : ℂ) * Complex.I * B‖ := norm_add_le _ _
    _ = ‖A‖ + |t| * ‖B‖ := by rw [norm_mul, norm_mul]; simp

/-- **Vanishing of the affine-exponential coefficients.**  If the function
`t ↦ a + (i t) b + e^{2πt}(c + (i t) d)` tends to `0` along `t → +∞`, then all four complex
coefficients vanish.  (Multiply by `e^{-2πt}`, so that `c + i t d → 0`; a non-constant affine
function cannot tend to `0` at `+∞`, and a constant one can only tend to `0`.) -/
theorem affine_exp_coeffs_zero {a b c d : ℂ}
    (h : Filter.Tendsto (fun t : ℝ => a + ((t : ℂ) * Complex.I) * b
        + Complex.exp (2 * Real.pi * t) * (c + ((t : ℂ) * Complex.I) * d))
      Filter.atTop (nhds 0)) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hk : 0 < 2 * Real.pi := by positivity
  have hce : ∀ t : ℝ,
      Complex.exp (-(↑((2 * Real.pi) * t) : ℂ)) = ((Real.exp (-((2 * Real.pi) * t))) : ℂ) := by
    intro t
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have he : Tendsto (fun t : ℝ => Complex.exp (-(↑((2 * Real.pi) * t) : ℂ))) atTop (nhds 0) := by
    have hreal : Tendsto (fun t : ℝ => Real.exp (-((2 * Real.pi) * t))) atTop (nhds 0) :=
      exp_neg_mul_tendsto_zero hk
    have hcf : Tendsto (fun t : ℝ => ((Real.exp (-((2 * Real.pi) * t))) : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    exact hcf.congr (fun t => (hce t).symm)
  have hG : Tendsto (fun t : ℝ => Complex.exp (-(↑((2 * Real.pi) * t) : ℂ)) * (a
      + ((t : ℂ) * Complex.I) * b
      + Complex.exp (2 * Real.pi * t) * (c + ((t : ℂ) * Complex.I) * d))) atTop (nhds 0) := by
    have := he.mul h
    simpa using this
  have hexpc : ∀ t : ℝ,
      Complex.exp (-(↑((2 * Real.pi) * t) : ℂ)) * Complex.exp (2 * Real.pi * t) = 1 := by
    intro t
    rw [← Complex.exp_add]
    rw [show -(↑((2 * Real.pi) * t) : ℂ) + (2 * Real.pi * t : ℂ) = 0 by
      push_cast; ring, Complex.exp_zero]
  have hunit : ∀ (t : ℝ) (X : ℂ),
      Complex.exp (-(↑((2 * Real.pi) * t) : ℂ)) * (Complex.exp (2 * Real.pi * t) * X) = X := by
    intro t X
    rw [← mul_assoc, hexpc t, one_mul]
  have hG' : Tendsto (fun t : ℝ => (a + ((t : ℂ) * Complex.I) * b)
      * Complex.exp (-(↑((2 * Real.pi) * t) : ℂ))
      + (c + ((t : ℂ) * Complex.I) * d)) atTop (nhds 0) := by
    refine hG.congr (fun t => ?_)
    rw [mul_add, mul_add, hunit t (c + ((t : ℂ) * Complex.I) * d)]
    ring
  have hlin : Tendsto (fun t : ℝ => (a + ((t : ℂ) * Complex.I) * b)
      * Complex.exp (-(↑((2 * Real.pi) * t) : ℂ))) atTop (nhds 0) :=
    poly_exp_tendsto_zero a b (k := 2 * Real.pi) hk
  have hcd : Tendsto (fun t : ℝ => c + ((t : ℂ) * Complex.I) * d) atTop (nhds 0) := by
    have hh := hG'.sub hlin
    rw [sub_zero] at hh
    refine hh.congr (fun t => ?_)
    ring
  obtain ⟨hc0, hId0⟩ := affine_complex_tendsto_zero (u := c) (v := Complex.I * d) (by
    simpa only [mul_assoc] using hcd)
  have hd0 : d = 0 := by
    rcases mul_eq_zero.mp hId0 with hh | hh
    · exact absurd hh Complex.I_ne_zero
    · exact hh
  have hf : Tendsto (fun t : ℝ => a + ((t : ℂ) * Complex.I) * b) atTop (nhds 0) := by
    refine h.congr (fun t => ?_)
    rw [hc0, hd0]
    ring
  obtain ⟨ha0, hIb0⟩ := affine_complex_tendsto_zero (u := a) (v := Complex.I * b) (by
    simpa only [mul_assoc] using hf)
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hIb0 with hh | hh
    · exact absurd hh Complex.I_ne_zero
    · exact hh
  exact ⟨ha0, hb0, hc0, hd0⟩

end Work.CKFinal
