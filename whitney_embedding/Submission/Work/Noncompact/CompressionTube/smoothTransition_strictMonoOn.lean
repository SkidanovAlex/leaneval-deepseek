import Mathlib

/-!
# Strict monotonicity of `Real.smoothTransition` on `(0,1)`

`Real.smoothTransition` is Mathlib's smooth step function
`x ↦ expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`.  Mathlib proves it is
`Monotone` (`Real.smoothTransition.monotone`), but not that it is *strictly* monotone on `(0,1)`,
which is what makes the clamped reparametrisation

  `φ s := s - η + η * Real.smoothTransition ((s - a) / b)`

(used to splice a straight germ of length `η` onto an immersed arc in
`Work.Noncompact.CompressionTube.immersedLine_of_canal`) *injective*, and hence the spliced piece an
injection on its parameter interval.

The proof unfolds the definition and reduces strict monotonicity to two strict/non-strict
comparisons of `expNegInvGlue`, the strict one being `exp ∘ (x ↦ -x⁻¹)` on `(0,∞)`.
-/

namespace Work.Noncompact.CompressionTube

open Set

/-- **`Real.smoothTransition` is strictly monotone on `(0,1)`.** -/
theorem strictMonoOn_smoothTransition : StrictMonoOn Real.smoothTransition (Set.Ioo (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hlt : expNegInvGlue x < expNegInvGlue y := by
    simp only [expNegInvGlue, if_neg (not_le.mpr hx.1), if_neg (not_le.mpr hy.1)]
    rw [Real.exp_lt_exp, neg_lt_neg_iff]
    simpa using one_div_lt_one_div_of_lt hx.1 hxy
  have hpos : 0 < expNegInvGlue (1 - y) := expNegInvGlue.pos_of_pos (by linarith [hy.2])
  simp only [Real.smoothTransition]
  rw [div_lt_div_iff₀ (Real.smoothTransition.pos_denom x) (Real.smoothTransition.pos_denom y)]
  simp only [mul_add, mul_comm (expNegInvGlue x) (expNegInvGlue y), add_lt_add_iff_left]
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt hpos)
    (mul_le_mul_of_nonneg_left (expNegInvGlue.monotone (by linarith [hx.1, hy.1]))
      (expNegInvGlue.nonneg _))

/-- The corresponding injectivity. -/
theorem injOn_smoothTransition_Ioo : Set.InjOn Real.smoothTransition (Set.Ioo (0:ℝ) 1) :=
  strictMonoOn_smoothTransition.injOn

/-- **The clamped reparametrisation is strictly monotone.**  For `0 ≤ η` and `0 < b`,
`s ↦ s - η + η * Real.smoothTransition ((s - a) / b)` is strictly monotone on any interval where
`s ↦ s - η` is: that is, on intervals contained in `{s | a ≤ s}` the strict monotonicity of
`smoothTransition` on `(0,1)` supplies the strictness. -/
theorem strictMonoOn_clamp {a b η : ℝ} (hb : 0 < b) (hη : 0 ≤ η)
    {s t : ℝ} (ha_s : a < s) (hst : s < t) (ha_t : t < a + b) :
    s - η + η * Real.smoothTransition ((s - a) / b) <
      t - η + η * Real.smoothTransition ((t - a) / b) := by
  have hs : (s - a) / b ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨div_pos (by linarith) hb, by rw [div_lt_one hb]; linarith⟩
  have ht : (t - a) / b ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨div_pos (by linarith) hb, by rw [div_lt_one hb]; linarith⟩
  have hst' : (s - a) / b < (t - a) / b := div_lt_div_of_pos_right (by linarith) hb
  have hmono := strictMonoOn_smoothTransition hs ht hst'
  nlinarith [hmono, hη]

end Work.Noncompact.CompressionTube
