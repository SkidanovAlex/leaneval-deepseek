import Mathlib

namespace Work.Smooth.Morse.Regular

open Set

/-- Near a point `a` at which `ψ` is differentiable with `ψ' a = 0` (and `ψ'` continuous there),
`ψ` moves slower than the identity: `|ψ x - ψ a| ≤ |x - a|` on a symmetric interval around `a`.
This is the mean value inequality applied with the bound `|ψ'| ≤ 1` furnished by continuity of
`deriv ψ` at `a`. -/
theorem abs_sub_le_of_deriv_eq_zero {ψ : ℝ → ℝ} {a b ρ : ℝ} (hρ : 0 < ρ) (hψa : ψ a = b)
    (hd : ∀ x ∈ Set.Ioo (a - ρ) (a + ρ), HasDerivAt ψ (deriv ψ x) x)
    (hdc : ContinuousOn (deriv ψ) (Set.Ioo (a - ρ) (a + ρ))) (h0 : deriv ψ a = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ x ∈ Set.Ioo (a - δ) (a + δ), |ψ x - b| ≤ |x - a| := by
  -- `a` lies in the interval on which `deriv ψ` is continuous, hence `deriv ψ` is continuous at `a`.
  have hamem : a ∈ Set.Ioo (a - ρ) (a + ρ) := ⟨by linarith, by linarith⟩
  have hcont : ContinuousAt (deriv ψ) a :=
    (hdc.continuousWithinAt hamem).continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
  -- Continuity at `a` together with `deriv ψ a = 0` gives `|deriv ψ| < 1` near `a`.
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  -- The radius we return is the smaller of `ρ` and the continuity radius.
  set δ := min δ₁ ρ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδ₁pos hρ
  have hδleρ : δ ≤ ρ := by rw [hδdef]; exact min_le_right _ _
  have hδleδ₁ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  refine ⟨δ, hδpos, hδleρ, ?_⟩
  -- The interval of radius `δ` sits inside the interval of radius `ρ`.
  have hsub : Set.Ioo (a - δ) (a + δ) ⊆ Set.Ioo (a - ρ) (a + ρ) := by
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hδleρ], by linarith [hy.2, hδleρ]⟩
  have hdiff : ∀ y ∈ Set.Ioo (a - δ) (a + δ), DifferentiableAt ℝ ψ y :=
    fun y hy => (hd y (hsub hy)).differentiableAt
  have hbound : ∀ y ∈ Set.Ioo (a - δ) (a + δ), ‖deriv ψ y‖ ≤ 1 := by
    intro y hy
    rw [Set.mem_Ioo] at hy
    have hya : |y - a| < δ := abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hya₁ : dist y a < δ₁ := by rw [Real.dist_eq]; exact lt_of_lt_of_le hya hδleδ₁
    have hd1 : dist (deriv ψ y) (deriv ψ a) < 1 := hδ₁ hya₁
    rw [Real.dist_eq, h0, sub_zero] at hd1
    rw [Real.norm_eq_abs]
    exact le_of_lt hd1
  -- The mean value inequality with the constant bound `1` on the derivative.
  intro x hx
  rw [Set.mem_Ioo] at hx
  have hamemδ : a ∈ Set.Ioo (a - δ) (a + δ) := ⟨by linarith [hδpos], by linarith [hδpos]⟩
  have hxmem : x ∈ Set.Ioo (a - δ) (a + δ) := ⟨hx.1, hx.2⟩
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := ψ)
      (s := Set.Ioo (a - δ) (a + δ)) (C := 1) (x := a) (y := x)
      hdiff hbound (convex_Ioo _ _) hamemδ hxmem
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, hψa] at hmain
  exact hmain

end Work.Smooth.Morse.Regular
