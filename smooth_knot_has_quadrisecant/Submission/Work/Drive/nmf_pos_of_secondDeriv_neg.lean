import Mathlib

namespace Work.Drive

/-- **A `C²` function with strictly negative second derivative and vanishing at both endpoints is
strictly positive inside.** -/
lemma nmf_pos_of_secondDeriv_neg {h : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hd : DifferentiableOn ℝ h (Set.Ioo a b))
    (hcont1 : ContinuousOn (deriv h) (Set.Icc a b))
    (hd1 : DifferentiableOn ℝ (deriv h) (Set.Ioo a b))
    (h2 : ∀ x ∈ Set.Ioo a b, deriv (deriv h) x ≤ -c)
    (ha : h a = 0) (hb : h b = 0) : ∀ x ∈ Set.Ioo a b, 0 < h x := by
  intro x hx
  -- Suppose `h x ≤ 0`.  Three successive mean value theorems (on `[a,x]`, on `[x,b]`, and on
  -- `[ξ₁,ξ₂]` for `deriv h`) yield an interior point `ξ` at which the second derivative is `≥ 0`,
  -- contradicting `h2` (and `c > 0`).
  by_contra hcon
  have hxle : h x ≤ 0 := le_of_not_gt hcon
  obtain ⟨hax, hxb⟩ := hx
  -- MVT on `[a, x]`
  obtain ⟨ξ₁, hξ₁, hξ₁d⟩ := exists_deriv_eq_slope h hax
    (hcont.mono (fun y hy => ⟨hy.1, le_trans hy.2 hxb.le⟩))
    (hd.mono (fun y hy => ⟨hy.1, lt_trans hy.2 hxb⟩))
  -- MVT on `[x, b]`
  obtain ⟨ξ₂, hξ₂, hξ₂d⟩ := exists_deriv_eq_slope h hxb
    (hcont.mono (fun y hy => ⟨le_trans hax.le hy.1, hy.2⟩))
    (hd.mono (fun y hy => ⟨lt_of_le_of_lt hax.le hy.1, hy.2⟩))
  have hab' : ξ₁ < ξ₂ := lt_trans hξ₁.2 hξ₂.1
  -- MVT on `[ξ₁, ξ₂]` applied to `deriv h`
  obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope (deriv h) hab'
    (hcont1.mono (fun y hy => ⟨le_trans hξ₁.1.le hy.1, le_trans hy.2 hξ₂.2.le⟩))
    (hd1.mono (fun y hy => ⟨lt_trans hξ₁.1 hy.1, lt_trans hy.2 hξ₂.2⟩))
  -- the two slopes are `≤ 0` and `≥ 0` respectively
  have h₁ : deriv h ξ₁ ≤ 0 := by
    rw [hξ₁d, ha]; simp only [sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg hxle (by linarith)
  have h₂ : 0 ≤ deriv h ξ₂ := by
    rw [hξ₂d, hb]; simp only [zero_sub]
    exact div_nonneg (neg_nonneg.mpr hxle) (by linarith)
  have hq : 0 ≤ (deriv h ξ₂ - deriv h ξ₁) / (ξ₂ - ξ₁) :=
    div_nonneg (by linarith) (by linarith)
  have hξmem : ξ ∈ Set.Ioo a b := ⟨lt_trans hξ₁.1 hξ.1, lt_trans hξ.2 hξ₂.2⟩
  have hthis := h2 ξ hξmem
  rw [hξd] at hthis
  linarith

end Work.Drive
