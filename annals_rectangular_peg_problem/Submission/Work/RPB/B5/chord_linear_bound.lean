import Mathlib
import Submission.Work.RPB.B4.mvt_hasDerivAt_bounds

namespace Work.RPB.B5

open scoped ContDiff

/-- Quantitative chord estimate: a `C¹` curve whose derivative has norm `≥ ε₁` and varies by at
most `ε₁/2` over steps of length `≤ δ` grows by at least `(ε₁/2)·|s|` over a chord of length
`|s| ≤ δ`.

Writing `G v = γ v - (v - t) • deriv γ t`, the mean value inequality applied on `[t, t+s]` bounds
`‖G t - G (t+s)‖` by `(ε₁/2)·|s|`, while `γ (t+s) - γ t = s • deriv γ t - (G t - G (t+s))` and
`‖s • deriv γ t‖ = |s|·‖deriv γ t‖ ≥ |s|·ε₁`.  The reverse triangle inequality finishes. -/
theorem chord_linear_bound (γ : ℝ → ℂ) (hC1 : ContDiff ℝ 1 γ) {ε₁ δ : ℝ} (hε₁ : 0 < ε₁) (hδ : 0 < δ)
    (hmin : ∀ t : ℝ, ε₁ ≤ ‖deriv γ t‖)
    (hcont : ∀ t u : ℝ, |u| ≤ δ → ‖deriv γ (t + u) - deriv γ t‖ ≤ ε₁ / 2) :
    ∀ t s : ℝ, |s| ≤ δ → (ε₁ / 2) * |s| ≤ ‖γ (t + s) - γ t‖ := by
  intro t s hs
  -- `γ` is differentiable with derivative `deriv γ`
  have hderiv : ∀ x : ℝ, HasDerivAt γ (deriv γ x) x := fun x =>
    (hC1.differentiable_one x).hasDerivAt
  -- the auxiliary curve whose derivative is `deriv γ v - deriv γ t`
  set G : ℝ → ℂ := fun v => γ v - (v - t) • deriv γ t with hGdef
  have hG : ∀ v : ℝ, HasDerivAt G (deriv γ v - deriv γ t) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => γ v) (deriv γ v) v := hderiv v
    have h2 : HasDerivAt (fun v : ℝ => (v - t) • deriv γ t) (deriv γ t) v := by
      have hlin : HasDerivAt (fun v : ℝ => v - t) 1 v := by
        simpa using (hasDerivAt_id v).sub_const t
      have := hlin.smul_const (deriv γ t)
      simpa [one_smul] using this
    have hh := h1.sub h2
    rw [hGdef]
    exact hh
  -- on the segment between `t` and `t+s` the displacement is `≤ δ`, so the perturbation is small
  have hbound : ∀ v ∈ Set.uIcc t (t + s), ‖deriv γ v - deriv γ t‖ ≤ ε₁ / 2 := by
    intro v hv
    rw [Set.mem_uIcc] at hv
    have hvt : |v - t| ≤ |s| := by
      rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h0 : 0 ≤ v - t := by linarith
        rw [abs_of_nonneg h0]
        exact le_trans (by linarith : v - t ≤ s) (le_abs_self s)
      · have h0 : v - t ≤ 0 := by linarith
        rw [abs_of_nonpos h0]
        have hs0 : s ≤ 0 := by linarith
        rw [abs_of_nonpos hs0]
        linarith
    have := hcont t (v - t) (le_trans hvt hs)
    rwa [add_sub_cancel] at this
  -- mean value inequality for `G`
  have hmvt := Work.RPB.B4.mvt_hasDerivAt_bounds (f := G)
      (f' := fun v : ℝ => deriv γ v - deriv γ t) (C := ε₁ / 2) (a := t) (b := t + s) hG hbound
  have hbs : t - (t + s) = -s := by ring
  rw [hbs, abs_neg] at hmvt
  -- decomposition of the chord
  have hdecomp : γ (t + s) - γ t = s • deriv γ t - (G t - G (t + s)) := by
    simp only [hGdef]
    have e1 : t - t = (0 : ℝ) := by ring
    have e2 : t + s - t = s := by ring
    rw [e1, e2, zero_smul, sub_zero]
    abel
  rw [hdecomp]
  -- reverse triangle inequality and the lower bound on `‖deriv γ t‖`
  have hsplit : ‖s • deriv γ t‖ ≤ ‖s • deriv γ t - (G t - G (t + s))‖ + ‖G t - G (t + s)‖ := by
    have := norm_add_le (s • deriv γ t - (G t - G (t + s))) (G t - G (t + s))
    rwa [sub_add_cancel] at this
  have hsm : ‖s • deriv γ t‖ = |s| * ‖deriv γ t‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hle : |s| * ε₁ ≤ ‖s • deriv γ t‖ := by
    rw [hsm]; exact mul_le_mul_of_nonneg_left (hmin t) (abs_nonneg s)
  linarith [hsplit, hle, hmvt]

end Work.RPB.B5
