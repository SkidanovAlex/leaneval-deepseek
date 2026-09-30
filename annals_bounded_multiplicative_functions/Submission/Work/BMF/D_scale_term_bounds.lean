import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `f g : ℕ → ℂ` bounded by `1` in norm, the real part of `f p * conj (g p)` lies in
`[-1, 1]`. -/
lemma re_mul_star_mem_Icc {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (p : ℕ) : (f p * star (g p)).re ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 : ‖f p * star (g p)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    nlinarith [hf p, hg p, norm_nonneg (f p), norm_nonneg (g p)]
  have h2 := Complex.abs_re_le_norm (f p * star (g p))
  rw [abs_le] at h2
  exact ⟨by linarith [h2.1, h1], le_trans h2.2 h1⟩

theorem D_scale_term_bounds (f g : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) :
    (∀ p : ℕ, 0 ≤ (1 - (f p * star (g p)).re) / (p : ℝ)) ∧
    (∀ p : ℕ, (1 - (f p * star (g p)).re) / (p : ℝ) ≤ 2 / (p : ℝ)) := by
  have hmem : ∀ p : ℕ, (f p * star (g p)).re ∈ Set.Icc (-1 : ℝ) 1 :=
    re_mul_star_mem_Icc hf hg
  constructor
  · intro p
    apply div_nonneg
    · linarith [(hmem p).2]
    · positivity
  · intro p
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [(hmem p).1]

end Work.BMF
