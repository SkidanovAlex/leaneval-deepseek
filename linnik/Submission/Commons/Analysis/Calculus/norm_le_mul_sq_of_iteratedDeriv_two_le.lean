import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

/-- Mean value inequality: a function whose derivative is bounded by `C` on the open interval
`(a, b)`, and which is continuous on `[a, b]`, satisfies `‖g b - g a‖ ≤ C * (b - a)`.
This only needs differentiability on the *open* interval, unlike
`norm_image_sub_le_of_norm_deriv_right_le_segment` which needs a right derivative at `a`. -/
private lemma norm_sub_le_of_norm_deriv_le {g : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ g (Set.Ioo a b))
    (hbound : ∀ x ∈ Set.Ioo a b, ‖deriv g x‖ ≤ C) :
    ‖g b - g a‖ ≤ C * (b - a) := by
  rcases eq_or_lt_of_le hab with h | hlt
  · subst h; simp
  · obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope g hlt hcont hdiff
    have hbc : 0 < b - a := sub_pos.mpr hlt
    have hmul : deriv g c * (b - a) = g b - g a := by
      rw [hc_eq]
      exact div_mul_cancel₀ _ (ne_of_gt hbc)
    calc ‖g b - g a‖ = ‖deriv g c * (b - a)‖ := by rw [hmul]
      _ = ‖deriv g c‖ * (b - a) := by rw [norm_mul, Real.norm_of_nonneg (le_of_lt hbc)]
      _ ≤ C * (b - a) := mul_le_mul_of_nonneg_right (hbound c hc_mem) (le_of_lt hbc)

theorem norm_le_mul_sq_of_iteratedDeriv_two_le {f : ℝ → ℝ} {x₀ B : ℝ} (hx₀ : 0 < x₀)
    (hcont : ContinuousOn f (Set.Icc (0:ℝ) x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hf0 : f 0 = 0) (hfx : f x₀ = 0) :
    (∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖f t‖ ≤ B * x₀ ^ 2) ∧
      (∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv f t‖ ≤ B * x₀) := by
  -- `0 ≤ B` since the hypothesis `hBnd` is nonempty on the open interval
  have hBnn : 0 ≤ B := by
    have hx : x₀ / 2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
    exact (norm_nonneg _).trans (hBnd _ hx)
  -- differentiability facts on the open interval
  have hf_diff : DifferentiableOn ℝ f (Set.Ioo (0:ℝ) x₀) :=
    hf2.differentiableOn (by norm_num)
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo (0:ℝ) x₀) :=
    hf2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv_cont_diff : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) x₀) :=
    hf2.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)
  have hderiv_diff : DifferentiableOn ℝ (deriv f) (Set.Ioo (0:ℝ) x₀) :=
    hderiv_cont_diff.differentiableOn (by norm_num)
  -- `iteratedDeriv 2 f = deriv (deriv f)` pointwise
  have h2 : ∀ x, iteratedDeriv 2 f x = deriv (deriv f) x := by
    intro x
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- Rolle: there is an interior critical point of `f`
  obtain ⟨c, hc_mem, hc0⟩ := exists_deriv_eq_zero hx₀ hcont (hf0.trans hfx.symm)
  have hc_pos : 0 < c := hc_mem.1
  have hc_lt : c < x₀ := hc_mem.2
  -- bound on the first derivative, comparing every point with the Rolle point `c`
  have hderiv_bound : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖deriv f t‖ ≤ B * x₀ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htx : t < x₀ := ht.2
    rcases le_or_gt c t with hct | htc
    · have hsubI : Set.Ioo c t ⊆ Set.Ioo (0:ℝ) x₀ := by
        intro y hy
        exact ⟨lt_of_lt_of_le hc_pos (le_of_lt hy.1), lt_of_le_of_lt (le_of_lt hy.2) htx⟩
      have hsubC : Set.Icc c t ⊆ Set.Ioo (0:ℝ) x₀ := by
        intro y hy
        exact ⟨lt_of_lt_of_le hc_pos hy.1, lt_of_le_of_lt hy.2 htx⟩
      have hbnd : ∀ x ∈ Set.Ioo c t, ‖deriv (deriv f) x‖ ≤ B := by
        intro x hx
        rw [← h2 x]
        exact hBnd x (hsubI hx)
      have hmain := norm_sub_le_of_norm_deriv_le (g := deriv f) hct (hderiv_cont.mono hsubC)
        (hderiv_diff.mono hsubI) hbnd
      rw [hc0, sub_zero] at hmain
      calc ‖deriv f t‖ ≤ B * (t - c) := hmain
        _ ≤ B * x₀ := mul_le_mul_of_nonneg_left (by linarith) hBnn
    · have hsubI : Set.Ioo t c ⊆ Set.Ioo (0:ℝ) x₀ := by
        intro y hy
        exact ⟨lt_of_lt_of_le ht0 (le_of_lt hy.1), lt_of_le_of_lt (le_of_lt hy.2) hc_lt⟩
      have hsubC : Set.Icc t c ⊆ Set.Ioo (0:ℝ) x₀ := by
        intro y hy
        exact ⟨lt_of_lt_of_le ht0 hy.1, lt_of_le_of_lt hy.2 hc_lt⟩
      have hbnd : ∀ x ∈ Set.Ioo t c, ‖deriv (deriv f) x‖ ≤ B := by
        intro x hx
        rw [← h2 x]
        exact hBnd x (hsubI hx)
      have hmain := norm_sub_le_of_norm_deriv_le (g := deriv f) (le_of_lt htc)
        (hderiv_cont.mono hsubC) (hderiv_diff.mono hsubI) hbnd
      rw [hc0, zero_sub, norm_neg] at hmain
      calc ‖deriv f t‖ ≤ B * (c - t) := hmain
        _ ≤ B * x₀ := mul_le_mul_of_nonneg_left (by linarith) hBnn
  -- bound on `f` itself from the derivative bound and `f 0 = 0`
  have hf_bound : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖f t‖ ≤ B * x₀ ^ 2 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hsubI : Set.Ioo (0:ℝ) t ⊆ Set.Ioo (0:ℝ) x₀ := by
      intro y hy
      exact ⟨hy.1, lt_trans hy.2 ht.2⟩
    have hsubC : Set.Icc (0:ℝ) t ⊆ Set.Icc (0:ℝ) x₀ :=
      Set.Icc_subset_Icc_right (le_of_lt ht.2)
    have hbnd : ∀ x ∈ Set.Ioo (0:ℝ) t, ‖deriv f x‖ ≤ B * x₀ :=
      fun x hx => hderiv_bound x (hsubI hx)
    have hmain := norm_sub_le_of_norm_deriv_le (g := f) (le_of_lt ht0) (hcont.mono hsubC)
      (hf_diff.mono hsubI) hbnd
    simp only [hf0, sub_zero] at hmain
    calc ‖f t‖ ≤ (B * x₀) * t := hmain
      _ ≤ (B * x₀) * x₀ :=
          mul_le_mul_of_nonneg_left (le_of_lt ht.2) (mul_nonneg hBnn (le_of_lt hx₀))
      _ = B * x₀ ^ 2 := by ring
  exact ⟨hf_bound, hderiv_bound⟩

end Commons.Analysis.Calculus