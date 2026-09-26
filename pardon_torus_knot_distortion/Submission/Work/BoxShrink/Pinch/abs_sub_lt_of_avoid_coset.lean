import Mathlib

/-!
# Escaping the coset `cℤ + d`

A continuous real function that avoids every point of the arithmetic progression
`cℤ + d` (with `c > 0`) cannot take two values whose difference has absolute
value at least `c`: any closed interval of length `≥ c` contains a point of the
progression, and the intermediate value theorem would then force `f` to hit it.
-/

namespace Work.BoxShrink.Pinch

theorem abs_sub_lt_of_avoid_coset {c d : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t : ℝ, ∀ m : ℤ, f t ≠ m * c + d) (s t : ℝ) : |f s - f t| < c := by
  by_contra hcontra
  rw [not_lt] at hcontra
  -- Any closed interval of length `≥ c` contains a point of the coset `cℤ + d`.
  have grid : ∀ x y : ℝ, x ≤ y → c ≤ y - x →
      ∃ m : ℤ, x ≤ (m : ℝ) * c + d ∧ (m : ℝ) * c + d ≤ y := by
    intro x y _ hlen
    refine ⟨⌈(x - d) / c⌉, ?_, ?_⟩
    · have h1 : (x - d) / c ≤ ((⌈(x - d) / c⌉ : ℤ) : ℝ) := Int.le_ceil _
      have h2 : x - d ≤ ((⌈(x - d) / c⌉ : ℤ) : ℝ) * c := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hc)
        rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at this
      linarith
    · have h1 : ((⌈(x - d) / c⌉ : ℤ) : ℝ) < (x - d) / c + 1 := Int.ceil_lt_add_one _
      have h2 : ((⌈(x - d) / c⌉ : ℤ) : ℝ) * c < x - d + c := by
        have := mul_lt_mul_of_pos_right h1 hc
        rw [add_mul, one_mul, div_mul_cancel₀ (x - d) (ne_of_gt hc)] at this
        linarith
      linarith
  rcases le_total (f s) (f t) with hval | hval
  · have hlen : c ≤ f t - f s := by
      have hnn := abs_of_nonpos (show f s - f t ≤ 0 by linarith)
      rw [hnn] at hcontra; linarith
    obtain ⟨m, hm1, hm2⟩ := grid (f s) (f t) hval hlen
    have hconn : IsPreconnected (f '' Set.Icc (min s t) (max s t)) :=
      (isPreconnected_Icc (a := min s t) (b := max s t)).image f hf.continuousOn
    have hmem : (m : ℝ) * c + d ∈ f '' Set.Icc (min s t) (max s t) :=
      hconn.ordConnected.out
        ⟨s, ⟨min_le_left s t, le_max_left s t⟩, rfl⟩
        ⟨t, ⟨min_le_right s t, le_max_right s t⟩, rfl⟩
        ⟨hm1, hm2⟩
    obtain ⟨u, _, hfu⟩ := hmem
    exact h u m hfu
  · have hlen : c ≤ f s - f t := by
      have hnn := abs_of_nonneg (show 0 ≤ f s - f t by linarith)
      rw [hnn] at hcontra; linarith
    obtain ⟨m, hm1, hm2⟩ := grid (f t) (f s) hval hlen
    have hconn : IsPreconnected (f '' Set.Icc (min s t) (max s t)) :=
      (isPreconnected_Icc (a := min s t) (b := max s t)).image f hf.continuousOn
    have hmem : (m : ℝ) * c + d ∈ f '' Set.Icc (min s t) (max s t) :=
      hconn.ordConnected.out
        ⟨t, ⟨min_le_right s t, le_max_right s t⟩, rfl⟩
        ⟨s, ⟨min_le_left s t, le_max_left s t⟩, rfl⟩
        ⟨hm1, hm2⟩
    obtain ⟨u, _, hfu⟩ := hmem
    exact h u m hfu

end Work.BoxShrink.Pinch
