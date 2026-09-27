import Mathlib

namespace Work.EKLC6Core

theorem exists_one_sided_bound_of_hasDerivAt {f : ℝ → ℝ} (hf : Monotone f) {A B : ℝ}
    (hA : ∀ x : ℝ, A ≤ f x) (hB : ∀ x : ℝ, f x ≤ B) {r K : ℝ} (hr : 0 < r)
    (hd : HasDerivAt f K r) :
    ∃ cp cm : ℝ, 0 < cp ∧ 0 < cm ∧
      (∀ h : ℝ, 0 < h → f (r + h) - f r ≤ cp * h) ∧
      (∀ h : ℝ, 0 < h → f r - f (r - h) ≤ cm * h) := by
  -- Differentiability at `r` gives a neighbourhood on which `f` is bounded
  -- by the linear (tangent) approximation.
  have hev : ∀ᶠ y in nhds r, ‖f y - f r - (y - r) * K‖ ≤ ‖y - r‖ := by
    have h := hd.isLittleO.eventuallyLE
    simpa [smul_eq_mul] using h
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  -- Global bounds give an additive bound `B - A` for differences of `f`.
  have hAB : A ≤ B := le_trans (hA r) (hB r)
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  -- The common constant.  It dominates `K + 1` near `r` and `(B - A) / δ` far
  -- from `r`.
  set c : ℝ := max (|K| + 1) ((B - A) / δ) with hc
  have hc1 : (|K| + 1) ≤ c := by rw [hc]; exact le_max_left _ _
  have hc2 : (B - A) / δ ≤ c := by rw [hc]; exact le_max_right _ _
  have hcpos : 0 < c := lt_of_lt_of_le (by have := abs_nonneg K; linarith) hc1
  refine ⟨c, c, hcpos, hcpos, ?_, ?_⟩
  · -- Right-hand one-sided bound.
    intro h hh
    rcases lt_or_ge h δ with hlt | hge
    · -- `h` small: use the derivative bound.
      have hdist : dist (r + h) r < δ := by
        have h2 : r + h - r = h := by ring
        simp only [Real.dist_eq, h2, abs_of_pos hh]
        exact hlt
      have hb : ‖f (r + h) - f r - h * K‖ ≤ h := by
        have h1 := hδ hdist
        have h2 : r + h - r = h := by ring
        simp only [h2, Real.norm_of_nonneg (le_of_lt hh)] at h1
        exact h1
      have hle2 : f (r + h) - f r ≤ h * K + h := by
        have := (abs_le.mp hb).2; linarith
      have hk : h * K ≤ h * |K| := by
        rw [mul_comm h K, mul_comm h |K|]
        exact mul_le_mul_of_nonneg_right (le_abs_self K) (le_of_lt hh)
      have hle3 : h * K + h ≤ (|K| + 1) * h := by nlinarith [hk]
      have hle4 : (|K| + 1) * h ≤ c * h :=
        mul_le_mul_of_nonneg_right hc1 (le_of_lt hh)
      linarith
    · -- `h` large: use monotone global boundedness.
      have hbnd : f (r + h) - f r ≤ B - A := by
        have h1 := hB (r + h); have h2 := hA r; linarith
      have hstep : (B - A) / δ * δ ≤ (B - A) / δ * h :=
        mul_le_mul_of_nonneg_left hge (div_nonneg hBA (le_of_lt hδpos))
      have heq : (B - A) / δ * δ = B - A := div_mul_cancel₀ (B - A) (ne_of_gt hδpos)
      have hstep2 : (B - A) / δ * h ≤ c * h :=
        mul_le_mul_of_nonneg_right hc2 (le_of_lt hh)
      linarith
  · -- Left-hand one-sided bound.
    intro h hh
    rcases lt_or_ge h δ with hlt | hge
    · have hdist : dist (r - h) r < δ := by
        have h2 : r - h - r = -h := by ring
        simp only [Real.dist_eq, h2, abs_neg, abs_of_pos hh]
        exact hlt
      have hb : ‖f (r - h) - f r + h * K‖ ≤ h := by
        have h1 := hδ hdist
        have h2 : r - h - r = -h := by ring
        simp only [h2, Real.norm_eq_abs, abs_neg, abs_of_pos hh] at h1
        have harg : f (r - h) - f r - -h * K = f (r - h) - f r + h * K := by ring
        rwa [harg] at h1
      have hlow : -h ≤ f (r - h) - f r + h * K := (abs_le.mp hb).1
      have hle2 : f r - f (r - h) ≤ h * K + h := by linarith
      have hk : h * K ≤ h * |K| := by
        rw [mul_comm h K, mul_comm h |K|]
        exact mul_le_mul_of_nonneg_right (le_abs_self K) (le_of_lt hh)
      have hle3 : h * K + h ≤ (|K| + 1) * h := by nlinarith [hk]
      have hle4 : (|K| + 1) * h ≤ c * h :=
        mul_le_mul_of_nonneg_right hc1 (le_of_lt hh)
      linarith
    · have hbnd : f r - f (r - h) ≤ B - A := by
        have h1 := hB r; have h2 := hA (r - h); linarith
      have hstep : (B - A) / δ * δ ≤ (B - A) / δ * h :=
        mul_le_mul_of_nonneg_left hge (div_nonneg hBA (le_of_lt hδpos))
      have heq : (B - A) / δ * δ = B - A := div_mul_cancel₀ (B - A) (ne_of_gt hδpos)
      have hstep2 : (B - A) / δ * h ≤ c * h :=
        mul_le_mul_of_nonneg_right hc2 (le_of_lt hh)
      linarith

end Work.EKLC6Core
