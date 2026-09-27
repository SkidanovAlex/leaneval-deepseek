/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Brown
-/
import Mathlib
import Submission.Work.Brown.Basic

/-!
# Moving a compact set into a nonempty open set by a compactly supported homeomorphism of `ℝⁿ`

The main result is `Work.Brown.Cell.exists_homeomorph_image_compact_subset_open`: for a compact
`K ⊆ ℝⁿ` and a nonempty open `A ⊆ ℝⁿ` there is a homeomorphism `h` of `ℝⁿ` with `h '' K ⊆ A`
which is the identity outside a sufficiently large ball.

The construction is elementary:

* pick `a ∈ A` and `r > 0` with `ball a r ⊆ A`,
* let `M` bound `‖k - a‖` for `k ∈ K` and let `r0 = r/2`,
* build a (piecewise linear) increasing homeomorphism `σ : ℝ → ℝ` with `σ t = t` for `t ≥ R`
  and `σ t ≤ r0` for `0 ≤ t ≤ M`, with explicit inverse `τ`,
* the radial map `ρ x = (σ ‖x‖ / ‖x‖) • x` is a homeomorphism of `ℝⁿ` shrinking the ball of
  radius `M` into the ball of radius `r0`, and it is the identity outside the ball of radius `R`,
* conjugate by the translation taking `a` to `0`: `h x = a + ρ (x - a)`.

The auxiliary definitions `continuous_radial`, `norm_radial`, `radialHomeomorph` and
`piecewise_data` are stated for an arbitrary real normed space where possible.
-/

open Set Metric

namespace Work.Brown.Cell

/-- The radial map `x ↦ (ψ ‖x‖ / ‖x‖) • x` is continuous whenever `ψ` is continuous and
`ψ 0 = 0`.  (Lean's convention `a / 0 = 0` makes the formula total and equal to `0` at the
origin.) -/
theorem continuous_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) :
    Continuous (fun x : E => (ψ ‖x‖ / ‖x‖) • x) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rcases eq_or_ne x0 0 with rfl | hx0
  · rw [ContinuousAt]
    rw [show (ψ ‖(0:E)‖ / ‖(0:E)‖) • (0:E) = 0 by simp]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ x : E, ‖(ψ ‖x‖ / ‖x‖) • x‖ = |ψ ‖x‖| := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp [hψ0]
      · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg x)]
        rw [div_mul_cancel₀]
        exact norm_ne_zero_iff.mpr hx
    simp only [hnorm]
    have hcont : Continuous (fun x : E => |ψ ‖x‖|) := continuous_abs.comp (hψ.comp continuous_norm)
    have ht := hcont.continuousAt (x := (0:E))
    rw [ContinuousAt] at ht
    simpa [hψ0] using ht
  · have hx0' : ‖x0‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    have h1 : ContinuousAt (fun x : E => ψ ‖x‖ / ‖x‖) x0 :=
      ((hψ.comp continuous_norm).continuousAt).div continuous_norm.continuousAt hx0'
    exact h1.smul continuousAt_id

/-- The norm of the radial map `x ↦ (ψ ‖x‖ / ‖x‖) • x` is `|ψ ‖x‖|`, for any `ψ` with
`ψ 0 = 0`. -/
lemma norm_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 0) (x : E) :
    ‖(ψ ‖x‖ / ‖x‖) • x‖ = |ψ ‖x‖| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hψ0]
  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg x)]
    rw [div_mul_cancel₀]
    exact norm_ne_zero_iff.mpr hx

/-- **The radial homeomorphism.**  Given continuous `σ τ : ℝ → ℝ` fixing `0`, positive on
`[0,∞)` and mutually inverse on `[0,∞)`, the map `x ↦ (σ ‖x‖ / ‖x‖) • x` is a homeomorphism of
`E`, with inverse `y ↦ (τ ‖y‖ / ‖y‖) • y`. -/
noncomputable def radialHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ τ : ℝ → ℝ) (hσc : Continuous σ) (hτc : Continuous τ)
    (hσ0 : σ 0 = 0) (hτ0 : τ 0 = 0)
    (hσnn : ∀ t, 0 ≤ t → 0 ≤ σ t) (hτnn : ∀ t, 0 ≤ t → 0 ≤ τ t)
    (hστ : ∀ t, 0 ≤ t → τ (σ t) = t) (hτσ : ∀ t, 0 ≤ t → σ (τ t) = t) :
    E ≃ₜ E where
  toFun := fun x => (σ ‖x‖ / ‖x‖) • x
  invFun := fun y => (τ ‖y‖ / ‖y‖) • y
  left_inv := by
    intro x
    simp only []
    by_cases hx : x = 0
    · subst hx; simp [hσ0, hτ0]
    · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hσne : σ ‖x‖ ≠ 0 := by
        intro hz
        have h := hστ ‖x‖ (norm_nonneg x)
        rw [hz, hτ0] at h
        exact hxnorm h.symm
      have hnormρ : ‖(σ ‖x‖ / ‖x‖) • x‖ = σ ‖x‖ := by
        rw [norm_radial hσ0 x, abs_of_nonneg (hσnn _ (norm_nonneg x))]
      rw [hnormρ, hστ ‖x‖ (norm_nonneg x), smul_smul]
      rw [show ‖x‖ / σ ‖x‖ * (σ ‖x‖ / ‖x‖) = 1 by field_simp]
      rw [one_smul]
  right_inv := by
    intro y
    simp only []
    by_cases hy : y = 0
    · subst hy; simp [hσ0, hτ0]
    · have hynorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
      have hτne : τ ‖y‖ ≠ 0 := by
        intro hz
        have h := hτσ ‖y‖ (norm_nonneg y)
        rw [hz, hσ0] at h
        exact hynorm h.symm
      have hnormρ : ‖(τ ‖y‖ / ‖y‖) • y‖ = τ ‖y‖ := by
        rw [norm_radial hτ0 y, abs_of_nonneg (hτnn _ (norm_nonneg y))]
      rw [hnormρ, hτσ ‖y‖ (norm_nonneg y), smul_smul]
      rw [show ‖y‖ / τ ‖y‖ * (τ ‖y‖ / ‖y‖) = 1 by field_simp]
      rw [one_smul]
  continuous_toFun := continuous_radial hσc hσ0
  continuous_invFun := continuous_radial hτc hτ0

/-- Computuation rule for `radialHomeomorph`. -/
lemma radialHomeomorph_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ τ : ℝ → ℝ) (hσc : Continuous σ) (hτc : Continuous τ)
    (hσ0 : σ 0 = 0) (hτ0 : τ 0 = 0)
    (hσnn : ∀ t, 0 ≤ t → 0 ≤ σ t) (hτnn : ∀ t, 0 ≤ t → 0 ≤ τ t)
    (hστ : ∀ t, 0 ≤ t → τ (σ t) = t) (hτσ : ∀ t, 0 ≤ t → σ (τ t) = t) (x : E) :
    radialHomeomorph σ τ hσc hτc hσ0 hτ0 hσnn hτnn hστ hτσ x = (σ ‖x‖ / ‖x‖) • x := rfl

/-- **The piecewise linear squeeze.**  For `0 < M`, `0 < r0 < R` and `M < R` there are
continuous functions `σ τ : ℝ → ℝ` which are mutually inverse homeomorphisms of `[0,∞)`, with
`σ t = t` for `t ≥ R`, `σ t ≤ r0` for `0 ≤ t ≤ M`, and `σ, τ ≥ 0` on `[0,∞)`. -/
lemma piecewise_data (M r0 R : ℝ) (hM : 0 < M) (hr0 : 0 < r0)
    (hMR : M < R) (hr0R : r0 < R) :
    ∃ σ τ : ℝ → ℝ,
      Continuous σ ∧ Continuous τ ∧ σ 0 = 0 ∧ τ 0 = 0 ∧
      (∀ t, 0 ≤ t → 0 ≤ σ t) ∧ (∀ t, 0 ≤ t → 0 ≤ τ t) ∧
      (∀ t, 0 ≤ t → τ (σ t) = t) ∧ (∀ t, 0 ≤ t → σ (τ t) = t) ∧
      (∀ t, 0 ≤ t → t ≤ M → σ t ≤ r0) ∧ (∀ t, R ≤ t → σ t = t) := by
  set c1 : ℝ := r0 / M with hc1
  set c2 : ℝ := (R - r0) / (R - M) with hc2
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hc2pos : 0 < c2 := by rw [hc2]; exact div_pos (by linarith) (by linarith)
  have hc1M : c1 * M = r0 := by rw [hc1]; exact div_mul_cancel₀ r0 (ne_of_gt hM)
  have hc2RM : c2 * (R - M) = R - r0 := by
    rw [hc2]; exact div_mul_cancel₀ (R - r0) (ne_of_gt (by linarith))
  have hinv1 : (1/c1) * r0 = M := by
    rw [hc1, one_div_div]; exact div_mul_cancel₀ M (ne_of_gt hr0)
  have hinv2 : (1/c2) * (R - r0) = R - M := by
    rw [hc2, one_div_div]; exact div_mul_cancel₀ (R - M) (ne_of_gt (by linarith))
  set σ : ℝ → ℝ := fun t => c1 * min t M + c2 * max (min t R - M) 0 + max (t - R) 0 with hσ
  set τ : ℝ → ℝ := fun t => (1/c1) * min t r0 + (1/c2) * max (min t R - r0) 0 + max (t - R) 0 with hτ
  have hs1 : ∀ t, t ≤ M → σ t = c1 * t := by
    intro t ht
    simp only [hσ]
    rw [min_eq_left ht, min_eq_left (le_trans ht (le_of_lt hMR))]
    rw [max_eq_right (by linarith : t - M ≤ 0), max_eq_right (by linarith : t - R ≤ 0)]
    ring
  have hs2 : ∀ t, M ≤ t → t ≤ R → σ t = r0 + c2 * (t - M) := by
    intro t h1 h2
    simp only [hσ]
    rw [min_eq_right h1, min_eq_left h2, hc1M]
    rw [max_eq_left (by linarith : 0 ≤ t - M), max_eq_right (by linarith : t - R ≤ 0)]
    ring
  have hs3 : ∀ t, R ≤ t → σ t = t := by
    intro t ht
    simp only [hσ]
    rw [min_eq_right (le_trans (le_of_lt hMR) ht), min_eq_right ht]
    rw [max_eq_left (by linarith : 0 ≤ R - M), max_eq_left (by linarith : 0 ≤ t - R)]
    rw [hc1M, hc2RM]
    ring
  have ht1 : ∀ s, s ≤ r0 → τ s = (1/c1) * s := by
    intro s hs
    simp only [hτ]
    rw [min_eq_left hs, min_eq_left (le_trans hs (le_of_lt hr0R))]
    rw [max_eq_right (by linarith : s - r0 ≤ 0), max_eq_right (by linarith : s - R ≤ 0)]
    ring
  have ht2 : ∀ s, r0 ≤ s → s ≤ R → τ s = M + (1/c2) * (s - r0) := by
    intro s h1 h2
    simp only [hτ]
    rw [min_eq_right h1, min_eq_left h2, hinv1]
    rw [max_eq_left (by linarith : 0 ≤ s - r0), max_eq_right (by linarith : s - R ≤ 0)]
    ring
  have ht3 : ∀ s, R ≤ s → τ s = s := by
    intro s hs
    simp only [hτ]
    rw [min_eq_right (by linarith : r0 ≤ s), min_eq_right hs]
    rw [max_eq_left (by linarith : 0 ≤ R - r0), max_eq_left (by linarith : 0 ≤ s - R)]
    rw [hinv1, hinv2]
    ring
  refine ⟨σ, τ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hσ]; fun_prop
  · simp only [hτ]; fun_prop
  · rw [hs1 0 (le_of_lt hM)]; ring
  · rw [ht1 0 (le_of_lt hr0)]; ring
  · intro t ht
    simp only [hσ]
    have h1 : 0 ≤ c1 * min t M := mul_nonneg (le_of_lt hc1pos) (le_min ht (le_of_lt hM))
    have h2 : 0 ≤ c2 * max (min t R - M) 0 := mul_nonneg (le_of_lt hc2pos) (le_max_right _ _)
    have h3 : 0 ≤ max (t - R) 0 := le_max_right _ _
    linarith
  · intro s hs
    simp only [hτ]
    have h1 : 0 ≤ (1/c1) * min s r0 := mul_nonneg (by positivity) (le_min hs (le_of_lt hr0))
    have h2 : 0 ≤ (1/c2) * max (min s R - r0) 0 := mul_nonneg (by positivity) (le_max_right _ _)
    have h3 : 0 ≤ max (s - R) 0 := le_max_right _ _
    linarith
  · intro t ht
    rcases le_total t M with h | h
    · rw [hs1 t h, ht1 (c1 * t) ?_]
      · rw [one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc1pos), one_mul]
      · calc c1 * t ≤ c1 * M := mul_le_mul_of_nonneg_left h (le_of_lt hc1pos)
          _ = r0 := hc1M
    · rcases le_total t R with h2 | h2
      · rw [hs2 t h h2, ht2 (r0 + c2 * (t - M)) ?_ ?_]
        · rw [show r0 + c2 * (t - M) - r0 = c2 * (t - M) by ring,
              ← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hc2pos), one_mul]
          ring
        · have : 0 ≤ c2 * (t - M) := mul_nonneg (le_of_lt hc2pos) (by linarith)
          linarith
        · have : c2 * (t - M) ≤ R - r0 := by
            rw [← hc2RM]; exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hc2pos)
          linarith
      · rw [hs3 t h2, ht3 t h2]
  · intro t ht
    rcases le_total t r0 with h | h
    · rw [ht1 t h, hs1 ((1/c1) * t) ?_]
      · rw [one_div, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc1pos), one_mul]
      · calc (1/c1) * t ≤ (1/c1) * r0 := mul_le_mul_of_nonneg_left h (by positivity)
          _ = M := hinv1
    · rcases le_total t R with h2 | h2
      · rw [ht2 t h h2, hs2 (M + (1/c2) * (t - r0)) ?_ ?_]
        · rw [show M + (1/c2) * (t - r0) - M = (1/c2) * (t - r0) by ring,
              ← mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hc2pos), one_mul]
          ring
        · have : 0 ≤ (1/c2) * (t - r0) := mul_nonneg (by positivity) (by linarith)
          linarith
        · have : (1/c2) * (t - r0) ≤ R - M := by
            rw [← hinv2]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
      · rw [ht3 t h2, hs3 t h2]
  · intro t _ htM
    rw [hs1 t htM]
    calc c1 * t ≤ c1 * M := mul_le_mul_of_nonneg_left htM (le_of_lt hc1pos)
      _ = r0 := hc1M
  · exact hs3

theorem exists_homeomorph_image_compact_subset_open {n : ℕ} {K A : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hA : IsOpen A) (hAne : A.Nonempty) : ∃ h : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n), h '' K ⊆ A ∧ ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → h x = x := by
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp hA) a ha
  have hbdd : Bornology.IsBounded K := hK.isBounded
  rw [Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))] at hbdd
  obtain ⟨Rk, hRk⟩ := hbdd
  set M : ℝ := |Rk| + ‖a‖ + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  set r0 : ℝ := r / 2 with hr0def
  have hr0pos : 0 < r0 := by rw [hr0def]; linarith
  have hr0r : r0 < r := by rw [hr0def]; linarith
  set R : ℝ := M + r0 + 1 with hRdef
  have hMR : M < R := by rw [hRdef]; linarith
  have hr0R : r0 < R := by rw [hRdef]; linarith
  have hbound : ∀ k ∈ K, ‖k - a‖ ≤ M := by
    intro k hk
    have hk' : ‖k‖ ≤ Rk := by
      have h1 := hRk hk
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact h1
    calc ‖k - a‖ ≤ ‖k‖ + ‖a‖ := norm_sub_le k a
      _ ≤ Rk + ‖a‖ := by linarith
      _ ≤ M := by rw [hMdef]; linarith [le_abs_self Rk]
  obtain ⟨σ, τ, hσc, hτc, hσ0, hτ0, hσnn, hτnn, hστ, hτσ, hsle, hsid⟩ :=
    piecewise_data M r0 R hMpos hr0pos hMR hr0R
  let ρ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    radialHomeomorph σ τ hσc hτc hσ0 hτ0 hσnn hτnn hστ hτσ
  have hρ : ∀ x, ρ x = (σ ‖x‖ / ‖x‖) • x := fun x => rfl
  have hh : ∀ x, ((Homeomorph.vadd (-a)).trans (ρ.trans (Homeomorph.vadd a))) x = a + ρ (x - a) := by
    intro x
    simp only [Homeomorph.trans_apply, Homeomorph.vadd_apply, vadd_eq_add]
    rw [show (-a) + x = x - a by rw [sub_eq_add_neg, add_comm]]
  refine ⟨(Homeomorph.vadd (-a)).trans (ρ.trans (Homeomorph.vadd a)), ?_, R + ‖a‖, ?_⟩
  · intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    rw [hh]
    have hkbd : ‖k - a‖ ≤ M := hbound k hk
    have hnorm : ‖ρ (k - a)‖ ≤ r0 := by
      rw [hρ, norm_radial hσ0, abs_of_nonneg (hσnn _ (norm_nonneg _))]
      exact hsle _ (norm_nonneg _) hkbd
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show a + ρ (k - a) - a = ρ (k - a) by abel]
    linarith
  · intro x hx
    rw [hh]
    have hxnorm : R ≤ ‖x - a‖ := by
      have : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
        calc ‖x‖ = ‖x - a + a‖ := by rw [show x - a + a = x by abel]
          _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
      linarith
    have hne : ‖x - a‖ ≠ 0 := by
      have : 0 < ‖x - a‖ := lt_of_lt_of_le (by linarith : (0:ℝ) < R) hxnorm
      exact ne_of_gt this
    rw [hρ, hsid ‖x - a‖ hxnorm, div_self hne, one_smul]
    abel

end Work.Brown.Cell
