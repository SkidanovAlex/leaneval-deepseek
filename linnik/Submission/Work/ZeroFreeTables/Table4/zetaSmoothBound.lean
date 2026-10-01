import Mathlib
import Submission.Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split

open Complex Set Filter
open scoped Topology

namespace Work.ZeroFreeTables.Table4

noncomputable section

/-!
# `Work.ZeroFreeTables.Table4.zetaSmoothBound`

The three combinations
`ζ'/ζ(s) + 1/(s-1)`, `(ζ'/ζ)'(s) - 1/(s-1)²`, `(ζ'/ζ)''(s) + 2/(s-1)³`
extend to holomorphic functions on a neighbourhood of the closed rectangle
`{1 ≤ Re s ≤ 4, |Im s| ≤ 5}`, hence are bounded there.

The point is Mathlib's entire function `riemannZeta₁`, which completes `(s-1)ζ(s)` at `s = 1`
(`riemannZeta_eq_inv_sub_mul`): for `s ≠ 1`, `ζ(s) = (s-1)⁻¹ · ζ₁(s)`, so
`logDeriv ζ s = logDeriv ζ₁ s - (s-1)⁻¹`.  Consequently all three combinations above are the
iterated derivatives of the *holomorphic* function `logDeriv ζ₁`, and the result follows from
compactness of the rectangle and continuity of `logDeriv ζ₁` and its first two derivatives there.
-/

/-- The closed rectangle `{s : ℂ | 1 ≤ Re s ≤ 4, |Im s| ≤ 5}`. -/
private def K : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 4 ∧ |s.im| ≤ 5}

private lemma isCompact_K : IsCompact K := by
  have h : K = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
      (Icc 1 4 ×ˢ Icc (-5 : ℝ) 5) := by
    ext s
    constructor
    · intro ⟨h1, h2, h3⟩
      refine ⟨(s.re, s.im), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [abs_le] at h3; exact ⟨h3.1, h3.2⟩
      · simp
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
      refine ⟨?_, ?_, ?_⟩
      · simpa using hp1
      · simpa using hp2
      · simp only [ofReal_re, ofReal_im, add_im, mul_I_im, zero_add]
        exact abs_le.mpr ⟨hp3, hp4⟩
  rw [h]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-- `(s - 1) * ζ s = ζ₁ s` for `s ≠ 1`, i.e. `ζ₁` is `(s-1)ζ(s)` completed at `s = 1`. -/
private lemma sub_one_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    (s - 1) * riemannZeta s = riemannZeta₁ s := by
  have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ hsne, one_mul]

private lemma riemannZeta₁_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta₁ s ≠ 0 := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [← sub_one_mul_zeta hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re (le_of_lt hs))

private lemma riemannZeta₁_ne_zero_of_mem_K {s : ℂ} (hs : s ∈ K) : riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · subst h; rw [riemannZeta₁_one]; norm_num
  · rw [← sub_one_mul_zeta h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re hs.1)

/-- The logarithmic derivative of `ζ` on `Re s > 1`, written with the pole term split off. -/
private lemma logDeriv_zeta_eq (z : ℂ) (hz : 1 < z.re) :
    logDeriv riemannZeta z = logDeriv riemannZeta₁ z - (z - 1)⁻¹ := by
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
  have hsne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ₁ : riemannZeta₁ z ≠ 0 := riemannZeta₁_ne_zero_of_one_lt_re hz
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hz1,
    riemannZeta_eq_inv_sub_mul hz1]
  field_simp
  ring

private lemma eventually_logDeriv_zeta_eq {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta =ᶠ[𝓝 s] (fun z : ℂ => logDeriv riemannZeta₁ z - (z - 1)⁻¹) := by
  have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [hmem] with z hz
  exact logDeriv_zeta_eq z hz

/-- `iteratedDeriv 1` of `z ↦ (z-1)⁻¹`. -/
private lemma iteratedDeriv_one_inv_sub_one (s : ℂ) :
    iteratedDeriv 1 (fun z : ℂ => (z - 1)⁻¹) s = -(((s - 1) ^ 2)⁻¹) := by
  have h := congrFun (iter_deriv_inv_linear_sub 1 (1 : ℂ) 1) s
  simp only [one_mul, one_pow, mul_one] at h
  rw [iteratedDeriv_eq_iterate, h]
  rw [show (-1 : ℤ) - ((1 : ℕ) : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  norm_num

/-- `iteratedDeriv 2` of `z ↦ (z-1)⁻¹`. -/
private lemma iteratedDeriv_two_inv_sub_one (s : ℂ) :
    iteratedDeriv 2 (fun z : ℂ => (z - 1)⁻¹) s = 2 * (((s - 1) ^ 3)⁻¹) := by
  have h := congrFun (iter_deriv_inv_linear_sub 2 (1 : ℂ) 1) s
  simp only [one_mul, one_pow, mul_one] at h
  rw [iteratedDeriv_eq_iterate, h]
  rw [show (-1 : ℤ) - ((2 : ℕ) : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  norm_num

private lemma analyticAt_logDeriv_zeta₁ {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (logDeriv riemannZeta₁) s := by
  have h1 : AnalyticAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁.analyticAt s
  have hne : riemannZeta₁ s ≠ 0 := riemannZeta₁_ne_zero_of_one_lt_re hs
  change AnalyticAt ℂ (fun z => deriv riemannZeta₁ z / riemannZeta₁ z) s
  exact h1.deriv.div h1 hne

private lemma analyticAt_logDeriv_zeta₁_of_mem_K {s : ℂ} (hs : s ∈ K) :
    AnalyticAt ℂ (logDeriv riemannZeta₁) s := by
  have h1 : AnalyticAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁.analyticAt s
  have hne : riemannZeta₁ s ≠ 0 := riemannZeta₁_ne_zero_of_mem_K hs
  change AnalyticAt ℂ (fun z => deriv riemannZeta₁ z / riemannZeta₁ z) s
  exact h1.deriv.div h1 hne

private lemma analyticOnNhd_iteratedDeriv (j : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv j (logDeriv riemannZeta₁)) K := by
  induction j with
  | zero =>
      simpa only [iteratedDeriv_zero] using
        (show AnalyticOnNhd ℂ (logDeriv riemannZeta₁) K from
          fun s hs => analyticAt_logDeriv_zeta₁_of_mem_K hs)
  | succ j ih =>
      simpa only [iteratedDeriv_succ] using ih.deriv

private lemma bound_iteratedDeriv (j : ℕ) :
    ∃ C : ℝ, ∀ s : ℂ, s ∈ K → |(iteratedDeriv j (logDeriv riemannZeta₁) s).re| ≤ C := by
  have hcont : ContinuousOn (fun s : ℂ => (iteratedDeriv j (logDeriv riemannZeta₁) s).re) K :=
    Complex.continuous_re.comp_continuousOn (analyticOnNhd_iteratedDeriv j).continuousOn
  obtain ⟨C, hC⟩ := isCompact_K.exists_bound_of_continuousOn hcont
  exact ⟨C, fun s hs => hC s hs⟩

private lemma smooth_zero (s : ℂ) (hs : 1 < s.re) :
    logDeriv riemannZeta s + 1 / (s - 1) = logDeriv riemannZeta₁ s := by
  rw [logDeriv_zeta_eq s hs, one_div]
  ring

private lemma smooth_one (s : ℂ) (hs : 1 < s.re) :
    iteratedDeriv 1 (logDeriv riemannZeta) s - 1 / (s - 1) ^ 2
      = iteratedDeriv 1 (logDeriv riemannZeta₁) s := by
  have h1 : iteratedDeriv 1 (logDeriv riemannZeta) s
      = iteratedDeriv 1 (fun z : ℂ => logDeriv riemannZeta₁ z - (z - 1)⁻¹) s :=
    (eventually_logDeriv_zeta_eq hs).iteratedDeriv_eq 1
  have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr (by rintro rfl; norm_num at hs)
  have hcd₁ : ContDiffAt ℂ (1 : ℕ∞) (logDeriv riemannZeta₁) s :=
    (analyticAt_logDeriv_zeta₁ hs).contDiffAt
  have hcd₂ : ContDiffAt ℂ (1 : ℕ∞) (fun z : ℂ => (z - 1)⁻¹) s := by
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
      analyticAt_id.sub (analyticAt_const (v := (1 : ℂ)))
    exact (hsub.inv hsne).contDiffAt
  have h2 : iteratedDeriv 1 (fun z : ℂ => logDeriv riemannZeta₁ z - (z - 1)⁻¹) s
      = iteratedDeriv 1 (logDeriv riemannZeta₁) s
        - iteratedDeriv 1 (fun z : ℂ => (z - 1)⁻¹) s :=
    iteratedDeriv_sub hcd₁ hcd₂
  have h3 : iteratedDeriv 1 (fun z : ℂ => (z - 1)⁻¹) s = -(((s - 1) ^ 2)⁻¹) :=
    iteratedDeriv_one_inv_sub_one s
  rw [h1, h2, h3, div_eq_mul_inv]
  ring

private lemma smooth_two (s : ℂ) (hs : 1 < s.re) :
    iteratedDeriv 2 (logDeriv riemannZeta) s + 2 / (s - 1) ^ 3
      = iteratedDeriv 2 (logDeriv riemannZeta₁) s := by
  have h1 : iteratedDeriv 2 (logDeriv riemannZeta) s
      = iteratedDeriv 2 (fun z : ℂ => logDeriv riemannZeta₁ z - (z - 1)⁻¹) s :=
    (eventually_logDeriv_zeta_eq hs).iteratedDeriv_eq 2
  have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr (by rintro rfl; norm_num at hs)
  have hcd₁ : ContDiffAt ℂ (2 : ℕ∞) (logDeriv riemannZeta₁) s :=
    (analyticAt_logDeriv_zeta₁ hs).contDiffAt
  have hcd₂ : ContDiffAt ℂ (2 : ℕ∞) (fun z : ℂ => (z - 1)⁻¹) s := by
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
      analyticAt_id.sub (analyticAt_const (v := (1 : ℂ)))
    exact (hsub.inv hsne).contDiffAt
  have h2 : iteratedDeriv 2 (fun z : ℂ => logDeriv riemannZeta₁ z - (z - 1)⁻¹) s
      = iteratedDeriv 2 (logDeriv riemannZeta₁) s
        - iteratedDeriv 2 (fun z : ℂ => (z - 1)⁻¹) s :=
    iteratedDeriv_sub hcd₁ hcd₂
  have h3 : iteratedDeriv 2 (fun z : ℂ => (z - 1)⁻¹) s = 2 * (((s - 1) ^ 3)⁻¹) :=
    iteratedDeriv_two_inv_sub_one s
  rw [h1, h2, h3, div_eq_mul_inv]
  ring

theorem zetaSmoothBound : ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 4 → |s.im| ≤ 5 →
    |(logDeriv riemannZeta s + 1 / (s - 1)).re| ≤ M ∧
    |(iteratedDeriv 1 (logDeriv riemannZeta) s - 1 / (s - 1) ^ 2).re| ≤ M ∧
    |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 / (s - 1) ^ 3).re| ≤ M := by
  obtain ⟨C0, hC0⟩ := bound_iteratedDeriv 0
  obtain ⟨C1, hC1⟩ := bound_iteratedDeriv 1
  obtain ⟨C2, hC2⟩ := bound_iteratedDeriv 2
  have hb0 : ∀ s ∈ K, |(logDeriv riemannZeta₁ s).re| ≤ C0 := by
    intro s hs
    simpa only [iteratedDeriv_zero] using hC0 s hs
  refine ⟨|C0| + |C1| + |C2| + 1, by positivity, ?_⟩
  intro s h1 h2 h3
  have hsK : s ∈ K := ⟨le_of_lt h1, h2, h3⟩
  have hM0 : C0 ≤ |C0| + |C1| + |C2| + 1 := by
    linarith [le_abs_self C0, abs_nonneg C1, abs_nonneg C2]
  have hM1 : C1 ≤ |C0| + |C1| + |C2| + 1 := by
    linarith [le_abs_self C1, abs_nonneg C0, abs_nonneg C2]
  have hM2 : C2 ≤ |C0| + |C1| + |C2| + 1 := by
    linarith [le_abs_self C2, abs_nonneg C0, abs_nonneg C1]
  refine ⟨?_, ?_, ?_⟩
  · rw [smooth_zero s h1]
    exact le_trans (hb0 s hsK) hM0
  · rw [smooth_one s h1]
    exact le_trans (hC1 s hsK) hM1
  · rw [smooth_two s h1]
    exact le_trans (hC2 s hsK) hM2

end

end Work.ZeroFreeTables.Table4
