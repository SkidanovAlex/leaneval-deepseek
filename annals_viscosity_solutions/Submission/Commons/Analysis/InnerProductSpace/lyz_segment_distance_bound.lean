import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.InnerProductSpace

/-- **Decomposition of the squared distance to a line.**
For a nonzero vector `v`, the squared distance from `x` to the line through `0` and `v`,
`‖x‖² - (⟪x,v⟫)²/‖v‖²`, plus the squared distance of the projection coordinate
`⟪x,v⟫/‖v‖² - s` times `‖v‖²`, equals `‖x - s • v‖²`. -/
lemma norm_sq_sub_smul_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x v : F) (hv : v ≠ 0) (s : ℝ) :
    ‖x - s • v‖ ^ 2
      = (‖x‖ ^ 2 - (inner ℝ x v) ^ 2 / ‖v‖ ^ 2)
        + (inner ℝ x v / ‖v‖ ^ 2 - s) ^ 2 * ‖v‖ ^ 2 := by
  have hL : ‖v‖ ^ 2 ≠ 0 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-- Elementary consequence: if `0 ≤ d` and `d ^ 2 ≤ 4 * S * Ψ` with `S, Ψ ≥ 0`
then `d ≤ 2 * sqrt (S * Ψ)`. -/
private lemma le_two_sqrt_of_sq_le {d S Ψ : ℝ} (hS : 0 ≤ S) (hΨ : 0 ≤ Ψ) (hd : 0 ≤ d)
    (h : d ^ 2 ≤ 4 * (S * Ψ)) : d ≤ 2 * Real.sqrt (S * Ψ) := by
  have hsp : 0 ≤ S * Ψ := mul_nonneg hS hΨ
  have h2 : (2 * Real.sqrt (S * Ψ)) ^ 2 = 4 * (S * Ψ) := by
    rw [mul_pow, Real.sq_sqrt hsp]; ring
  have hle : d ^ 2 ≤ (2 * Real.sqrt (S * Ψ)) ^ 2 := by rw [h2]; exact h
  calc d = Real.sqrt (d ^ 2) := (Real.sqrt_sq hd).symm
    _ ≤ Real.sqrt ((2 * Real.sqrt (S * Ψ)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 2 * Real.sqrt (S * Ψ) := Real.sqrt_sq (by positivity)

/-- Elementary consequence: `2 * Ψ ≤ 2 * sqrt (S * Ψ)` when `0 < S` and `0 ≤ Ψ ≤ S / 2`. -/
private lemma two_mul_le_two_sqrt {S Ψ : ℝ} (hS : 0 < S) (hΨ : 0 ≤ Ψ) (hΨS : Ψ ≤ S / 2) :
    2 * Ψ ≤ 2 * Real.sqrt (S * Ψ) := by
  have hsp : 0 ≤ S * Ψ := by positivity
  have h : Ψ ≤ Real.sqrt (S * Ψ) := by
    rw [Real.le_sqrt hΨ hsp]
    nlinarith [hΨS, hS, hΨ, mul_nonneg hΨ (by linarith : (0:ℝ) ≤ S - Ψ)]
  linarith

/-- **Geometric core.**  Given two vectors `x`, `v` with `‖v‖ ≥ S/2`, a bound on the sum of the
distances `‖x‖ + ‖x - v‖ ≤ S/2 + 2 Ψ`, and that `t ∈ [0,1]` minimises `‖x - s v‖`, the distance
`‖x - t v‖` is at most `2 sqrt (S Ψ)`. -/
private theorem segment_dist_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x v : F} {t S Ψ : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hS : 0 < S) (hΨ : 0 ≤ Ψ)
    (hΨS : Ψ ≤ S / 2) (hL : S / 2 ≤ ‖v‖)
    (hlen : ‖x‖ + ‖x - v‖ ≤ S / 2 + 2 * Ψ)
    (hmin : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖x - t • v‖ ≤ ‖x - s • v‖) :
    ‖x - t • v‖ ≤ 2 * Real.sqrt (S * Ψ) := by
  have hv : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hL
    linarith
  have hLnonneg : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
  -- squared distance to the line and projection coordinate
  set D : ℝ := ‖x‖ ^ 2 - (inner ℝ x v) ^ 2 / ‖v‖ ^ 2 with hDdef
  set c : ℝ := inner ℝ x v / ‖v‖ ^ 2 with hcdef
  have hD_nonneg : 0 ≤ D := by
    have hcs : (inner ℝ x v) ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
      have h := real_inner_mul_inner_self_le x v
      rw [real_inner_self_eq_norm_sq x, real_inner_self_eq_norm_sq v] at h
      rw [sq]; exact h
    rw [hDdef]
    have hL2pos : 0 < ‖v‖ ^ 2 := by positivity
    have : (inner ℝ x v) ^ 2 / ‖v‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [div_le_iff₀ hL2pos]; linarith
    linarith
  have hdecomp : ∀ s : ℝ, ‖x - s • v‖ ^ 2 = D + (c - s) ^ 2 * ‖v‖ ^ 2 := by
    intro s
    have h := norm_sq_sub_smul_eq x v hv s
    rw [hDdef, hcdef]
    exact h
  have hcs2 : ∀ s ∈ Set.Icc (0:ℝ) 1, (c - t) ^ 2 ≤ (c - s) ^ 2 := by
    intro s hs
    have h1 : ‖x - t • v‖ ^ 2 ≤ ‖x - s • v‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hmin s hs) 2
    rw [hdecomp t, hdecomp s] at h1
    have hL2pos : 0 < ‖v‖ ^ 2 := by positivity
    nlinarith [h1, hL2pos]
  -- case distinction on t
  by_cases ht0 : t = 0
  · -- t = 0
    have hc0 : c ≤ 0 := by
      by_contra hc
      push Not at hc
      rcases lt_or_ge 1 c with hlt | hle
      · have hmem : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
        have h := hcs2 1 hmem
        rw [ht0] at h
        nlinarith
      · have hmem : c ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hc, hle⟩
        have h := hcs2 c hmem
        rw [ht0] at h
        nlinarith
    have hsub : ‖x - t • v‖ = ‖x‖ := by rw [ht0, zero_smul, sub_zero]
    rw [hsub]
    have hxv_ge : S / 2 ≤ ‖x - v‖ := by
      have h2 : ‖x - v‖ ^ 2 = D + (c - 1) ^ 2 * ‖v‖ ^ 2 := by
        have h := hdecomp 1; rwa [one_smul] at h
      have hc1 : (1:ℝ) ≤ (c - 1) ^ 2 := by nlinarith [hc0]
      have hge : ‖v‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
        rw [h2]
        nlinarith [hD_nonneg, hc1, sq_nonneg ‖v‖, mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖v‖)]
      have : ‖v‖ ≤ ‖x - v‖ := by
        have := sq_le_sq.mp hge
        rw [abs_of_nonneg hLnonneg, abs_of_nonneg (norm_nonneg _)] at this
        exact this
      linarith
    have : ‖x‖ ≤ 2 * Ψ := by linarith
    exact le_trans this (two_mul_le_two_sqrt hS hΨ hΨS)
  · by_cases ht1 : t = 1
    · -- t = 1
      have hc1 : 1 ≤ c := by
        by_contra hc
        push Not at hc
        rcases lt_or_ge c 0 with hlt | hle
        · have hmem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
          have h := hcs2 0 hmem
          rw [ht1] at h
          nlinarith
        · have hmem : c ∈ Set.Icc (0:ℝ) 1 := ⟨hle, le_of_lt hc⟩
          have h := hcs2 c hmem
          rw [ht1] at h
          nlinarith
      have hsub : ‖x - t • v‖ = ‖x - v‖ := by rw [ht1, one_smul]
      rw [hsub]
      have hx_ge : S / 2 ≤ ‖x‖ := by
        have h2 : ‖x‖ ^ 2 = D + c ^ 2 * ‖v‖ ^ 2 := by
          have h := hdecomp 0
          rw [zero_smul, sub_zero] at h
          rw [h]; ring
        have hc2 : (1:ℝ) ≤ c ^ 2 := by nlinarith [hc1]
        have hge : ‖v‖ ^ 2 ≤ ‖x‖ ^ 2 := by
          rw [h2]
          nlinarith [hD_nonneg, hc2, sq_nonneg ‖v‖, mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖v‖)]
        have : ‖v‖ ≤ ‖x‖ := by
          have := sq_le_sq.mp hge
          rw [abs_of_nonneg hLnonneg, abs_of_nonneg (norm_nonneg _)] at this
          exact this
        linarith
      have : ‖x - v‖ ≤ 2 * Ψ := by linarith
      exact le_trans this (two_mul_le_two_sqrt hS hΨ hΨS)
    · -- 0 < t < 1
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have htlt1 : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hc_ge0 : 0 ≤ c := by
        by_contra hc
        push Not at hc
        have hmem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
        have h := hcs2 0 hmem
        nlinarith [h, mul_pos htpos (by linarith : (0:ℝ) < t - 2 * c)]
      have hc_le1 : c ≤ 1 := by
        by_contra hc
        push Not at hc
        have hmem : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
        have h := hcs2 1 hmem
        nlinarith [h, mul_neg_of_neg_of_pos (by linarith : t - 1 < 0) (by linarith : (0:ℝ) < 2 * c - 1 - t)]
      have hct : c = t := by
        have hmem : c ∈ Set.Icc (0:ℝ) 1 := ⟨hc_ge0, hc_le1⟩
        have h := hcs2 c hmem
        nlinarith
      have hdD : ‖x - t • v‖ ^ 2 = D := by
        rw [hdecomp t, hct, sub_self]; simp
      have hx2 : ‖x‖ ^ 2 = D + c ^ 2 * ‖v‖ ^ 2 := by
        have h := hdecomp 0
        rw [zero_smul, sub_zero] at h
        rw [h]; ring
      have hxv2 : ‖x - v‖ ^ 2 = D + (1 - c) ^ 2 * ‖v‖ ^ 2 := by
        have h := hdecomp 1
        rw [one_smul] at h
        rw [h]; ring
      -- key product estimate
      have hprod : D + ‖v‖ ^ 2 * c * (1 - c) ≤ ‖x‖ * ‖x - v‖ := by
        have hsq : (D + ‖v‖ ^ 2 * c * (1 - c)) ^ 2 ≤ (‖x‖ * ‖x - v‖) ^ 2 := by
          rw [mul_pow, hx2, hxv2]
          nlinarith [mul_nonneg hD_nonneg (sq_nonneg (‖v‖ * (2 * c - 1)))]
        have hnn1 : 0 ≤ D + ‖v‖ ^ 2 * c * (1 - c) := by
          nlinarith [hD_nonneg, mul_nonneg hc_ge0 (sub_nonneg.mpr hc_le1), sq_nonneg ‖v‖]
        have hnn2 : 0 ≤ ‖x‖ * ‖x - v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have h := sq_le_sq.mp hsq
        rwa [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at h
      have hp2 : ‖v‖ ^ 2 + 4 * D ≤ (‖x‖ + ‖x - v‖) ^ 2 := by
        nlinarith [hprod, hx2, hxv2]
      have hp_sq : (‖x‖ + ‖x - v‖) ^ 2 ≤ (S / 2 + 2 * Ψ) ^ 2 :=
        pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) hlen 2
      have hL_sq : (S / 2) ^ 2 ≤ ‖v‖ ^ 2 :=
        pow_le_pow_left₀ (by linarith) hL 2
      have h4D : 4 * D ≤ 2 * S * Ψ + 4 * Ψ ^ 2 := by
        nlinarith [hp2, hp_sq, hL_sq]
      have hDle : D ≤ 4 * (S * Ψ) := by
        nlinarith [h4D, hΨS, hΨ, mul_le_mul_of_nonneg_right hΨS hΨ]
      have hfin : ‖x - t • v‖ ^ 2 ≤ 4 * (S * Ψ) := by rw [hdD]; exact hDle
      exact le_two_sqrt_of_sq_le (le_of_lt hS) hΨ (norm_nonneg _) hfin

/-- The requested statement. -/
theorem lyz_segment_distance_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {q y ξ : F} {t S Ψ : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hS : 0 < S) (hΨ : 0 ≤ Ψ)
    (hΨS : Ψ ≤ S / 2) (hsep : S / 2 ≤ ‖q - y‖)
    (hlen : ‖ξ - q‖ + ‖ξ - y‖ ≤ S / 2 + 2 * Ψ)
    (hmin : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖ξ - (q + t • (y - q))‖ ≤ ‖ξ - (q + s • (y - q))‖) :
    ‖ξ - (q + t • (y - q))‖ ≤ 2 * Real.sqrt (S * Ψ) := by
  have hL : S / 2 ≤ ‖y - q‖ := by rw [norm_sub_rev]; exact hsep
  have hlen' : ‖ξ - q‖ + ‖(ξ - q) - (y - q)‖ ≤ S / 2 + 2 * Ψ := by
    have h : (ξ - q) - (y - q) = ξ - y := by abel
    rwa [h]
  have hmin' : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖(ξ - q) - t • (y - q)‖ ≤ ‖(ξ - q) - s • (y - q)‖ := by
    intro s hs
    have h1 : ξ - (q + t • (y - q)) = (ξ - q) - t • (y - q) := by abel
    have h2 : ξ - (q + s • (y - q)) = (ξ - q) - s • (y - q) := by abel
    rw [← h1, ← h2]
    exact hmin s hs
  have := segment_dist_bound (x := ξ - q) (v := y - q) ht hS hΨ hΨS hL hlen' hmin'
  have hg : ξ - (q + t • (y - q)) = (ξ - q) - t • (y - q) := by abel
  rwa [hg]

end Commons.Analysis.InnerProductSpace