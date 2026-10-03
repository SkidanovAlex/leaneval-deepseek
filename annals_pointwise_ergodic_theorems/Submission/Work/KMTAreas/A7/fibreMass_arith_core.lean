/-
# The arithmetic core of the fibre-mass bound

`fibreMass_arith_core` is the elementary two-factor bookkeeping that turns the two
single-frequency `L¹`-computations (`fibreMass_sumA`, `fibreMass_sumB`) into the
derivative `∫`-bound (`fibreMass_pointwise`) with the reduced second frequency radius
`r₂ = min (N^{-d}) λ₂`.  The only content is the two-regime estimate

* `λ₂ ≤ max (λ₂ N^d) 1 · r₂`,
* `1 + λ₂ N^d ≤ 4 max (λ₂ N^d) 1`,
* `(1 + λ₂ N^d)^2 r₂ ≤ 4 max (λ₂ N^d) 1 · λ₂`,

together with `1 + 1/(λ₁ N) ≤ 3`, which gives the constant `9 · 4 = 36 ≤ 64`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassHbdDefs

namespace Work.KMTAreas.A7

/-- `λ₂` is dominated by `max (λ₂ N^d) 1 · r₂`: in the physical regime `λ₂ N^d ≥ 1` the two
factors multiply to `λ₂`, and in the degenerate regime `λ₂ ≤ N^{-d}` (only possible at `N = 1`)
the second factor is exactly `λ₂`. -/
private lemma fibLam₂_le_max_mul_fibR₂ (P : Polynomial ℤ) {N k₂ : ℕ} (hN : 1 ≤ N) :
    fibLam₂ P N k₂
      ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 * fibR₂ P N k₂ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hApos : (0 : ℝ) < fibLam₂ P N k₂ := fibLam₂_pos P N k₂
  rcases le_total (fibLam₂ P N k₂) (((N : ℝ) ^ P.natDegree)⁻¹) with h | h
  · have hR : fibR₂ P N k₂ = fibLam₂ P N k₂ := by
      unfold fibR₂; exact min_eq_right h
    rw [hR]
    calc fibLam₂ P N k₂ = 1 * fibLam₂ P N k₂ := (one_mul _).symm
      _ ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 * fibLam₂ P N k₂ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hApos)
  · have hR : fibR₂ P N k₂ = (((N : ℝ) ^ P.natDegree)⁻¹) := by
      unfold fibR₂; exact min_eq_left h
    rw [hR]
    have hcancel : fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree * ((N : ℝ) ^ P.natDegree)⁻¹
        = fibLam₂ P N k₂ := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hMpos), mul_one]
    calc fibLam₂ P N k₂
        = fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree * ((N : ℝ) ^ P.natDegree)⁻¹ := hcancel.symm
      _ ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 * ((N : ℝ) ^ P.natDegree)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (le_of_lt hMpos))

/-- `1 + λ₂ N^d ≤ 4 max (λ₂ N^d) 1`. -/
private lemma one_add_fibLam₂_mul_le (P : Polynomial ℤ) (N k₂ : ℕ) :
    1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree
      ≤ 4 * max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 := by
  have h1 : (1 : ℝ) ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 := le_max_right _ _
  have h2 : fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree
      ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 := le_max_left _ _
  linarith

/-- `(1 + λ₂ N^d)^2 r₂ ≤ 4 max (λ₂ N^d) 1 · λ₂`.  This is the sharp two-regime estimate:
dividing by `λ₂ r₂ > 0` it is `((1 + λ₂N^d)/(λ₂N^d))^2 ≤ 4` in the physical regime and
`(1 + λ₂N^d)^2 ≤ 4` in the degenerate one. -/
private lemma sq_one_add_fibLam₂_mul_fibR₂_le (P : Polynomial ℤ) {N k₂ : ℕ} (hN : 1 ≤ N) :
    (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2 * fibR₂ P N k₂
      ≤ 4 * max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 * fibLam₂ P N k₂ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hApos : (0 : ℝ) < fibLam₂ P N k₂ := fibLam₂_pos P N k₂
  have hxnn : 0 ≤ fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree := mul_nonneg hApos.le hMpos.le
  rcases le_total (fibLam₂ P N k₂) (((N : ℝ) ^ P.natDegree)⁻¹) with h | h
  · have hR : fibR₂ P N k₂ = fibLam₂ P N k₂ := by
      unfold fibR₂; exact min_eq_right h
    have hxle : fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_right h (le_of_lt hMpos)
      rwa [inv_mul_cancel₀ (ne_of_gt hMpos)] at h1
    have hsq : (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2 ≤ 4 := by
      have h2 : 1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree ≤ 2 := by linarith
      calc (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2
          ≤ 2 ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
        _ = 4 := by norm_num
    rw [hR, max_eq_right hxle]
    calc (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2 * fibLam₂ P N k₂
        ≤ 4 * fibLam₂ P N k₂ := mul_le_mul_of_nonneg_right hsq hApos.le
      _ = 4 * 1 * fibLam₂ P N k₂ := by ring
  · have hR : fibR₂ P N k₂ = (((N : ℝ) ^ P.natDegree)⁻¹) := by
      unfold fibR₂; exact min_eq_left h
    have hx1 : 1 ≤ fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree := by
      have h1 := mul_le_mul_of_nonneg_right h (le_of_lt hMpos)
      rwa [inv_mul_cancel₀ (ne_of_gt hMpos)] at h1
    have hsq : (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2
        ≤ 4 * (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2 := by nlinarith [hx1]
    rw [hR, max_eq_left hx1]
    have hcancel : fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree * ((N : ℝ) ^ P.natDegree)⁻¹
        = fibLam₂ P N k₂ := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hMpos), mul_one]
    have key : (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2 * ((N : ℝ) ^ P.natDegree)⁻¹
        = (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) * fibLam₂ P N k₂ := by
      rw [pow_two, mul_assoc, hcancel]
    calc (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2 * ((N : ℝ) ^ P.natDegree)⁻¹
        ≤ 4 * (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ 2 * ((N : ℝ) ^ P.natDegree)⁻¹ :=
          mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hMpos.le)
      _ = 4 * (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) * fibLam₂ P N k₂ := by
          rw [mul_assoc, key]; ring

/-- The `i₂` part of the arithmetic core:
`(1 + λ₂ N^d)^{i₂} λ₂^{1-i₂} ≤ 4 max (λ₂ N^d) 1 · r₂^{1-i₂}` for `i₂ ≤ 2`. -/
private lemma fibreMassAux_g (P : Polynomial ℤ) {N k₂ : ℕ} (hN : 1 ≤ N)
    (i₂ : ℕ) (hi₂ : i₂ ≤ 2) :
    (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ i₂
        * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ))
      ≤ 4 * max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1
          * (fibR₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) := by
  interval_cases i₂
  · norm_num
    have hA := fibLam₂_le_max_mul_fibR₂ P (N := N) (k₂ := k₂) hN
    have h0 : (0 : ℝ) ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 * fibR₂ P N k₂ :=
      mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (le_of_lt (fibR₂_pos P hN))
    linarith
  · norm_num
    exact one_add_fibLam₂_mul_le P N k₂
  · norm_num
    rw [← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ (fibLam₂_pos P N k₂) (fibR₂_pos P hN)]
    exact sq_one_add_fibLam₂_mul_fibR₂_le P hN

theorem fibreMass_arith_core (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (hN : 1 ≤ N)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) :
    (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁
      * (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ i₂
      * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ))
    ≤ 64 * max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1
        * (fibR₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hLam1N : (1 : ℝ) / 2 ≤ fibLam₁ N k₁ * (N : ℝ) := fibLam₁_mul_N_ge_half N k₁ hN
  have hLam1Npos : 0 < fibLam₁ N k₁ * (N : ℝ) := by linarith
  have hdiv2 : 1 / (fibLam₁ N k₁ * (N : ℝ)) ≤ 2 := by
    rw [div_le_iff₀ hLam1Npos]; linarith
  have hf9 : (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁ ≤ 9 := by
    have h3 : 1 + 1 / (fibLam₁ N k₁ * (N : ℝ)) ≤ 3 := by linarith
    have hnn : (0 : ℝ) ≤ 1 + 1 / (fibLam₁ N k₁ * (N : ℝ)) := by
      have := div_nonneg (zero_le_one : (0 : ℝ) ≤ 1) hLam1Npos.le
      linarith
    calc (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁ ≤ 3 ^ i₁ := pow_le_pow_left₀ hnn h3 i₁
      _ ≤ 3 ^ 2 := pow_le_pow_right₀ (by norm_num) hi₁
      _ = 9 := by norm_num
  have hg := fibreMassAux_g P (N := N) (k₂ := k₂) hN i₂ hi₂
  have hGnn : 0 ≤ (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ i₂
      * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) := by
    refine mul_nonneg (pow_nonneg ?_ _) (le_of_lt (zpow_pos (fibLam₂_pos P N k₂) _))
    have := mul_nonneg (fibLam₂_pos P N k₂).le (pow_nonneg hNpos.le P.natDegree)
    linarith
  have hmr : 0 ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1
      * (fibR₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) :=
    mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (le_of_lt (zpow_pos (fibR₂_pos P hN) _))
  calc (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁
        * (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ i₂
        * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ))
      = (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁
        * ((1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ i₂
            * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ))) := by rw [mul_assoc]
    _ ≤ 9 * (4 * max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1
            * (fibR₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ))) := mul_le_mul hf9 hg hGnn (by norm_num)
    _ ≤ 64 * max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1
        * (fibR₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ)) := by nlinarith [hmr]

end Work.KMTAreas.A7
