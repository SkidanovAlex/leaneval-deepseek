import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.radius_numerics

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-!
# The constants of the gluing lemma

This module produces the two *small constants* of the gluing construction: a scale `lam`
for the perturbation and a threshold `ε₀` for the perturbation parameter, small enough
that all the estimates used in the construction of the gluing datum hold.

Both are pure real-arithmetic existence statements; the only input from the geometry is
`0 < innerRad c` (and `0 ≤ farRad c`), which comes from `radius_numerics`.
-/

/-- Choosing the small scale `lam`: if `I > 0` and `F ≥ 0`, there is `lam > 0` with
`lam * Q₀ ≤ 1` and `lam * Q₀ * Kχ * (4 * (F + 1) ^ 2) ≤ I`. -/
theorem exists_lam_scale (I F Q₀ Kχ : ℝ) (hI : 0 < I) (hF : 0 ≤ F)
    (hQ₀ : 0 ≤ Q₀) (hKχ : 0 ≤ Kχ) :
    ∃ lam : ℝ, 0 < lam ∧ lam * Q₀ ≤ 1 ∧ lam * Q₀ * Kχ * (4 * (F + 1) ^ 2) ≤ I := by
  have hF1 : (0 : ℝ) < F + 1 := by linarith
  have hFsq : (0 : ℝ) < (F + 1) ^ 2 := pow_pos hF1 2
  have hDpos : (0 : ℝ) < 4 * (F + 1) ^ 2 := by linarith
  have hP : 0 ≤ Q₀ * Kχ := mul_nonneg hQ₀ hKχ
  have hden : 0 < (Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2) := mul_pos (by linarith) hDpos
  refine ⟨min (1 / (Q₀ + 1)) (I / ((Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2))), ?_, ?_, ?_⟩
  · exact lt_min (div_pos one_pos (by linarith)) (div_pos hI hden)
  · have hle : min (1 / (Q₀ + 1)) (I / ((Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2))) ≤
        1 / (Q₀ + 1) := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_right hle hQ₀
    have hone : (1 / (Q₀ + 1)) * Q₀ ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith : (0 : ℝ) < Q₀ + 1)]
      linarith
    linarith [hmul, hone]
  · have hle : min (1 / (Q₀ + 1)) (I / ((Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2))) ≤
        I / ((Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hle (mul_nonneg hP hDpos.le)
    have hone : (I / ((Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2))) * (Q₀ * Kχ * (4 * (F + 1) ^ 2)) ≤ I := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [mul_pos hI hDpos]
    have hconv : min (1 / (Q₀ + 1)) (I / ((Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2))) * Q₀ * Kχ *
        (4 * (F + 1) ^ 2) =
        min (1 / (Q₀ + 1)) (I / ((Q₀ * Kχ + 1) * (4 * (F + 1) ^ 2))) *
          (Q₀ * Kχ * (4 * (F + 1) ^ 2)) := by ring
    linarith [hmul, hone, hconv]

/-- The threshold `ε₀` for the perturbation parameter: given `lam` with
`lam * Q₀ * Kχ * (4 * (F + 1) ^ 2) ≤ I`, all the estimates of the gluing construction
hold for every `ε` with `0 < ε < ε₀`. -/
theorem exists_eps_scale (I F lam Q₀ Q₁ Kχ : ℝ) (hI : 0 < I) (hF : 0 ≤ F) (hlam : 0 < lam)
    (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁) (hKχ : 0 ≤ Kχ)
    (hA : lam * Q₀ * Kχ * (4 * (F + 1) ^ 2) ≤ I) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ε * (lam * Q₀) ≤ 1 ∧
      ε * ((lam * Q₀) * Kχ + lam * Q₁) ≤ I ∧
      ε * (lam * Q₁ + 2 * (lam * Q₀) * Kχ) < 2 * I ∧
      ε * (lam * Q₀) * Kχ / I ≤ ε ∧
      ε * (lam * Q₀) * Kχ / I ≤ 1 / 2 ∧
      4 * (ε * (lam * Q₀) * Kχ / I) * (F + 1) ^ 2 ≤ ε := by
  have hF1 : (0 : ℝ) < F + 1 := by linarith
  have hDpos : (0 : ℝ) < 4 * (F + 1) ^ 2 := by have := pow_pos hF1 2; linarith
  have hDge1 : (1 : ℝ) ≤ 4 * (F + 1) ^ 2 := by nlinarith [sq_nonneg F, hF]
  have hDge4 : (4 : ℝ) ≤ 4 * (F + 1) ^ 2 := by nlinarith [sq_nonneg F, hF]
  have hLnn : 0 ≤ lam * Q₀ := mul_nonneg hlam.le hQ₀
  have hL1 : 0 < lam * Q₀ + 1 := by linarith
  have hAnn : 0 ≤ (lam * Q₀) * Kχ := mul_nonneg hLnn hKχ
  have hBnn : 0 ≤ (lam * Q₀) * Kχ + lam * Q₁ := by
    have := mul_nonneg hlam.le hQ₁
    linarith
  have hCnn : 0 ≤ lam * Q₁ + 2 * (lam * Q₀) * Kχ := by
    have h1 := mul_nonneg hlam.le hQ₁
    have h2 := hAnn
    nlinarith
  have hu : (lam * Q₀) * Kχ / I ≤ 1 / (4 * (F + 1) ^ 2) := by
    rw [div_le_iff₀ hI, one_div_mul_eq_div]
    exact (le_div_iff₀ hDpos).mpr hA
  have hu1 : (lam * Q₀) * Kχ / I ≤ 1 := hu.trans ((div_le_one hDpos).mpr hDge1)
  have hu4 : (lam * Q₀) * Kχ / I ≤ 1 / 4 :=
    hu.trans (one_div_le_one_div_of_le (by norm_num) hDge4)
  have hAInn : 0 ≤ (lam * Q₀) * Kχ / I := div_nonneg hAnn hI.le
  let ε₀ : ℝ := min (min (min 1 (1 / (lam * Q₀ + 1))) (I / ((lam * Q₀) * Kχ + lam * Q₁ + 1)))
    (2 * I / (lam * Q₁ + 2 * (lam * Q₀) * Kχ + 1))
  have hB1 : 0 < (lam * Q₀) * Kχ + lam * Q₁ + 1 := by linarith
  have hC1 : 0 < lam * Q₁ + 2 * (lam * Q₀) * Kχ + 1 := by linarith
  have hε₀pos : 0 < ε₀ :=
    lt_min (lt_min (lt_min one_pos (div_pos one_pos hL1)) (div_pos hI hB1))
      (div_pos (by linarith) hC1)
  have hε₀le1 : ε₀ ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε₀L : ε₀ ≤ 1 / (lam * Q₀ + 1) :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε₀B : ε₀ ≤ I / ((lam * Q₀) * Kχ + lam * Q₁ + 1) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hε₀C : ε₀ ≤ 2 * I / (lam * Q₁ + 2 * (lam * Q₀) * Kχ + 1) := min_le_right _ _
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hεpos hεlt
  have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεlt hε₀le1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hεle : ε ≤ 1 / (lam * Q₀ + 1) := by linarith [hεlt, hε₀L]
    have hmul := mul_le_mul_of_nonneg_right hεle hLnn
    have hone : (1 / (lam * Q₀ + 1)) * (lam * Q₀) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one hL1]
      linarith
    linarith [hmul, hone]
  · have hεle : ε ≤ I / ((lam * Q₀) * Kχ + lam * Q₁ + 1) := by linarith [hεlt, hε₀B]
    have hmul := mul_le_mul_of_nonneg_right hεle hBnn
    have hone : (I / ((lam * Q₀) * Kχ + lam * Q₁ + 1)) * ((lam * Q₀) * Kχ + lam * Q₁) ≤ I := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB1]
      nlinarith [hI]
    linarith [hmul, hone]
  · by_cases hC0 : lam * Q₁ + 2 * (lam * Q₀) * Kχ = 0
    · rw [hC0, mul_zero]
      linarith [hI]
    · have hCpos : 0 < lam * Q₁ + 2 * (lam * Q₀) * Kχ := lt_of_le_of_ne hCnn (Ne.symm hC0)
      have hεle : ε < 2 * I / (lam * Q₁ + 2 * (lam * Q₀) * Kχ + 1) := by linarith [hεlt, hε₀C]
      have hmul := mul_lt_mul_of_pos_right hεle hCpos
      have hone : (2 * I / (lam * Q₁ + 2 * (lam * Q₀) * Kχ + 1)) *
          (lam * Q₁ + 2 * (lam * Q₀) * Kχ) < 2 * I := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hC1]
        nlinarith [hI]
      linarith [hmul, hone]
  · calc ε * (lam * Q₀) * Kχ / I = ε * (((lam * Q₀) * Kχ) / I) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hu1 hεpos.le
      _ = ε := by ring
  · calc ε * (lam * Q₀) * Kχ / I = ε * (((lam * Q₀) * Kχ) / I) := by ring
      _ ≤ 1 * (1 / 4) := mul_le_mul hε1 hu4 hAInn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  · have hkey : 4 * (((lam * Q₀) * Kχ) / I) * (F + 1) ^ 2 ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hu hDpos.le
      rw [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h
      linarith [h]
    calc 4 * (ε * (lam * Q₀) * Kχ / I) * (F + 1) ^ 2 =
          ε * (4 * (((lam * Q₀) * Kχ) / I) * (F + 1) ^ 2) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hkey hεpos.le
      _ = ε := by ring

theorem glue_constants (c : ℂ) {Q₀ Q₁ Kχ : ℝ} (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁) (hKχ : 0 ≤ Kχ) :
    ∃ lam : ℝ, 0 < lam ∧ lam * Q₀ ≤ 1 ∧
      lam * Q₀ * Kχ ≤ Work.FBif.innerRad c / (4 * (Work.FBif.farRad c + 1) ^ 2) ∧
      (lam * Q₀) * Kχ * (4 * (Work.FBif.farRad c + 1) ^ 2) ≤ Work.FBif.innerRad c ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ε * (lam * Q₀) ≤ 1 ∧
        ε * ((lam * Q₀) * Kχ + lam * Q₁) ≤ Work.FBif.innerRad c ∧
        ε * (lam * Q₁ + 2 * (lam * Q₀) * Kχ) < 2 * Work.FBif.innerRad c ∧
        ε * (lam * Q₀) * Kχ / Work.FBif.innerRad c ≤ ε ∧
        ε * (lam * Q₀) * Kχ / Work.FBif.innerRad c ≤ 1 / 2 ∧
        4 * (ε * (lam * Q₀) * Kχ / Work.FBif.innerRad c) * (Work.FBif.farRad c + 1) ^ 2 ≤ ε := by
  have hFpos : 0 < farRad c := (radius_numerics c).1
  have hIpos : 0 < innerRad c := (radius_numerics c).2.1
  obtain ⟨lam, hlampos, hlamQ₀, hlam3⟩ :=
    exists_lam_scale (innerRad c) (farRad c) Q₀ Kχ hIpos hFpos.le hQ₀ hKχ
  have hDpos : 0 < 4 * (farRad c + 1) ^ 2 := by
    have := pow_pos (by linarith : (0 : ℝ) < farRad c + 1) 2
    linarith
  have hlam2 : lam * Q₀ * Kχ ≤ innerRad c / (4 * (farRad c + 1) ^ 2) :=
    (le_div_iff₀ hDpos).mpr hlam3
  obtain ⟨ε₀, hε₀pos, hε⟩ :=
    exists_eps_scale (innerRad c) (farRad c) lam Q₀ Q₁ Kχ hIpos hFpos.le hlampos hQ₀ hQ₁ hKχ hlam3
  exact ⟨lam, hlampos, hlamQ₀, hlam2, hlam3, ε₀, hε₀pos, hε⟩

end Work.FBif
