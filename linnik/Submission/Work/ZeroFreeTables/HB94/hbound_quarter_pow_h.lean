/-
# HB Lemma 2.5 with `φ = 1/4` for characters with `χ ^ h = 1`

`Submission/Work/ZeroFreeTables/hbound_quarter_pow_four.lean` with the order bound `4` replaced
by a general `h ≥ 1` (threshold `81 ↦ ⌈exp h⌉₊ + 1`, `80^{1/9} ↦ (⌈exp h⌉₊ + 1)^{1/9}`).
-/
import Mathlib
import Submission.Work.LinnikAreas.area1
import Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity

open DirichletCharacter

set_option maxHeartbeats 1000000

namespace Work.ZeroFreeTables

theorem hbound_quarter_pow_h (h : ℕ) (hh : 1 ≤ h) :
    ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ h = 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) := by
  intro k hk ε' hε'
  obtain ⟨C₁, hC₁pos, hb₁⟩ := Work.LinnikAreas.LBoundSmall_holds k hk ε' hε'
  obtain ⟨C₂, hC₂pos, hb₂⟩ :=
    Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity hε' k hk
  set N₀ : ℕ := ⌈Real.exp (h : ℝ)⌉₊ + 1 with hN₀def
  have hN₀pos : (0:ℝ) < (N₀:ℝ) := by
    have : 0 < N₀ := by omega
    exact_mod_cast this
  refine ⟨max C₁ (C₂ * (N₀:ℝ) ^ ((1:ℝ)/9) * 2), lt_max_of_lt_left hC₁pos, ?_⟩
  intro N _inst χ hχ hχh σ t hσ hσle
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have h : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact_mod_cast h
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith only [hN1]
  have hexple : Real.exp (h:ℝ) ≤ (N₀:ℝ) := by
    have h1 : Real.exp (h:ℝ) ≤ (⌈Real.exp (h:ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (h:ℝ)⌉₊ : ℝ) ≤ (N₀:ℝ) := by
      rw [hN₀def]; push_cast; linarith only []
    linarith only [h1, h2]
  have hhle : (h:ℝ) ≤ Real.log (N₀:ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (h:ℝ)) hexple
    rwa [Real.log_exp] at h
  by_cases hN : N₀ ≤ N
  · -- `N ≥ N₀`: `orderOf χ ≤ h ≤ log N`
    have hordh : orderOf χ ≤ h :=
      Nat.le_of_dvd (by omega) (orderOf_dvd_iff_pow_eq_one.mpr hχh)
    have hNR : (N₀:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hlogN : (h:ℝ) ≤ Real.log (N:ℝ) :=
      le_trans hhle (Real.log_le_log hN₀pos hNR)
    have hord : (orderOf χ : ℝ) ≤ Real.log (N:ℝ) := by
      have hh' : ((orderOf χ : ℕ) : ℝ) ≤ (h:ℝ) := by exact_mod_cast hordh
      linarith only [hlogN, hh']
    have h := hb₁ χ hχ hord σ t hσ hσle
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  · -- `N < N₀`: convexity
    have hNle : N ≤ N₀ := le_of_lt (Nat.lt_of_not_le hN)
    have hNR : (N:ℝ) ≤ (N₀:ℝ) := by exact_mod_cast hNle
    have hk3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h1σ : (1:ℝ) - σ ≤ 1/(k:ℝ) := by linarith only [hσ]
    have hprod : (1 - σ) * (1 + 1/(k:ℝ)) ≤ 4/9 := by
      by_cases hσ1 : 0 ≤ 1 - σ
      · have h2 : (1:ℝ) + 1/(k:ℝ) ≤ 4/3 := by
          have h : 1/(k:ℝ) ≤ 1/3 := by
            rw [div_le_div_iff₀ hkpos (by norm_num : (0:ℝ) < 3)]
            linarith only [hk3]
          linarith only [h]
        have h3 : (1:ℝ)/(k:ℝ) ≤ 1/3 := by
          rw [div_le_div_iff₀ hkpos (by norm_num : (0:ℝ) < 3)]
          linarith only [hk3]
        have hp : (1 - σ) * (1 + 1/(k:ℝ)) ≤ (1/(k:ℝ)) * (4/3) :=
          mul_le_mul h1σ h2 (by positivity) (by positivity)
        linarith only [hp, h3, h2]
      · have h : (1:ℝ) - σ < 0 := by linarith only [hσ1]
        have hpos : (0:ℝ) < 1 + 1/(k:ℝ) := by positivity
        have hneg : (1 - σ) * (1 + 1/(k:ℝ)) < 0 := mul_neg_of_neg_of_pos h hpos
        linarith only [hneg]
    have hE1 : ((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) ≤ 1/9 := by
      linarith only [hprod]
    have hfac : (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)))
        ≤ (N₀:ℝ) ^ ((1:ℝ)/9) := by
      have h1 : (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))) ≤ (N:ℝ) ^ ((1:ℝ)/9) :=
        Real.rpow_le_rpow_of_exponent_le hN1 hE1
      have h2 : (N:ℝ) ^ ((1:ℝ)/9) ≤ (N₀:ℝ) ^ ((1:ℝ)/9) :=
        Real.rpow_le_rpow (le_of_lt hNpos) hNR (by norm_num)
      linarith only [h1, h2]
    have h := hb₂ χ hχ σ t hσ hσle
    have hexp : ((1:ℝ)/2) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'
        = ((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))
          + (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by ring
    rw [hexp, Real.rpow_add hNpos] at h
    have hz : (0:ℝ) ≤ (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
      Real.rpow_nonneg (le_of_lt hNpos) _
    have ht : (0:ℝ) ≤ 1 + |t| := by positivity
    have h80 : (0:ℝ) ≤ (N₀:ℝ) ^ ((1:ℝ)/9) := Real.rpow_nonneg (le_of_lt hN₀pos) _
    have hkey : C₂ * ((N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)))
          * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'))
        ≤ (max C₁ (C₂ * (N₀:ℝ) ^ ((1:ℝ)/9) * 2))
          * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by
      have hC₂nn : (0:ℝ) ≤ C₂ := le_of_lt hC₂pos
      calc C₂ * ((N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'))
          = (C₂ * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by ring
        _ ≤ (C₂ * (N₀:ℝ) ^ ((1:ℝ)/9))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hC₂nn) hz
        _ ≤ (C₂ * (N₀:ℝ) ^ ((1:ℝ)/9) * 2)
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (by linarith only [mul_nonneg hC₂nn h80, hC₂nn, h80]) hz
        _ ≤ (max C₁ (C₂ * (N₀:ℝ) ^ ((1:ℝ)/9) * 2))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hz
    exact h.trans (mul_le_mul_of_nonneg_right hkey ht)

end Work.ZeroFreeTables
