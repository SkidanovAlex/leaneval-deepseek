/-
# HB Lemma 2.5 with `φ = 1/4` for characters of order dividing `4`

For every `k ≥ 3` and `ε' > 0` there is `Cb > 0` such that every non-principal character `χ` of a
modulus `N` with `χ ^ 4 = 1` satisfies

`‖L(σ+it,χ)‖ ≤ Cb · N^{((1/4)(1-σ)(1+1/k) + ε')} · (1+|t|)`

on the window `1 - 1/k ≤ σ ≤ 1 + log log N / log N`.

Two ingredients:

* `Work.LinnikAreas.LBoundSmall_holds` (HB Lemma 2.5 with `φ = 1/4` for `orderOf χ ≤ log N`),
  applied for `N ≥ 81`, where `χ ^ 4 = 1` and `χ ≠ 1` give `orderOf χ ≤ 4 ≤ Real.log 81 ≤ log N`;
* the convexity bound of `Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity` (exponent
  `1/2`) for `N ≤ 80`, where the extra factor `N^{(1/4)(1-σ)(1+1/k)} ≤ 80^{1/9}` is absorbed into
  the constant.  (Since `σ ≥ 1 - 1/k` with `k ≥ 3` we have `(1-σ)(1+1/k) ≤ 4/9`.)

This is `Work.ZeroFreeTables.XY.hbound_quarter_real` with the order bound `2` replaced by `4`
(and the threshold `8` by `81`), and is the analytic input consumed (via
`Submission.Work.LinnikAreas.l31free.lemma3_1_free_q4`) by `L52Hyp_eighth_le4`.
-/
import Mathlib
import Submission.Work.LinnikAreas.area1
import Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity

open DirichletCharacter

set_option maxHeartbeats 1000000

namespace Work.ZeroFreeTables

theorem hbound_quarter_pow_four :
    ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 4 = 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) := by
  intro k hk ε' hε'
  obtain ⟨C₁, hC₁pos, hb₁⟩ := Work.LinnikAreas.LBoundSmall_holds k hk ε' hε'
  obtain ⟨C₂, hC₂pos, hb₂⟩ :=
    Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity hε' k hk
  refine ⟨max C₁ (C₂ * 80 ^ ((1:ℝ)/9) * 2), lt_max_of_lt_left hC₁pos, ?_⟩
  intro N _inst χ hχ hχ4 σ t hσ hσle
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have h : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact_mod_cast h
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith only [hN1]
  by_cases hN : 81 ≤ N
  · -- `N ≥ 81`: `orderOf χ ≤ 4 ≤ log N`
    have hord4 : orderOf χ ≤ 4 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hχ4)
    have hlog81 : (4:ℝ) ≤ Real.log 81 := by
      have h : Real.log (81:ℝ) = 4 * Real.log 3 := by
        rw [show (81:ℝ) = 3 ^ 4 by norm_num, Real.log_pow]
        norm_num
      rw [h]
      have h3 : (1:ℝ) < Real.log 3 := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      linarith only [h3]
    have hlogN : (4:ℝ) ≤ Real.log (N:ℝ) := by
      have h81 : (81:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      exact le_trans hlog81 (Real.log_le_log (by norm_num) h81)
    have hord : (orderOf χ : ℝ) ≤ Real.log (N:ℝ) := by
      have h4 : ((orderOf χ : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hord4
      linarith only [hlogN, h4]
    have h := hb₁ χ hχ hord σ t hσ hσle
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  · -- `N ≤ 80`: convexity
    have hNle : N ≤ 80 := by omega
    have hNR : (N:ℝ) ≤ 80 := by exact_mod_cast hNle
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
    have hfac : (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))) ≤ (80:ℝ) ^ ((1:ℝ)/9) := by
      have h1 : (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))) ≤ (N:ℝ) ^ ((1:ℝ)/9) :=
        Real.rpow_le_rpow_of_exponent_le hN1 hE1
      have h2 : (N:ℝ) ^ ((1:ℝ)/9) ≤ (80:ℝ) ^ ((1:ℝ)/9) :=
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
    have h80 : (0:ℝ) ≤ (80:ℝ) ^ ((1:ℝ)/9) := Real.rpow_nonneg (by norm_num) _
    have hkey : C₂ * ((N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)))
          * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'))
        ≤ (max C₁ (C₂ * 80 ^ ((1:ℝ)/9) * 2))
          * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by
      have hC₂nn : (0:ℝ) ≤ C₂ := le_of_lt hC₂pos
      calc C₂ * ((N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'))
          = (C₂ * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by ring
        _ ≤ (C₂ * (80:ℝ) ^ ((1:ℝ)/9))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hC₂nn) hz
        _ ≤ (C₂ * 80 ^ ((1:ℝ)/9) * 2)
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (by linarith only [mul_nonneg hC₂nn h80, hC₂nn, h80]) hz
        _ ≤ (max C₁ (C₂ * 80 ^ ((1:ℝ)/9) * 2))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hz
    exact h.trans (mul_le_mul_of_nonneg_right hkey ht)

end Work.ZeroFreeTables
