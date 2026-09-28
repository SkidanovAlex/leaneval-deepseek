import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.MM2.loc_arith
import Submission.Work.HP.six_le_NN

namespace Work.HP.MM2

open Filter

theorem mix_tail_arith_final (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (K : ℝ) (hK : 0 < K)
    (hN : 2 * d + 1 ≤ Work.HP.NN d n) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → ∀ A : ℝ, B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      K * (1 + Real.log A) ^ 3 * Real.log B * (Work.HP.bigW (Work.HP.wOf B) : ℝ)
          ≤ A ^ (((Work.HP.NN d n - 2 : ℕ) : ℝ) / 4) ∧
      ∀ x : Fin (n + 1) → ℤ, Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
        K * (1 + Real.log A) ^ 2 * Real.log B * (Work.HP.bigW (Work.HP.wOf B) : ℝ) *
          Work.HP.eNorm (Work.HP.veronese d n x) ≤ A ^ (Work.HP.NN d n - 2) := by
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hN2ge4 : 4 ≤ NN d n - 2 := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₁, c₂, hc₁, hc₂, hbound⟩ := eNorm_veronese_bounds d n hd1
  have hnd_pos : (0:ℝ) < (n:ℝ) + 1 - d := by
    have : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
    linarith
  have hr_le : (d:ℝ) / ((n:ℝ) + 1 - d) ≤ (d:ℝ) := by
    have hden : (1:ℝ) ≤ (n:ℝ) + 1 - d := by
      have : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
      linarith
    rw [div_le_iff₀ hnd_pos]
    calc (d:ℝ) = (d:ℝ) * 1 := by ring
      _ ≤ (d:ℝ) * ((n:ℝ) + 1 - d) := mul_le_mul_of_nonneg_left hden (by positivity)
  have hNm2 : (2*(d:ℝ) - 1) ≤ ((NN d n - 2 : ℕ):ℝ) := by
    have h2 : (2:ℕ) ≤ NN d n := by omega
    have hcast : ((NN d n - 2 : ℕ):ℝ) = ((NN d n : ℕ):ℝ) - 2 := by
      rw [Nat.cast_sub h2]; norm_num
    rw [hcast]
    have h2' : ((2*d+1 : ℕ):ℝ) ≤ ((NN d n:ℕ):ℝ) := by exact_mod_cast hN
    push_cast at h2'
    linarith
  have hd2r : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hgap_pos : 0 < (5:ℝ)/6*((NN d n - 2:ℕ):ℝ) - (d:ℝ)/((n:ℝ)+1-d) := by
    have h1 : (5:ℝ)/6*(2*(d:ℝ)-1) ≤ (5:ℝ)/6*((NN d n - 2:ℕ):ℝ) :=
      mul_le_mul_of_nonneg_left hNm2 (by norm_num)
    have h4 : (1:ℝ)/2 ≤ (5:ℝ)/6*(2*(d:ℝ)-1) - (d:ℝ) := by nlinarith [hd2r]
    linarith [h1, h4, hr_le]
  set r : ℝ := (d:ℝ)/((n:ℝ)+1-d) with hrdef
  set e : ℝ := (5:ℝ)/6*((NN d n - 2:ℕ):ℝ) - r with hedef
  have he_pos : 0 < e := by rw [hedef, hrdef]; exact hgap_pos
  have hg1 : ∀ᶠ B in Filter.atTop,
      27 * K * (Real.log B)^4 * ((bigW (wOf B):ℕ):ℝ) ≤ B^((5:ℝ)/6) := by
    have := la_const_pow_log_mul_bigW_pow_le (27*K) 4 1 (by norm_num) (by norm_num : (0:ℝ) < 5/6)
    simpa using this
  have hg2 : ∀ᶠ B in Filter.atTop,
      9*c₂*K*(Real.log B)^3*((bigW (wOf B):ℕ):ℝ) ≤ B^e := by
    have := la_const_pow_log_mul_bigW_pow_le (9*c₂*K) 3 1 (by norm_num) he_pos
    simpa using this
  have hBge1 : ∀ᶠ B in Filter.atTop, (1:ℝ) ≤ B := eventually_ge_atTop 1
  have hlogBge2 : ∀ᶠ B in Filter.atTop, (2:ℝ) ≤ Real.log B :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  have hev : ∀ᶠ B in Filter.atTop, ∀ A : ℝ, B^((5:ℝ)/6) ≤ A → A ≤ B^2 →
      (K * (1 + Real.log A)^3 * Real.log B * ((bigW (wOf B):ℕ):ℝ)
          ≤ A ^ (((NN d n - 2:ℕ):ℝ)/4)) ∧
      (∀ x : Fin (n+1) → ℤ, eNorm x ≤ B^(1/((n:ℝ)+1-d)) →
        K * (1 + Real.log A)^2 * Real.log B * ((bigW (wOf B):ℕ):ℝ) *
          eNorm (veronese d n x) ≤ A ^ (NN d n - 2)) := by
    filter_upwards [hBge1, hlogBge2, hg1, hg2] with B hB1 hlogB2 hg1 hg2
    intro A hA1 hA2
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
    have hL1 : (1:ℝ) ≤ Real.log B := by linarith
    have hLpos : 0 < Real.log B := by linarith
    have hA_ge1 : 1 ≤ A := le_trans (Real.one_le_rpow hB1 (by norm_num)) hA1
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge1
    have hLA_ge1 : 1 ≤ Real.log A := by
      have h1 : Real.log (B^((5:ℝ)/6)) ≤ Real.log A :=
        Real.log_le_log (Real.rpow_pos_of_pos hBpos _) hA1
      rw [Real.log_rpow hBpos] at h1
      nlinarith
    have hLA_le : Real.log A ≤ 2 * Real.log B := by
      have h1 : Real.log A ≤ Real.log (B^2) := Real.log_le_log hApos hA2
      rw [Real.log_pow] at h1
      norm_num at h1
      linarith
    have h1LA_le : 1 + Real.log A ≤ 3 * Real.log B := by nlinarith [hLA_le, hL1]
    have h1LA_nn : 0 ≤ 1 + Real.log A := by linarith
    have hdiv4ge1 : (1:ℝ) ≤ ((NN d n - 2:ℕ):ℝ)/4 := by
      have : (4:ℝ) ≤ ((NN d n - 2:ℕ):ℝ) := by exact_mod_cast hN2ge4
      linarith
    refine ⟨?_, ?_⟩
    · -- first claim
      have hRHS : A ≤ A ^ (((NN d n - 2:ℕ):ℝ)/4) := by
        calc A = A^(1:ℝ) := (Real.rpow_one A).symm
          _ ≤ A^(((NN d n - 2:ℕ):ℝ)/4) :=
              Real.rpow_le_rpow_of_exponent_le hA_ge1 hdiv4ge1
      have hp : (1 + Real.log A)^3 ≤ 27 * (Real.log B)^3 := by
        have h := pow_le_pow_left₀ h1LA_nn h1LA_le 3
        calc (1 + Real.log A)^3 ≤ (3*Real.log B)^3 := h
          _ = 27 * (Real.log B)^3 := by ring
      have hnn : 0 ≤ K * Real.log B * ((bigW (wOf B):ℕ):ℝ) :=
        mul_nonneg (mul_nonneg hK.le hLpos.le) (Nat.cast_nonneg _)
      have ha : K * Real.log B * ((bigW (wOf B):ℕ):ℝ) * (1 + Real.log A)^3
          ≤ K * Real.log B * ((bigW (wOf B):ℕ):ℝ) * (27 * (Real.log B)^3) :=
        mul_le_mul_of_nonneg_left hp hnn
      calc K * (1 + Real.log A)^3 * Real.log B * ((bigW (wOf B):ℕ):ℝ)
          = K * Real.log B * ((bigW (wOf B):ℕ):ℝ) * (1 + Real.log A)^3 := by ring
        _ ≤ K * Real.log B * ((bigW (wOf B):ℕ):ℝ) * (27 * (Real.log B)^3) := ha
        _ = 27 * K * (Real.log B)^4 * ((bigW (wOf B):ℕ):ℝ) := by ring
        _ ≤ B^((5:ℝ)/6) := hg1
        _ ≤ A := hA1
        _ ≤ A ^ (((NN d n - 2:ℕ):ℝ)/4) := hRHS
    · intro x hx
      have hx_nn : 0 ≤ eNorm x := eNorm_toR_nonneg x
      have hver_le : eNorm (veronese d n x) ≤ c₂ * B^r := by
        have h := (hbound x).2
        have hpow : eNorm x ^ d ≤ B^r := by
          have h1 : eNorm x ^ d ≤ (B^(1/((n:ℝ)+1-d)))^d :=
            pow_le_pow_left₀ hx_nn hx d
          refine le_trans h1 (le_of_eq ?_)
          rw [← Real.rpow_natCast (B^(1/((n:ℝ)+1-d))) d, ← Real.rpow_mul hBpos.le]
          congr 1
          rw [hrdef]
          rw [one_div, inv_mul_eq_div]
        calc eNorm (veronese d n x) ≤ c₂ * eNorm x ^ d := h
          _ ≤ c₂ * B^r := mul_le_mul_of_nonneg_left hpow hc₂.le
      have h1LA2 : (1 + Real.log A)^2 ≤ 9 * (Real.log B)^2 := by
        have h := pow_le_pow_left₀ h1LA_nn h1LA_le 2
        calc (1 + Real.log A)^2 ≤ (3*Real.log B)^2 := h
          _ = 9 * (Real.log B)^2 := by ring
      have hKLW_nn : 0 ≤ K * Real.log B * ((bigW (wOf B):ℕ):ℝ) :=
        mul_nonneg (mul_nonneg hK.le hLpos.le) (Nat.cast_nonneg _)
      have hstep : K * (1 + Real.log A)^2 * Real.log B * ((bigW (wOf B):ℕ):ℝ) * c₂ * B^r
          ≤ K * (9*(Real.log B)^2) * Real.log B * ((bigW (wOf B):ℕ):ℝ) * c₂ * B^r := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hBpos.le _)
        apply mul_le_mul_of_nonneg_right _ hc₂.le
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hLpos.le
        exact mul_le_mul_of_nonneg_left h1LA2 hK.le
      have hBr : B^e * B^r = B^((5:ℝ)/6*((NN d n - 2:ℕ):ℝ)) := by
        rw [← Real.rpow_add hBpos, hedef]
        congr 1
        ring
      have hstep2 : K * (9*(Real.log B)^2) * Real.log B * ((bigW (wOf B):ℕ):ℝ) * c₂ * B^r
          ≤ B^((5:ℝ)/6*((NN d n - 2:ℕ):ℝ)) := by
        calc K * (9*(Real.log B)^2) * Real.log B * ((bigW (wOf B):ℕ):ℝ) * c₂ * B^r
            = 9*c₂*K*(Real.log B)^3*((bigW (wOf B):ℕ):ℝ) * B^r := by ring
          _ ≤ B^e * B^r := mul_le_mul_of_nonneg_right hg2 (Real.rpow_nonneg hBpos.le _)
          _ = B^((5:ℝ)/6*((NN d n - 2:ℕ):ℝ)) := hBr
      have hApow : B^((5:ℝ)/6*((NN d n - 2:ℕ):ℝ)) ≤ A^(NN d n - 2) := by
        have h1 : (B^((5:ℝ)/6))^(NN d n - 2) ≤ A^(NN d n - 2) :=
          pow_le_pow_left₀ (Real.rpow_nonneg hBpos.le _) hA1 _
        rwa [← Real.rpow_natCast (B^((5:ℝ)/6)) (NN d n - 2), ← Real.rpow_mul hBpos.le] at h1
      have hnn2 : 0 ≤ K * (1 + Real.log A)^2 * Real.log B * ((bigW (wOf B):ℕ):ℝ) :=
        mul_nonneg (mul_nonneg (mul_nonneg hK.le (pow_nonneg h1LA_nn 2)) hLpos.le)
          (Nat.cast_nonneg _)
      calc K * (1 + Real.log A)^2 * Real.log B * ((bigW (wOf B):ℕ):ℝ) *
              eNorm (veronese d n x)
          ≤ K * (1 + Real.log A)^2 * Real.log B * ((bigW (wOf B):ℕ):ℝ) * (c₂ * B^r) :=
            mul_le_mul_of_nonneg_left hver_le hnn2
        _ = K * (1 + Real.log A)^2 * Real.log B * ((bigW (wOf B):ℕ):ℝ) * c₂ * B^r := by ring
        _ ≤ B^((5:ℝ)/6*((NN d n - 2:ℕ):ℝ)) := le_trans hstep hstep2
        _ ≤ A^(NN d n - 2) := hApow
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨B₀, fun B hB A hA1 hA2 => hB₀ B hB A hA1 hA2⟩

end Work.HP.MM2
