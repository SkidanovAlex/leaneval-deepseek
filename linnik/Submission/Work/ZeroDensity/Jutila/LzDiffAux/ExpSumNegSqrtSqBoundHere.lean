import Mathlib
import Submission.Work.ZeroDensity.Jutila.uniAQBound

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

/-- The maximum of `u^4 e^{-u}` on `u > 0` is `(4/e)^4`; equivalently `log v ≤ v - 1`
for `v = u/4`. -/
lemma pow_four_mul_exp_neg_le {u : ℝ} (hu : 0 < u) :
    u ^ 4 * Real.exp (-u) ≤ (4 / Real.exp 1) ^ 4 := by
  refine (Real.log_le_log_iff (by positivity) (by positivity)).mp ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp,
    Real.log_pow, Real.log_div (by norm_num) (Real.exp_ne_zero 1), Real.log_exp]
  have hv : 0 < u / 4 := by positivity
  have hlog : Real.log (u / 4) ≤ u / 4 - 1 := Real.log_le_sub_one_of_pos hv
  have hlogu : Real.log u = Real.log 4 + Real.log (u / 4) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt hv)]
    congr 1
    field_simp
  have h4 : 4 * Real.log (u / 4) ≤ 4 * (u / 4 - 1) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  rw [hlogu]
  linarith [h4]

/-- For `a > 0` and `m ≥ 1`: `exp (-(a√m)) ≤ (4/e)^4 / (a^4 m^2)`. -/
lemma exp_neg_sqrt_le {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-(a * Real.sqrt (m : ℝ))) ≤ (4 / Real.exp 1) ^ 4 / (a ^ 4 * (m : ℝ) ^ 2) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hspos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have hu : 0 < a * Real.sqrt (m : ℝ) := mul_pos ha hspos
  have hkey := pow_four_mul_exp_neg_le hu
  have hs4 : (Real.sqrt (m : ℝ)) ^ 4 = (m : ℝ) ^ 2 := by
    rw [show (Real.sqrt (m:ℝ)) ^ 4 = ((Real.sqrt (m:ℝ)) ^ 2) ^ 2 by ring, Real.sq_sqrt hm0.le]
  have hu4 : (a * Real.sqrt (m : ℝ)) ^ 4 = a ^ 4 * (m : ℝ) ^ 2 := by rw [mul_pow, hs4]
  rw [hu4] at hkey
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hkey]

/-- `Σ_{b ∈ Icc K L} 1/b² ≤ 2/K` for `K ≥ 1`. -/
lemma sum_Icc_inv_sq_le (K L : ℕ) (hK : 1 ≤ K) :
    (∑ b ∈ Finset.Icc K L, 1 / (b : ℝ) ^ 2) ≤ 2 / (K : ℝ) := by
  rcases eq_or_lt_of_le hK with h | h
  · subst h
    calc (∑ b ∈ Finset.Icc 1 L, 1 / (b : ℝ) ^ 2) ≤ 2 := uniAQInvSqSum L
      _ = 2 / ((1 : ℕ) : ℝ) := by norm_num
  · have hK2 : 2 ≤ K := h
    by_cases hKL : K ≤ L
    · have hterm : ∀ b ∈ Finset.Icc K L, 1 / (b : ℝ) ^ 2 ≤ 1 / ((b : ℝ) * ((b : ℝ) - 1)) := by
        intro b hb
        have hb2 : 2 ≤ b := le_trans hK2 (Finset.mem_Icc.mp hb).1
        have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
        have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
          have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
          linarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have htel : (∑ b ∈ Finset.Icc K L, 1 / ((b : ℝ) * ((b : ℝ) - 1)))
          = 1 / ((K : ℝ) - 1) - 1 / (L : ℝ) := by
        have hsub := Finset.sum_Icc_sub (m := K) (n := L) hKL
          (f := fun i : ℕ => -(1 / ((i : ℝ) - 1)))
        have hcongr : (∑ b ∈ Finset.Icc K L, 1 / ((b : ℝ) * ((b : ℝ) - 1)))
            = ∑ b ∈ Finset.Icc K L,
                (-(1 / ((((b + 1 : ℕ)) : ℝ) - 1)) - -(1 / ((b : ℝ) - 1))) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hb2 : 2 ≤ b := le_trans hK2 (Finset.mem_Icc.mp hb).1
          have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
          have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
            have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
            linarith
          have hcast : (((b + 1 : ℕ)) : ℝ) - 1 = (b : ℝ) := by push_cast; ring
          rw [hcast]
          field_simp
          ring
        rw [hcongr, hsub]
        have hcastL : (((L + 1 : ℕ)) : ℝ) - 1 = (L : ℝ) := by push_cast; ring
        rw [hcastL]
        ring
      calc (∑ b ∈ Finset.Icc K L, 1 / (b : ℝ) ^ 2)
          ≤ ∑ b ∈ Finset.Icc K L, 1 / ((b : ℝ) * ((b : ℝ) - 1)) := Finset.sum_le_sum hterm
        _ = 1 / ((K : ℝ) - 1) - 1 / (L : ℝ) := htel
        _ ≤ 1 / ((K : ℝ) - 1) := by
            have : (0 : ℝ) ≤ 1 / (L : ℝ) := by positivity
            linarith
        _ ≤ 2 / (K : ℝ) := by
            have hK1' : (0 : ℝ) < (K : ℝ) - 1 := by
              have : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK2
              linarith
            have hK0' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
            rw [div_le_div_iff₀ hK1' hK0']
            have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
            linarith
    · have hemp : Finset.Icc K L = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega)
      rw [hemp, Finset.sum_empty]
      positivity
/-- **`Σ_{k ≤ J} exp (-(a √k)) ≤ 10 + 10/a²`**, uniformly in `a > 0` and `J`.  Split the sum at
`K = ⌊3/a²⌋ + 2`: the head has at most `K` terms of modulus at most `1`, and in the tail the sharp
pointwise bound `a⁴k² e^{-a√k} ≤ (4/e)⁴ ≤ 10` applies, with `Σ 1/k² ≤ 2/K`. -/
theorem ExpSumNegSqrtSqBound {a : ℝ} (ha : 0 < a) (J : ℕ) :
    (∑ k ∈ Finset.range (J + 1), Real.exp (-(a * Real.sqrt (k : ℝ)))) ≤ 10 + 10 / a ^ 2 := by
  have hgoal : 10 + 10 / a ^ 2 = 10 + 10 * (1 / a ^ 2) := by ring
  rw [hgoal]
  have ha2 : (0:ℝ) < a^2 := by positivity
  set K : ℕ := ⌊3 / a ^ 2⌋₊ + 2 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKge : 3 / a^2 ≤ (K:ℝ) := by
    have h1 : 3 / a^2 < (⌊3 / a^2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hKdef]; push_cast; linarith
  have hKle : (K:ℝ) ≤ 3 * (1/a^2) + 2 := by
    have h1 : (⌊3 / a^2⌋₊ : ℝ) ≤ 3 / a^2 := Nat.floor_le (by positivity)
    have h2 : (3:ℝ) / a^2 = 3 * (1/a^2) := by ring
    have h3 : (K:ℝ) = (⌊3 / a^2⌋₊ : ℝ) + 2 := by rw [hKdef]; push_cast; ring
    rw [h3]; linarith
  have hu : (0:ℝ) ≤ 1 / a^2 := by positivity
  have hsplit : Finset.range (J + 1) = Finset.range (min (J + 1) K) ∪ Finset.Icc K J := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.range (min (J + 1) K)) (Finset.Icc K J) := by
    rw [Finset.disjoint_left]; intro k hk hk'
    simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc] at hk'; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hhead : (∑ k ∈ Finset.range (min (J + 1) K),
        Real.exp (-(a * Real.sqrt (k : ℝ)))) ≤ (K : ℝ) := by
    have h2 : ∀ k ∈ Finset.range (min (J + 1) K),
        Real.exp (-(a * Real.sqrt (k : ℝ))) ≤ (1:ℝ) := by
      intro k _
      refine Real.exp_le_one_iff.mpr ?_
      exact neg_nonpos.mpr (mul_nonneg ha.le (Real.sqrt_nonneg _))
    calc (∑ k ∈ Finset.range (min (J + 1) K), Real.exp (-(a * Real.sqrt (k : ℝ))))
        ≤ ∑ _k ∈ Finset.range (min (J + 1) K), (1:ℝ) := Finset.sum_le_sum h2
      _ = ((min (J + 1) K : ℕ) : ℝ) := by simp
      _ ≤ (K : ℝ) := by exact_mod_cast min_le_right _ _
  have htail : (∑ k ∈ Finset.Icc K J, Real.exp (-(a * Real.sqrt (k : ℝ))))
      ≤ 10 / a ^ 4 * (2 / (K : ℝ)) := by
    have hC : (4 / Real.exp 1) ^ 4 ≤ 10 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have he : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h3 : (2.7:ℝ)^4 ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) (le_of_lt he) 4
      nlinarith [h3]
    have hstep : (∑ k ∈ Finset.Icc K J, Real.exp (-(a * Real.sqrt (k : ℝ))))
        ≤ ∑ k ∈ Finset.Icc K J, (4 / Real.exp 1) ^ 4 / (a ^ 4 * (k : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact exp_neg_sqrt_le ha (by have := (Finset.mem_Icc.mp hk).1; omega)
    have hfac : (∑ k ∈ Finset.Icc K J, (4 / Real.exp 1) ^ 4 / (a ^ 4 * (k : ℝ) ^ 2))
        = ((4 / Real.exp 1) ^ 4 / a ^ 4) * ∑ k ∈ Finset.Icc K J, (1:ℝ) / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp
    rw [hfac] at hstep
    refine le_trans hstep ?_
    have hkey := sum_Icc_inv_sq_le K J hK1
    have ha4 : (0:ℝ) < a ^ 4 := by positivity
    have e1 : (4 / Real.exp 1) ^ 4 / a ^ 4 ≤ 10 / a^4 :=
      div_le_div_of_nonneg_right hC ha4.le
    exact mul_le_mul e1 hkey (by positivity) (by positivity)
  have htail2 : (∑ k ∈ Finset.Icc K J, Real.exp (-(a * Real.sqrt (k : ℝ))))
      ≤ (20/3) * (1 / a^2) := by
    refine le_trans htail ?_
    have hKinv : (2:ℝ) / (K:ℝ) ≤ 2 / (3 / a^2) := by
      have h2 : (0:ℝ) < 3 / a^2 := by positivity
      rw [div_le_div_iff₀ hKpos h2]
      nlinarith [hKge, ha2]
    have h1 : 10 / a ^ 4 * (2 / (K : ℝ)) ≤ 10 / a^4 * (2 / (3/a^2)) :=
      mul_le_mul_of_nonneg_left hKinv (by positivity)
    refine le_trans h1 ?_
    have h2 : (10:ℝ) / a^4 * (2 / (3/a^2)) = (20/3) * (1/a^2) := by
      field_simp
      ring
    rw [h2]
  linarith [hhead, htail2, hKle, hu]

end Work.ZeroDensity.Jutila.LzDiffAux
