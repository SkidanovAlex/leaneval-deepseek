import Mathlib
import Submission.Work.BMF.vke_defs
import Submission.Work.BMF.vke_range_aux
import Submission.Work.BMF.vke_H_pos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- `(a·b/c)^{-r} = a^{-r}·b^{-r}·c^{r}` for `a,b ≥ 0`, `c > 0`. -/
lemma vke_rpow_mul_div_neg (a b c r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    (a * b / c) ^ (-r) = a ^ (-r) * b ^ (-r) * c ^ r := by
  rw [Real.div_rpow (mul_nonneg ha hb) hc.le (-r), Real.mul_rpow ha hb,
      Real.rpow_neg hc.le r, div_inv_eq_mul]

/-- `(a/c)^{-r} = a^{-r}·c^{r}` for `a ≥ 0`, `c > 0`. -/
lemma vke_rpow_div_neg (a c r : ℝ) (ha : 0 ≤ a) (hc : 0 < c) :
    (a / c) ^ (-r) = a ^ (-r) * c ^ r := by
  rw [Real.div_rpow ha hc.le (-r), Real.rpow_neg hc.le r, div_inv_eq_mul]

/-- For `0 < a ≤ 1` and `0 < n`, `a^{-1/n} ≥ 1`. -/
lemma vke_one_le_rpow_neg_inv (a : ℝ) (n : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) (hn : 0 < n) :
    1 ≤ a ^ (-(1 / (n : ℝ))) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : 0 < 1 / (n:ℝ) := by positivity
  rw [Real.rpow_neg ha.le, one_le_inv₀ (Real.rpow_pos_of_pos ha _)]
  calc a ^ (1 / (n:ℝ)) ≤ 1 ^ (1 / (n:ℝ)) := Real.rpow_le_rpow ha.le ha1 h1.le
    _ = 1 := by simp

/-- For `log N ≥ 64`, `N^{-3/2} ≤ 1/4`, `N^{-3/2}(N+1) ≤ 1` and `N^{-3/2} ≤ 1`. -/
lemma vke_rpow_neg_bounds {N : ℝ} (hN : 2 ≤ N) (hL : 64 ≤ Real.log N) :
    N ^ (-(3 / 2 : ℝ)) ≤ 1 / 4 ∧ N ^ (-(3 / 2 : ℝ)) * (N + 1) ≤ 1 ∧
      N ^ (-(3 / 2 : ℝ)) ≤ 1 := by
  have hNpos : 0 < N := by linarith
  have h4exp : (4:ℝ) ≤ Real.exp 96 := by
    have hlog4 : Real.log 4 ≤ 96 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
    have h := Real.exp_le_exp.mpr hlog4
    rwa [Real.exp_log (show (0:ℝ) < 4 by norm_num)] at h
  have h2exp : (2:ℝ) ≤ Real.exp 32 := by
    have hlog2 : Real.log 2 ≤ 32 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have h := Real.exp_le_exp.mpr hlog2
    rwa [Real.exp_log (show (0:ℝ) < 2 by norm_num)] at h
  have hN32 : (4:ℝ) ≤ N ^ (3/2:ℝ) := by
    rw [Real.rpow_def_of_pos hNpos]
    have h : Real.exp 96 ≤ Real.exp (Real.log N * (3/2)) :=
      Real.exp_le_exp.mpr (by nlinarith [hL])
    linarith
  have hN12 : (2:ℝ) ≤ N ^ (1/2:ℝ) := by
    rw [Real.rpow_def_of_pos hNpos]
    have h : Real.exp 32 ≤ Real.exp (Real.log N * (1/2)) :=
      Real.exp_le_exp.mpr (by nlinarith [hL])
    linarith
  have hA : N ^ (-(3/2:ℝ)) ≤ 1/4 := by
    rw [Real.rpow_neg hNpos.le, show (1:ℝ)/4 = (4:ℝ)⁻¹ by norm_num]
    rw [inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) (by norm_num : (0:ℝ) < 4)]
    exact hN32
  have hinv : N ^ (-(1/2:ℝ)) ≤ (2:ℝ)⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    rw [inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) (by norm_num : (0:ℝ)<2)]
    exact hN12
  have hfin : 2 * N ^ (-(1/2:ℝ)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ) ≤ 2)
    rwa [show (2:ℝ) * 2⁻¹ = 1 by norm_num] at this
  have hB : N ^ (-(3/2:ℝ)) * (N + 1) ≤ 1 := by
    have hle : N + 1 ≤ 2 * N := by linarith
    have h1 : N ^ (-(3/2:ℝ)) * (N + 1) ≤ N ^ (-(3/2:ℝ)) * (2*N) :=
      mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hNpos.le _)
    have h2 : N ^ (-(3/2:ℝ)) * (2*N) = 2 * N ^ (-(1/2:ℝ)) := by
      have hmm : N ^ (-(3/2:ℝ)) * N = N ^ (-(1/2:ℝ)) := by
        have h := Real.rpow_add hNpos (-(3/2:ℝ)) 1
        rw [Real.rpow_one] at h
        have e : -(3/2:ℝ) + 1 = -(1/2) := by norm_num
        rw [e] at h
        exact h.symm
      calc N ^ (-(3/2:ℝ)) * (2*N) = 2 * (N ^ (-(3/2:ℝ)) * N) := by ring
        _ = 2 * N ^ (-(1/2:ℝ)) := by rw [hmm]
    rw [h2] at h1
    linarith [h1, hfin]
  exact ⟨hA, hB, le_trans hA (by norm_num)⟩

/-- `μ = vkMu N t ≤ N^{-3/2}` in the range of `vke_basic`. -/
lemma vke_mu_le_rpow (N t : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t)
    (hfac : (Nat.factorial (vkK N t - 1) : ℝ) ≤ N)
    (htt : t ≤ N ^ (vkK N t - 3))
    (hk6 : 6 ≤ vkK N t)
    (hk_le : ((vkK N t : ℕ) : ℝ) ≤ (Real.log N) ^ (1 / 6 : ℝ))
    (hL : 64 ≤ Real.log N) :
    vkMu N t ≤ N ^ (-(3 / 2 : ℝ)) := by
  rw [vkMu]
  set k : ℕ := vkK N t with hk
  have hNpos : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have htpos : 0 < t := by linarith
  have hLpos : 0 < Real.log N := by linarith
  have hApos : (0:ℝ) ≤ ((Nat.factorial (k - 1) : ℕ) : ℝ) := by positivity
  have hdenpos : (0:ℝ) < (N-1)^k := by positivity
  have h2pi1 : (1:ℝ)/(2*Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_d2]
  have hmu1 : (t / (2 * Real.pi)) * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k
      ≤ t * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k := by
    have hX : 0 ≤ t * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k :=
      div_nonneg (mul_nonneg htpos.le hApos) (le_of_lt hdenpos)
    calc (t / (2 * Real.pi)) * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k
        = (1/(2*Real.pi)) * (t * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k) := by
          field_simp
      _ ≤ 1 * (t * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k) :=
          mul_le_mul_of_nonneg_right h2pi1 hX
      _ = t * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k := by ring
  have hnum : t * ((Nat.factorial (k - 1) : ℕ) : ℝ) ≤ N ^ (k - 3) * N :=
    mul_le_mul htt hfac hApos (by positivity)
  have hNpow : N ^ (k - 3) * N = N ^ (k - 2) := by
    rw [← pow_succ]; congr 1; omega
  have hmu2 : t * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1) ^ k
      ≤ N ^ (k - 2) / (N - 1) ^ k := by
    rw [hNpow] at hnum
    exact div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
  have hNd : N ^ k = N ^ (k - 2) * N ^ 2 := by
    have h1 : (k - 2) + 2 = k := by omega
    nth_rewrite 1 [← h1]
    rw [pow_add]
  have hdivN : N ^ (k - 2) = N ^ k / N ^ 2 := by
    rw [eq_div_iff (ne_of_gt (by positivity : (0:ℝ) < N^2))]
    exact hNd.symm
  have hrat : N ^ (k - 2) / (N - 1) ^ k = (N / (N - 1)) ^ k / N ^ 2 := by
    rw [hdivN, div_div, div_pow, div_div]
    ring
  have hbase : N / (N - 1) ≤ 2 := by
    rw [div_le_iff₀ hN1]; linarith
  have hmu3 : N ^ (k - 2) / (N - 1) ^ k ≤ 2 ^ k / N ^ 2 := by
    rw [hrat]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)
  have hklog : ((k:ℕ):ℝ) * Real.log 2 ≤ (1/2) * Real.log N := by
    have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hle1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num); linarith
    have hL1 : (1:ℝ) ≤ Real.log N := by linarith
    have hLs : (Real.log N) ^ (1/2:ℝ) ≤ Real.log N / 2 := by
      rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hLpos.le _)
        (by linarith : (0:ℝ) ≤ Real.log N/2) (by norm_num : (0:ℝ) < 2)]
      rw [← Real.rpow_mul hLpos.le (1/2:ℝ) 2, show (1/2:ℝ) * 2 = 1 by norm_num,
          Real.rpow_one, Real.rpow_two, div_pow]
      nlinarith [hL]
    have hL16 : (Real.log N) ^ (1/6:ℝ) ≤ (1/2) * Real.log N :=
      calc (Real.log N) ^ (1/6:ℝ) ≤ (Real.log N) ^ (1/2:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1/6:ℝ) ≤ 1/2)
        _ ≤ Real.log N / 2 := hLs
        _ = (1/2) * Real.log N := by ring
    calc ((k:ℕ):ℝ) * Real.log 2 ≤ (Real.log N)^(1/6:ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hk_le hlog2nn
      _ ≤ (Real.log N)^(1/6:ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg hLpos.le _)
      _ = (Real.log N)^(1/6:ℝ) := by ring
      _ ≤ (1/2)*Real.log N := hL16
  have h2k : (2:ℝ) ^ k ≤ N ^ (1/2:ℝ) := by
    rw [← Real.rpow_natCast (2:ℝ) k]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.mpr
    linarith [hklog]
  have hfinal : N ^ (1/2:ℝ) / N^2 = N ^ (-(3/2:ℝ)) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_sub hNpos]
    norm_num
  calc (t / (2*Real.pi)) * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1)^k
      ≤ t * ((Nat.factorial (k - 1) : ℕ) : ℝ) / (N - 1)^k := hmu1
    _ ≤ N ^ (k-2) / (N-1)^k := hmu2
    _ ≤ 2 ^ k / N^2 := hmu3
    _ ≤ N ^ (1/2:ℝ) / N^2 := div_le_div_of_nonneg_right h2k (by positivity)
    _ = N ^ (-(3/2:ℝ)) := hfinal

/-- `vkH N t ≤ 7 N^{1-λ/k}` for `2 ≤ N ≤ t` and `N^λ = t`. -/
lemma vke_H_le_rpow (N t : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t) (hNlam : N ^ vkLam N t = t) :
    vkH N t ≤ 7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) := by
  have hNpos : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have htpos : 0 < t := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  have hApos : 0 < (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) := by
    have := Nat.factorial_pos (vkK N t - 1); positivity
  have hA1 : 1 ≤ (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) := by
    have h : 1 ≤ Nat.factorial (vkK N t - 1) := by
      have := Nat.factorial_pos (vkK N t - 1); omega
    exact_mod_cast h
  have hkpos : 0 < (((vkK N t : ℕ):ℝ)) := by
    have h : 0 < vkK N t := by simp only [vkK]; omega
    exact_mod_cast h
  have hk1 : (1:ℝ) ≤ (((vkK N t : ℕ):ℝ)) := by
    have h : 1 ≤ vkK N t := by simp only [vkK]; omega
    exact_mod_cast h
  have hz : (((N-1) ^ (vkK N t)) : ℝ) ^ (1/(((vkK N t : ℕ):ℝ))) = N - 1 := by
    rw [← Real.rpow_natCast (N-1) (vkK N t)]
    rw [← Real.rpow_mul hN1.le]
    rw [mul_one_div_cancel (ne_of_gt hkpos), Real.rpow_one]
  have hH : vkH N t = t ^ (-(1/(((vkK N t : ℕ):ℝ))))
      * (2*Real.pi) ^ (1/(((vkK N t : ℕ):ℝ)))
      * (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (N-1) := by
    rw [vkH, vkMu]
    rw [vke_rpow_mul_div_neg (t/(2*Real.pi)) (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ))
        ((N-1)^(vkK N t)) (1/(((vkK N t : ℕ):ℝ))) (by positivity) hApos.le (by positivity)]
    rw [hz]
    rw [vke_rpow_div_neg t (2*Real.pi) (1/(((vkK N t : ℕ):ℝ))) htpos.le hpi]
  have hbase : (1:ℝ) ≤ 2*Real.pi := by nlinarith [Real.pi_gt_d2]
  have h1kk : (1:ℝ)/(((vkK N t : ℕ):ℝ)) ≤ 1 := by
    rw [div_le_one hkpos]; exact hk1
  have h2pi : (2*Real.pi) ^ (1/(((vkK N t : ℕ):ℝ))) ≤ 2*Real.pi := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase h1kk
    rwa [Real.rpow_one] at h
  have hAinv : (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) ≤ 1 := by
    rw [Real.rpow_neg hApos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hA1 (by positivity))
  have ht' : t ^ (-(1/(((vkK N t : ℕ):ℝ)))) = N ^ (-(vkLam N t / ((vkK N t : ℕ):ℝ))) := by
    nth_rewrite 1 [← hNlam]
    rw [← Real.rpow_mul hNpos.le (vkLam N t) (-(1/(((vkK N t : ℕ):ℝ))))]
    congr 1
    ring
  have hNm : N ^ (1 - vkLam N t / ((vkK N t : ℕ):ℝ))
      = N * N ^ (-(vkLam N t / ((vkK N t : ℕ):ℝ))) := by
    have h := Real.rpow_add hNpos 1 (-(vkLam N t / ((vkK N t : ℕ):ℝ)))
    rw [Real.rpow_one, show (1:ℝ) + -(vkLam N t / ((vkK N t : ℕ):ℝ))
        = 1 - vkLam N t / ((vkK N t : ℕ):ℝ) by ring] at h
    exact h
  have hbb : (2*Real.pi) ^ (1/(((vkK N t : ℕ):ℝ)))
        * (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (N-1)
      ≤ (2*Real.pi) * 1 * N := by
    have h23 : (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (N-1)
        ≤ 1 * N :=
      mul_le_mul hAinv (by linarith : N-1 ≤ N) (by linarith : (0:ℝ) ≤ N-1) (by norm_num)
    calc (2*Real.pi) ^ (1/(((vkK N t : ℕ):ℝ)))
          * (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (N-1)
        = (2*Real.pi) ^ (1/(((vkK N t : ℕ):ℝ)))
          * ((((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (N-1)) := by ring
      _ ≤ (2*Real.pi) * (1 * N) := mul_le_mul h2pi h23 (by positivity) (by positivity)
      _ = (2*Real.pi) * 1 * N := by ring
  calc vkH N t
      = t ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (2*Real.pi) ^ (1/(((vkK N t : ℕ):ℝ)))
        * (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (N-1) := hH
    _ = t ^ (-(1/(((vkK N t : ℕ):ℝ)))) *
          ((2*Real.pi) ^ (1/(((vkK N t : ℕ):ℝ)))
            * (((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)) ^ (-(1/(((vkK N t : ℕ):ℝ)))) * (N-1)) := by ring
    _ ≤ t ^ (-(1/(((vkK N t : ℕ):ℝ)))) * ((2*Real.pi) * 1 * N) :=
        mul_le_mul_of_nonneg_left hbb (Real.rpow_nonneg htpos.le _)
    _ = 2*Real.pi * N ^ (1 - vkLam N t / ((vkK N t : ℕ):ℝ)) := by rw [ht', hNm]; ring
    _ ≤ 7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_lt_d2]) (Real.rpow_nonneg hNpos.le _)

/-- **The Weyl-shift and derivative-size bounds.**  For `log N` large (depending only on nothing),
`μ = vkMu N t` and `H = vkH N t = μ^{−1/k}` satisfy `μ ≤ 1/4`, `μ(N+1) ≤ 1`, `1 ≤ H` and
`H ≤ 7 N^{1−λ/k}`.  Route: `Work.BMF.vke_basic` (in `vke_range_aux`) gives, for `log N ≥ 64`,
`k = vkK N t ≤ (log N)^{1/6}`, `(k−1)! ≤ N`, `N^λ = t` and `t ≤ N^{k−3}`; hence
`μ ≤ 2^k N^{k−2}/(N−1)^k ≤ 2^{k+1}/N²` and `H = (N−1)·(2π/(t(k−1)!))^{1/k} ≤ (2π)^{1/k} N^{1−λ/k}`. -/
theorem vke_Hmu_range :
    ∃ U : ℝ, 0 < U ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t →
      Real.log t ≤ (1 / 100000) * Real.log N ^ (7 / 6 : ℝ) → U ≤ Real.log N →
      vkMu N t ≤ 1 / 4 ∧ vkMu N t * (N + 1) ≤ 1 ∧ 1 ≤ vkH N t ∧
        vkH N t ≤ 7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) := by
  obtain ⟨Ub, hUb1, hbasic⟩ := vke_basic (1/100000) (by norm_num) (by norm_num)
  refine ⟨max Ub 64, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 64) (le_max_right Ub 64)
  · intro N t hN hNt hlt hU
    have hL64 : (64:ℝ) ≤ Real.log N := le_trans (le_max_right Ub 64) hU
    have hLUb : Ub ≤ Real.log N := le_trans (le_max_left Ub 64) hU
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ :=
      hbasic N t hN hNt hlt hLUb
    have hmu := vke_mu_le_rpow N t hN hNt hb6 hb8 hb5 hb4 hL64
    have hbnds := vke_rpow_neg_bounds hN hL64
    have hmu14 : vkMu N t ≤ 1 / 4 := le_trans hmu hbnds.1
    have hmuN : vkMu N t * (N + 1) ≤ 1 := by
      have h1 : vkMu N t * (N + 1) ≤ N ^ (-(3/2:ℝ)) * (N + 1) :=
        mul_le_mul_of_nonneg_right hmu (by linarith)
      linarith [h1, hbnds.2.1]
    have hHge : 1 ≤ vkH N t := by
      have hmu0 : 0 < vkMu N t := vkMu_pos N t hN hNt
      have hmu1 : vkMu N t ≤ 1 := le_trans hmu14 (by norm_num)
      have h := vke_one_le_rpow_neg_inv (vkMu N t) (vkK N t) hmu0 hmu1 (by omega)
      simpa [vkH] using h
    exact ⟨hmu14, hmuN, hHge, vke_H_le_rpow N t hN hNt hb7⟩

end Work.BMF
