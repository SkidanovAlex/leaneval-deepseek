import Mathlib
import Submission.Work.BMF.vke_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For every constant `A > 0`, every real exponent `β` and every `γ > 0`, the function
`L ↦ A · (log L)^β` is eventually dominated by `L^γ`. -/
theorem vke_log_pow_le (A β γ : ℝ) (hA : 0 < A) (hγ : 0 < γ) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ L : ℝ, U ≤ L → A * (Real.log L) ^ β ≤ L ^ γ := by
  by_cases hβ : β ≤ 0
  · refine ⟨max (Real.exp 1) (A ^ (1 / γ) + 1), ?_, ?_⟩
    · exact le_trans (Real.one_le_exp zero_le_one) (le_max_left _ _)
    · intro L hL
      have hLexp : Real.exp 1 ≤ L := le_trans (le_max_left _ _) hL
      have hLA : A ^ (1 / γ) + 1 ≤ L := le_trans (le_max_right _ _) hL
      have hlog1 : 1 ≤ Real.log L := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) hLexp
      have hrpow : (Real.log L) ^ β ≤ 1 := by
        have h := Real.rpow_le_rpow_of_exponent_le hlog1 hβ
        rwa [Real.rpow_zero] at h
      have hAle : A ≤ L ^ γ := by
        have hAle0 : A ^ (1 / γ) ≤ L := by linarith
        have h0 : (0 : ℝ) ≤ A ^ (1 / γ) := Real.rpow_nonneg hA.le _
        have h := Real.rpow_le_rpow h0 hAle0 hγ.le
        have hmm : (A ^ (1 / γ)) ^ γ = A := by
          rw [← Real.rpow_mul hA.le (1 / γ) γ, show 1 / γ * γ = 1 by field_simp, Real.rpow_one]
        rwa [hmm] at h
      calc A * (Real.log L) ^ β ≤ A * 1 := mul_le_mul_of_nonneg_left hrpow hA.le
        _ = A := by ring
        _ ≤ L ^ γ := hAle
  · have hβ0 : 0 < β := not_le.mp hβ
    set ε : ℝ := γ / (2 * β) with hεdef
    have hε : 0 < ε := by rw [hεdef]; positivity
    have hεβ : ε * β = γ / 2 := by rw [hεdef]; field_simp
    refine ⟨max 1 ((A / ε ^ β) ^ (2 / γ)), ?_, ?_⟩
    · exact le_max_left _ _
    · intro L hL
      have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
      have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
      have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
      have hlog_le : Real.log L ≤ L ^ ε / ε := Real.log_le_rpow_div hLpos.le hε
      have hstep : (Real.log L) ^ β ≤ (L ^ ε / ε) ^ β := Real.rpow_le_rpow hlog0 hlog_le hβ0.le
      have hdiv : (L ^ ε / ε) ^ β = L ^ (ε * β) / ε ^ β := by
        rw [Real.div_rpow (Real.rpow_nonneg hLpos.le ε) hε.le β, Real.rpow_mul hLpos.le ε β]
      have hbase : (A / ε ^ β) ^ (2 / γ) ≤ L := le_trans (le_max_right _ _) hL
      have h0 : (0 : ℝ) ≤ A / ε ^ β := by positivity
      have hAle : A / ε ^ β ≤ L ^ (γ / 2) := by
        have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (A / ε ^ β) ^ (2 / γ)) hbase
          (by positivity : (0 : ℝ) ≤ γ / 2)
        rw [← Real.rpow_mul h0 (2 / γ) (γ / 2),
          show 2 / γ * (γ / 2) = 1 by field_simp, Real.rpow_one] at h
        exact h
      calc A * (Real.log L) ^ β ≤ A * (L ^ (ε * β) / ε ^ β) := by
            rw [← hdiv]; exact mul_le_mul_of_nonneg_left hstep hA.le
        _ = (A / ε ^ β) * L ^ (ε * β) := by ring
        _ ≤ L ^ (γ / 2) * L ^ (ε * β) :=
            mul_le_mul_of_nonneg_right hAle (Real.rpow_nonneg hLpos.le _)
        _ = L ^ γ := by
            rw [← Real.rpow_add hLpos, show γ / 2 + ε * β = γ by rw [hεβ]; ring]

/-- Basic size comparisons for `Work.BMF.vke_range`, valid as soon as `log N ≥ 64`. -/
theorem vke_basic (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1 / 100000) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ N t : ℝ, 2 ≤ N → N ≤ t →
      Real.log t ≤ c * (Real.log N) ^ (7 / 6 : ℝ) → U ≤ Real.log N →
      (1 ≤ vkLam N t ∧
       vkLam N t ≤ c * (Real.log N) ^ (1 / 6 : ℝ) ∧
       (((vkK N t : ℕ) : ℝ)) ≤ 8 * c * (Real.log N) ^ (1 / 6 : ℝ) ∧
       (((vkK N t : ℕ) : ℝ)) ≤ (Real.log N) ^ (1 / 6 : ℝ) ∧
       6 ≤ vkK N t ∧
       (Nat.factorial (vkK N t - 1) : ℝ) ≤ N ∧
       N ^ vkLam N t = t ∧
       t ≤ N ^ (vkK N t - 3) ∧
       vkLam N t + 2 ≤ Real.log N ∧
       Real.log (((vkK N t : ℕ) : ℝ)) ≤ (1 / 6) * Real.log (Real.log N)) := by
  refine ⟨64, by norm_num, ?_⟩
  intro N t hN hNt hlt hL
  have hNpos : 0 < N := by linarith
  have htpos : 0 < t := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hLleT : Real.log N ≤ Real.log t := Real.log_le_log hNpos hNt
  have hL64 : 64 ≤ Real.log N := le_trans (by norm_num) hL
  have hL1 : 1 ≤ Real.log N := by linarith
  -- `(log N)^{7/6} = (log N)^{1/6} · log N`
  have hpow : (Real.log N) ^ (7 / 6 : ℝ)
      = (Real.log N) ^ (1 / 6 : ℝ) * Real.log N := by
    rw [show (7 / 6 : ℝ) = 1 / 6 + 1 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  -- key: `1 ≤ c · (log N)^{1/6}`
  have hsplit : Real.log N ≤ (c * (Real.log N) ^ (1 / 6 : ℝ)) * Real.log N := by
    have hA : Real.log N ≤ c * (Real.log N) ^ (7 / 6 : ℝ) := le_trans hLleT hlt
    have hB : c * (Real.log N) ^ (7 / 6 : ℝ)
        = (c * (Real.log N) ^ (1 / 6 : ℝ)) * Real.log N := by
      rw [hpow]; ring
    exact hA.trans_eq hB
  have hkey1 : (1 : ℝ) ≤ c * (Real.log N) ^ (1 / 6 : ℝ) := by
    nlinarith [hsplit, hLpos]
  have hc8 : 8 * c ≤ 1 := by linarith
  have hc1le : c ≤ 1 := by linarith
  have hx0 : 0 ≤ (Real.log N) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hLpos.le _
  -- main comparisons
  have hlam_le : vkLam N t ≤ c * (Real.log N) ^ (1 / 6 : ℝ) := by
    rw [vkLam, div_le_iff₀ hLpos]
    have hB : c * (Real.log N) ^ (7 / 6 : ℝ)
        = (c * (Real.log N) ^ (1 / 6 : ℝ)) * Real.log N := by
      rw [hpow]; ring
    rw [← hB]
    exact hlt
  have hlam1 : 1 ≤ vkLam N t := vkLam_ge_one hN hNt
  have hkb := vkK_bounds hN hNt
  have hk6 : 6 ≤ vkK N t := vkK_ge_six hN hNt
  have hk6r : (6 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by exact_mod_cast hk6
  have hk_le8 : (((vkK N t : ℕ) : ℝ)) ≤ 8 * c * (Real.log N) ^ (1 / 6 : ℝ) := by
    have h := hkb.2
    nlinarith [h, hlam_le, hkey1]
  have hk_le' : (((vkK N t : ℕ) : ℝ)) ≤ (Real.log N) ^ (1 / 6 : ℝ) := by
    have h8x : 8 * c * (Real.log N) ^ (1 / 6 : ℝ)
        ≤ 1 * (Real.log N) ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right hc8 hx0
    linarith [hk_le8, h8x]
  have hbig : (2 : ℝ) ≤ (Real.log N) ^ (1 / 6 : ℝ) := by
    nlinarith [hkey1, hc1, hx0]
  -- factorial bound
  have hfact : (Nat.factorial (vkK N t - 1) : ℝ) ≤ N := by
    have hkRpos : 0 < ((vkK N t : ℕ) : ℝ) := by linarith
    have h1 : (Nat.factorial (vkK N t - 1) : ℝ) ≤ (((vkK N t : ℕ) : ℝ)) ^ (vkK N t) := by
      have := le_trans (Nat.factorial_le (Nat.sub_le (vkK N t) 1)) (Nat.factorial_le_pow (vkK N t))
      exact_mod_cast this
    have h2 : (((vkK N t : ℕ) : ℝ)) ^ (vkK N t)
        = Real.exp ((((vkK N t : ℕ) : ℝ)) * Real.log (((vkK N t : ℕ) : ℝ))) := by
      rw [← Real.rpow_natCast (((vkK N t : ℕ) : ℝ)) (vkK N t),
        Real.rpow_def_of_pos hkRpos]
      congr 1; ring
    have hlogk_self : Real.log (((vkK N t : ℕ) : ℝ)) ≤ ((vkK N t : ℕ) : ℝ) :=
      Real.log_le_self (by positivity)
    have hmul : (((vkK N t : ℕ) : ℝ)) * Real.log (((vkK N t : ℕ) : ℝ))
        ≤ (((vkK N t : ℕ) : ℝ)) * (((vkK N t : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogk_self hkRpos.le
    have hprod : (((vkK N t : ℕ) : ℝ)) * (((vkK N t : ℕ) : ℝ))
        ≤ (Real.log N) ^ (1 / 3 : ℝ) := by
      have h1' : (((vkK N t : ℕ) : ℝ)) * (((vkK N t : ℕ) : ℝ))
          ≤ ((Real.log N) ^ (1 / 6 : ℝ)) * ((Real.log N) ^ (1 / 6 : ℝ)) :=
        mul_le_mul hk_le' hk_le' (by positivity) hx0
      have h2' : ((Real.log N) ^ (1 / 6 : ℝ)) * ((Real.log N) ^ (1 / 6 : ℝ))
          = (Real.log N) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hLpos, show (1 / 6 : ℝ) + 1 / 6 = 1 / 3 by norm_num]
      linarith [h1', h2'.le, h2'.ge]
    have h3 : Real.exp ((((vkK N t : ℕ) : ℝ)) * Real.log (((vkK N t : ℕ) : ℝ))) ≤ N := by
      have hL13le : (Real.log N) ^ (1 / 3 : ℝ) ≤ Real.log N := by
        simpa [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 3 : ℝ) ≤ (1 : ℝ))
      have h4 : (((vkK N t : ℕ) : ℝ)) * Real.log (((vkK N t : ℕ) : ℝ)) ≤ Real.log N :=
        le_trans hmul (le_trans hprod hL13le)
      have h5 := Real.exp_le_exp.mpr h4
      rwa [Real.exp_log hNpos] at h5
    linarith [h1, h2.le, h2.ge, h3]
  -- `N^λ = t`
  have hNlam : N ^ vkLam N t = t := by
    rw [Real.rpow_def_of_pos hNpos, vkLam]
    have h : Real.log N * (Real.log t / Real.log N) = Real.log t := by
      field_simp
    rw [h, Real.exp_log htpos]
  -- `t ≤ N^{k-3}`
  have hk3le : 3 ≤ vkK N t := by omega
  have hk3 : vkLam N t ≤ (((vkK N t - 3 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub hk3le]
    push_cast
    linarith [hkb.1, hlam1]
  have ht_le : t ≤ N ^ (vkK N t - 3) := by
    have htmp : N ^ vkLam N t ≤ N ^ (vkK N t - 3) := by
      rw [← Real.rpow_natCast N (vkK N t - 3)]
      exact Real.rpow_le_rpow_of_exponent_le hN1 hk3
    simpa [hNlam] using htmp
  -- `λ + 2 ≤ log N`
  have hL23 : (1 : ℝ) ≤ (Real.log N) ^ (2 / 3 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h56 : (2 : ℝ) ≤ (Real.log N) ^ (5 / 6 : ℝ) := by
    have hsplit5 : (Real.log N) ^ (5 / 6 : ℝ)
        = (Real.log N) ^ (1 / 6 : ℝ) * (Real.log N) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hLpos, show (1 / 6 : ℝ) + 2 / 3 = 5 / 6 by norm_num]
    rw [hsplit5]
    nlinarith [hbig, hL23, hx0]
  have h2L : 2 * (Real.log N) ^ (1 / 6 : ℝ) ≤ Real.log N := by
    have hsplit2 : (Real.log N) ^ (1 / 6 : ℝ) * (Real.log N) ^ (5 / 6 : ℝ) = Real.log N := by
      rw [← Real.rpow_add hLpos, show (1 / 6 : ℝ) + 5 / 6 = 1 by norm_num, Real.rpow_one]
    calc 2 * (Real.log N) ^ (1 / 6 : ℝ)
        ≤ (Real.log N) ^ (5 / 6 : ℝ) * (Real.log N) ^ (1 / 6 : ℝ) :=
          mul_le_mul_of_nonneg_right h56 hx0
      _ = Real.log N := by rw [mul_comm]; exact hsplit2
  have hcle : vkLam N t ≤ (Real.log N) ^ (1 / 6 : ℝ) := by
    calc vkLam N t ≤ c * (Real.log N) ^ (1 / 6 : ℝ) := hlam_le
      _ ≤ 1 * (Real.log N) ^ (1 / 6 : ℝ) := mul_le_mul_of_nonneg_right hc1le hx0
      _ = _ := by ring
  have hlam2 : vkLam N t + 2 ≤ Real.log N := by
    linarith [hcle, hbig, h2L]
  -- `log k ≤ (1/6) log log N`
  have hlogk : Real.log (((vkK N t : ℕ) : ℝ)) ≤ (1 / 6) * Real.log (Real.log N) := by
    have hkRpos : 0 < ((vkK N t : ℕ) : ℝ) := by linarith
    calc Real.log (((vkK N t : ℕ) : ℝ)) ≤ Real.log ((Real.log N) ^ (1 / 6 : ℝ)) :=
          Real.log_le_log hkRpos hk_le'
      _ = (1 / 6) * Real.log (Real.log N) := Real.log_rpow hLpos (1 / 6)
  exact ⟨hlam1, hlam_le, hk_le8, hk_le', hk6, hfact, hNlam, ht_le, hlam2, hlogk⟩

end Work.BMF
