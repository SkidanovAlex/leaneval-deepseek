import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_sum_decay
import Submission.Work.LinnikAreas.Density4.selU_sub_eq_sum_Ico

namespace Work.LinnikAreas.Density4.BzHard

open Finset

noncomputable section

/-- `exp (-y) ≤ 24 / y ^ 4` for `y > 0`, from `exp y ≥ y ^ 4 / 4!`. -/
private lemma exp_neg_le_inv_pow4 {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 24 / y ^ 4 := by
  have h := Real.pow_div_factorial_le_exp y (le_of_lt hy) 4
  have h24 : y ^ 4 / (24 : ℝ) ≤ Real.exp y := by
    have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num
    rw [hf] at h
    exact h
  have hpos : (0 : ℝ) < y ^ 4 / 24 := by positivity
  have hle : 1 / Real.exp y ≤ 1 / (y ^ 4 / 24) := one_div_le_one_div_of_le hpos h24
  have hfe : 1 / (y ^ 4 / 24) = 24 / y ^ 4 := by rw [one_div_div]
  rw [hfe, one_div] at hle
  rw [Real.exp_neg]
  exact hle

/-- The target sum is the sharp log-weighted Möbius sum `selU T` minus the reciprocal
partial sum `muRecipSum T`. -/
private lemma mertens_sum_eq_selU_sub (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Icc 1 T,
        (ArithmeticFunction.moebius t : ℝ) *
          (Real.log (T : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ))
      = Work.LinnikAreas.Density4.selU (T : ℝ)
          - Commons.NumberTheory.Moebius.muRecipSum T := by
  rw [Work.LinnikAreas.Density4.selU_natCast_eq_logWeightedMuSum T hT]
  unfold Commons.NumberTheory.Moebius.logWeightedMuSum Commons.NumberTheory.Moebius.muRecipSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp ht).1
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  field_simp

/-- **The sharp Mertens-type log-weighted Möbius reciprocal sum.**

`Σ_{t ≤ T} μ(t)·(log(T/t) − 1)/t = 1 + O((log T)^{-2})` for `T ≥ 2`.

This is the constant-1 strengthening of
`Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound` (which gives only `O(1)`), and the
Mertens-type input to Graham's hard case for the Selberg weights.

Route.  `Σ_{t≤T} μ(t)(log T − log t − 1)/t = log T·M₁(T) − M₂(T) − M₁(T)` where
`M₁(T) = Σ_{t≤T} μ(t)/t = O(exp(-c√log T))` (`Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay`)
and `M₂(T) = Σ_{t≤T} μ(t)log t/t`.  The value `1` comes from `M₂(T) → −1`, i.e. from
`Σ_{t≥1} μ(t)log t·t^{−s} = −ζ'(s)/ζ(s)² → −1` as `s → 1⁺`: a clean way to conclude is
`Σ_{t≤T} μ(t)(log T − log t)/t = ∫₁^T M₁(u) du/u` (Abel), whose limit as `T → ∞` equals
`lim_{δ→0⁺} δ^{−1}·Σ_{t≥1}μ(t)t^{−1−δ} = lim_{δ→0⁺} δ^{−1}/ζ(1+δ) = 1`
(dominated convergence using the Mertens bound, then `ζ(s)(s−1) → 1`).  A rate like
`O(exp(-c√log T))` is provable from the same sources, hence certainly `O((log T)^{-2})`.
Mathlib has the Dirichlet series of `μ` and the residue of `ζ` at `1`. -/
theorem mertens_log_weighted_one : ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T →
    |(∑ t ∈ Finset.Icc 1 T,
        (ArithmeticFunction.moebius t : ℝ) * (Real.log (T : ℝ) - Real.log (t : ℝ) - 1) / (t : ℝ)) - 1|
      ≤ C / (Real.log (T : ℝ)) ^ 2 := by
  -- Sharp log-weighted Möbius sum: `Σ_{t ≤ T} μ t (log T − log t)/t = 1 + O(e^{-c√log T})`.
  obtain ⟨L, C₁, c₁, hc₁, hC₁, hrate₁⟩ := Work.LinnikAreas.Density4.selU_limit_rate
  have hL : L = 1 :=
    Work.LinnikAreas.Density4.selU_limit_eq_one L C₁ c₁ hc₁ hC₁ hrate₁
  -- Reciprocal partial sum: `Σ_{t ≤ T} μ t / t = O(e^{-c√log T})`.
  obtain ⟨K, c₂, hc₂, hK, hrate₂⟩ := Work.LinnikAreas.Density4.muRecipSum_exp_decay
  have htotal_pos : 0 < C₁ + K := by linarith
  refine ⟨(C₁ + K) * 24 / (min c₁ c₂) ^ 4, by positivity, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by omega
  have hlogpos : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
  have hsqrtpos : 0 < Real.sqrt (Real.log (T : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hc₁' : min c₁ c₂ ≤ c₁ := min_le_left _ _
  have hc₂' : min c₁ c₂ ≤ c₂ := min_le_right _ _
  have hminpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  -- the two error terms, both with rate `min c₁ c₂`
  have hselU : |Work.LinnikAreas.Density4.selU (T : ℝ) - 1|
      ≤ C₁ * Real.exp (-(min c₁ c₂ * Real.sqrt (Real.log (T : ℝ)))) := by
    have h := hrate₁ (T : ℝ) (by exact_mod_cast hT1)
    rw [hL] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₁.le)
    nlinarith [hc₁', hsqrtpos]
  have hmu : |Commons.NumberTheory.Moebius.muRecipSum T|
      ≤ K * Real.exp (-(min c₁ c₂ * Real.sqrt (Real.log (T : ℝ)))) := by
    refine (hrate₂ T hT1).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le)
    nlinarith [hc₂', hsqrtpos]
  rw [mertens_sum_eq_selU_sub T hT1]
  -- combine
  have hsplit : |Work.LinnikAreas.Density4.selU (T : ℝ)
        - Commons.NumberTheory.Moebius.muRecipSum T - 1|
      ≤ (C₁ + K) * Real.exp (-(min c₁ c₂ * Real.sqrt (Real.log (T : ℝ)))) := by
    have h1 : Work.LinnikAreas.Density4.selU (T : ℝ)
        - Commons.NumberTheory.Moebius.muRecipSum T - 1
        = (Work.LinnikAreas.Density4.selU (T : ℝ) - 1)
            - Commons.NumberTheory.Moebius.muRecipSum T := by ring
    rw [h1]
    calc |(Work.LinnikAreas.Density4.selU (T : ℝ) - 1)
            - Commons.NumberTheory.Moebius.muRecipSum T|
        ≤ |Work.LinnikAreas.Density4.selU (T : ℝ) - 1|
            + |Commons.NumberTheory.Moebius.muRecipSum T| := abs_sub _ _
      _ ≤ C₁ * Real.exp (-(min c₁ c₂ * Real.sqrt (Real.log (T : ℝ))))
            + K * Real.exp (-(min c₁ c₂ * Real.sqrt (Real.log (T : ℝ)))) := add_le_add hselU hmu
      _ = (C₁ + K) * Real.exp (-(min c₁ c₂ * Real.sqrt (Real.log (T : ℝ)))) := by ring
  -- `e^{-y} ≤ 24/y⁴` with `y = min c₁ c₂ · √log T`
  have hy : 0 < min c₁ c₂ * Real.sqrt (Real.log (T : ℝ)) := mul_pos hminpos hsqrtpos
  have hpow : (min c₁ c₂ * Real.sqrt (Real.log (T : ℝ))) ^ 4
      = (min c₁ c₂) ^ 4 * (Real.log (T : ℝ)) ^ 2 := by
    rw [mul_pow, show (Real.sqrt (Real.log (T : ℝ))) ^ 4
        = (Real.log (T : ℝ)) ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hlogpos.le]]
  calc |Work.LinnikAreas.Density4.selU (T : ℝ)
        - Commons.NumberTheory.Moebius.muRecipSum T - 1|
      ≤ (C₁ + K) * Real.exp (-(min c₁ c₂ * Real.sqrt (Real.log (T : ℝ)))) := hsplit
    _ ≤ (C₁ + K) * (24 / (min c₁ c₂ * Real.sqrt (Real.log (T : ℝ))) ^ 4) :=
        mul_le_mul_of_nonneg_left (exp_neg_le_inv_pow4 hy) htotal_pos.le
    _ = (C₁ + K) * 24 / (min c₁ c₂) ^ 4 / (Real.log (T : ℝ)) ^ 2 := by
        rw [hpow]; field_simp

end

end Work.LinnikAreas.Density4.BzHard
