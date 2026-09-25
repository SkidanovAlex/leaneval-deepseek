import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.psi_sub_le_of_RH

/-!
# `Work.RHContract.A.R3.caC_ge`

The lower bound for the margin coefficient
`c(ε) = (1 − 3/√ξ) / (ψ(ξ) · log ψ(ξ))` (`Work.RHContract.Margin.caC`) used in Region III
(`ξ = ξ(ε) ≥ 10^8`) of the colossally abundant analysis: for `ξ ≥ 10^8`,

`(1 − ξ^{−1/4}/2 − 6 ξ^{−1/2}) / (ξ log ξ) ≤ c(ε)`.

The proof is a single real-variable estimate.  Writing `u = ξ^{−1/4} ≤ 1/100`, RH gives
`|ψ(ξ) − ξ| ≤ 0.45 ξ^{3/4} + 2`, hence `ψ(ξ) ≤ ξ(1 + 23u/50)` and
`log ψ(ξ) ≤ log ξ + 23u/50`, so that

`ψ(ξ) log ψ(ξ) ≤ ξ log ξ · (1 + 23u/50)(1 + u/25)`;

the elementary inequality `(1 − u/2 − 6u²)(1 + 23u/50)(1 + u/25) ≤ 1 − 3u²` (valid for all
`u ≥ 0`, with equality of the coefficient of `u` being the only close call) then yields the
claim after clearing denominators.
-/

namespace Work.RHContract.A.R3

noncomputable section

open scoped BigOperators

/-- `(10^8)^{−1/4} = 1/100`. -/
lemma ten_pow_eight_rpow_neg_quarter : ((10 : ℝ) ^ 8) ^ (-(1 / 4 : ℝ)) = 1 / 100 := by
  rw [← Real.rpow_natCast (10 : ℝ) 8]
  rw [← Real.rpow_mul (x := (10 : ℝ)) (by norm_num) ((8 : ℕ) : ℝ) (-(1 / 4 : ℝ))]
  norm_num

/-- `16 ≤ log (10^8)`, as `exp 16 < 3^16 < 10^8`. -/
lemma sixteen_le_log_ten_pow_eight : (16 : ℝ) ≤ Real.log ((10 : ℝ) ^ 8) := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 8)]
  have he2 : Real.exp 16 = (Real.exp 1) ^ (16 : ℕ) := by
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [he2]
  have h32 : (Real.exp 1) ^ (16 : ℕ) ≤ (3 : ℝ) ^ (16 : ℕ) :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) 16
  have h9 : (3 : ℝ) ^ (16 : ℕ) < (10 : ℝ) ^ 8 := by norm_num
  linarith

/-- `x^{−1/4} ≤ 1/100` for `x ≥ 10^8`. -/
lemma rpow_neg_quarter_le {x : ℝ} (hx : (10 : ℝ) ^ 8 ≤ x) :
    x ^ (-(1 / 4 : ℝ)) ≤ 1 / 100 :=
  calc x ^ (-(1 / 4 : ℝ)) ≤ ((10 : ℝ) ^ 8) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
    _ = 1 / 100 := ten_pow_eight_rpow_neg_quarter

/-- The elementary polynomial inequality behind the estimate: for every `u ≥ 0`,
`(1 − u/2 − 6u²)(1 + 23u/50)(1 + u/25) ≤ 1 − 3u²`.  The difference of the two sides is
`(8079/2500)u² + (7523/2500)u³ + (69/625)u⁴ ≥ 0`. -/
lemma caC_poly_core (u : ℝ) (hu : 0 ≤ u) :
    (1 - u / 2 - 6 * u ^ (2 : ℕ)) * (1 + (23 / 50) * u) * (1 + (1 / 25) * u)
      ≤ 1 - 3 * u ^ (2 : ℕ) := by
  have hkey : 1 - 3 * u ^ (2 : ℕ)
        - (1 - u / 2 - 6 * u ^ (2 : ℕ)) * (1 + (23 / 50) * u) * (1 + (1 / 25) * u)
      = (8079 / 2500) * u ^ (2 : ℕ) + (7523 / 2500) * u ^ (3 : ℕ) + (69 / 625) * u ^ (4 : ℕ) := by
    ring
  have h2 : 0 ≤ (8079 / 2500 : ℝ) * u ^ (2 : ℕ) := by positivity
  have h3 : 0 ≤ (7523 / 2500 : ℝ) * u ^ (3 : ℕ) := by positivity
  have h4 : 0 ≤ (69 / 625 : ℝ) * u ^ (4 : ℕ) := by positivity
  linarith

/-- **The real-variable estimate.**  For `ξ ≥ 10^8` and `|ψ(ξ) − ξ| ≤ 0.45 ξ^{3/4} + 2`,

`(1 − ξ^{−1/4}/2 − 6 ξ^{−1/2}) / (ξ log ξ) ≤ (1 − 3/√ξ) / (ψ(ξ) log ψ(ξ))`. -/
lemma caC_ge_real (s : ℝ) (hξ : (10 : ℝ) ^ 8 ≤ s)
    (hψ : |Chebyshev.psi s - s| ≤ 0.45 * s ^ (3 / 4 : ℝ) + 2) :
    (1 - (1 / 2) * s ^ (-(1 / 4 : ℝ)) - 6 * s ^ (-(1 / 2 : ℝ))) / (s * Real.log s)
      ≤ (1 - 3 / Real.sqrt s) / (Chebyshev.psi s * Real.log (Chebyshev.psi s)) := by
  have hp8 : (0 : ℝ) < (10 : ℝ) ^ 8 := by norm_num
  have hs0 : 0 < s := lt_of_lt_of_le hp8 hξ
  have hlog16 : (16 : ℝ) ≤ Real.log s :=
    le_trans sixteen_le_log_ten_pow_eight (Real.log_le_log (by norm_num) hξ)
  have hlogpos : 0 < Real.log s := by linarith
  set u : ℝ := s ^ (-(1 / 4 : ℝ)) with hu
  have hu0 : 0 ≤ u := by rw [hu]; exact Real.rpow_nonneg hs0.le _
  have hule : u ≤ 1 / 100 := rpow_neg_quarter_le hξ
  have hu2 : u ^ (2 : ℕ) = s ^ (-(1 / 2 : ℝ)) := by
    rw [hu, ← Real.rpow_natCast (s ^ (-(1 / 4 : ℝ))) 2]
    rw [← Real.rpow_mul (x := s) hs0.le (-(1 / 4 : ℝ)) ((2 : ℕ) : ℝ)]
    norm_num
  have hu4 : u ^ (4 : ℕ) = s⁻¹ := by
    rw [hu, ← Real.rpow_natCast (s ^ (-(1 / 4 : ℝ))) 4]
    rw [← Real.rpow_mul (x := s) hs0.le (-(1 / 4 : ℝ)) ((4 : ℕ) : ℝ)]
    norm_num
    rw [Real.rpow_neg_one]
  have hs34 : s ^ (3 / 4 : ℝ) = s * u := by
    rw [hu]
    rw [show (3 / 4 : ℝ) = 1 + (-(1 / 4)) by norm_num, Real.rpow_add hs0, Real.rpow_one]
  have hψ_lb : s - (0.45 * s ^ (3 / 4 : ℝ) + 2) ≤ Chebyshev.psi s := by
    have h1 := (abs_le.mp hψ).1
    linarith
  have hψ_ub : Chebyshev.psi s - s ≤ 0.45 * s ^ (3 / 4 : ℝ) + 2 := (abs_le.mp hψ).2
  have hψ_up1 : Chebyshev.psi s ≤ s * (1 + (9 / 20) * u + 2 * u ^ (4 : ℕ)) := by
    have h2 : (2 : ℝ) = s * (2 * u ^ (4 : ℕ)) := by
      rw [hu4]; field_simp
    have h3 : (0.45 : ℝ) = 9 / 20 := by norm_num
    nlinarith [hψ_ub, hs34, h3, h2]
  have h24 : 2 * u ^ (4 : ℕ) ≤ (1 / 100) * u := by
    have h1 : u ^ (3 : ℕ) ≤ (1 / 100 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hu0 hule 3
    have h1b : (1 / 100 : ℝ) ^ (3 : ℕ) = 1 / 1000000 := by norm_num
    rw [h1b] at h1
    have he : u ^ (4 : ℕ) = u ^ (3 : ℕ) * u := by ring
    rw [he]
    nlinarith [h1, hu0, mul_le_mul_of_nonneg_right h1 hu0]
  have hψ_up2 : Chebyshev.psi s ≤ s * (1 + (23 / 50) * u) := by
    have hcoef : (1 + (9 / 20) * u + 2 * u ^ (4 : ℕ)) ≤ 1 + (23 / 50) * u := by linarith [h24]
    exact le_trans hψ_up1 (mul_le_mul_of_nonneg_left hcoef hs0.le)
  have hψ1 : 1 < Chebyshev.psi s := by
    have hu_le' : (9 / 20 : ℝ) * u ≤ 0.0045 := by nlinarith [hu0, hule]
    rw [hs34] at hψ_lb
    have h45 : (0.45 : ℝ) = 9 / 20 := by norm_num
    rw [h45] at hψ_lb
    nlinarith [hψ_lb, hu_le', hs0, hξ]
  have hψpos : 0 < Chebyshev.psi s := by linarith
  have hlogψpos : 0 < Real.log (Chebyshev.psi s) := Real.log_pos hψ1
  have hlogψ_le : Real.log (Chebyshev.psi s) ≤ Real.log s + (23 / 50) * u := by
    have h1 : Real.log (Chebyshev.psi s) ≤ Real.log (s * (1 + (23 / 50) * u)) :=
      Real.log_le_log hψpos hψ_up2
    have hne : (1 + (23 / 50) * u) ≠ 0 := by nlinarith [hu0]
    have h2 : Real.log (s * (1 + (23 / 50) * u))
        = Real.log s + Real.log (1 + (23 / 50) * u) := Real.log_mul (ne_of_gt hs0) hne
    have h3 : Real.log (1 + (23 / 50) * u) ≤ (23 / 50) * u := by
      have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + (23 / 50) * u by nlinarith [hu0])
      linarith
    linarith
  have hprod : Chebyshev.psi s * Real.log (Chebyshev.psi s)
      ≤ s * Real.log s * ((1 + (23 / 50) * u) * (1 + (1 / 25) * u)) := by
    have h1 : Chebyshev.psi s * Real.log (Chebyshev.psi s)
        ≤ (s * (1 + (23 / 50) * u)) * (Real.log s + (23 / 50) * u) :=
      mul_le_mul hψ_up2 hlogψ_le hlogψpos.le
        (mul_nonneg hs0.le (by nlinarith [hu0]))
    refine le_trans h1 ?_
    have hG : 0 ≤ s * Real.log s * (1 + (23 / 50) * u) :=
      mul_nonneg (mul_pos hs0 hlogpos).le (by nlinarith [hu0])
    have hdiv : (23 / 50) * u / Real.log s ≤ (1 / 25) * u := by
      rw [div_le_iff₀ hlogpos]
      nlinarith [hu0, hlog16]
    have heq : (s * (1 + (23 / 50) * u)) * (Real.log s + (23 / 50) * u)
        = (s * Real.log s * (1 + (23 / 50) * u)) * (1 + ((23 / 50) * u) / Real.log s) := by
      field_simp
    rw [heq]
    calc (s * Real.log s * (1 + (23 / 50) * u)) * (1 + (23 / 50) * u / Real.log s)
        ≤ (s * Real.log s * (1 + (23 / 50) * u)) * (1 + (1 / 25) * u) :=
          mul_le_mul_of_nonneg_left (by linarith) hG
      _ = s * Real.log s * ((1 + (23 / 50) * u) * (1 + (1 / 25) * u)) := by ring
  have hA : 0 ≤ 1 - u / 2 - 6 * u ^ (2 : ℕ) := by nlinarith [hu0, hule]
  have hcore : (1 - u / 2 - 6 * u ^ (2 : ℕ)) * (Chebyshev.psi s * Real.log (Chebyshev.psi s))
      ≤ (1 - 3 * u ^ (2 : ℕ)) * (s * Real.log s) := by
    have h1 : (1 - u / 2 - 6 * u ^ (2 : ℕ)) * (Chebyshev.psi s * Real.log (Chebyshev.psi s))
        ≤ (1 - u / 2 - 6 * u ^ (2 : ℕ))
            * (s * Real.log s * ((1 + (23 / 50) * u) * (1 + (1 / 25) * u))) :=
      mul_le_mul_of_nonneg_left hprod hA
    have h3 : 0 ≤ s * Real.log s := (mul_pos hs0 hlogpos).le
    have h4 : (1 - u / 2 - 6 * u ^ (2 : ℕ)) * ((1 + (23 / 50) * u) * (1 + (1 / 25) * u))
        ≤ 1 - 3 * u ^ (2 : ℕ) := by
      have he : (1 - u / 2 - 6 * u ^ (2 : ℕ)) * ((1 + (23 / 50) * u) * (1 + (1 / 25) * u))
          = (1 - u / 2 - 6 * u ^ (2 : ℕ)) * (1 + (23 / 50) * u) * (1 + (1 / 25) * u) := by
        ring
      rw [he]; exact caC_poly_core u hu0
    calc (1 - u / 2 - 6 * u ^ (2 : ℕ)) * (Chebyshev.psi s * Real.log (Chebyshev.psi s))
        ≤ (1 - u / 2 - 6 * u ^ (2 : ℕ))
            * (s * Real.log s * ((1 + (23 / 50) * u) * (1 + (1 / 25) * u))) := h1
      _ = s * Real.log s
            * ((1 - u / 2 - 6 * u ^ (2 : ℕ)) * ((1 + (23 / 50) * u) * (1 + (1 / 25) * u))) := by
          ring
      _ ≤ s * Real.log s * (1 - 3 * u ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left h4 h3
      _ = (1 - 3 * u ^ (2 : ℕ)) * (s * Real.log s) := by ring
  have hnum : 1 - (1 / 2) * s ^ (-(1 / 4 : ℝ)) - 6 * s ^ (-(1 / 2 : ℝ))
      = 1 - u / 2 - 6 * u ^ (2 : ℕ) := by
    rw [← hu, ← hu2]
    ring
  have hden : 1 - 3 / Real.sqrt s = 1 - 3 * u ^ (2 : ℕ) := by
    have h : 3 / Real.sqrt s = 3 * u ^ (2 : ℕ) := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hs0.le (1 / 2 : ℝ), ← hu2]
    rw [h]
  rw [hnum, hden]
  rw [div_le_div_iff₀ (mul_pos hs0 hlogpos) (mul_pos hψpos hlogψpos)]
  exact hcore

/-- **`caC_ge`.**  Under RH, for a colossally abundant number with `ξ(ε) ≥ 10^8`, the
coefficient `c(ε) = (1 − 3/√ξ)/(ψ(ξ) log ψ(ξ))` dominates
`(1 − ξ^{−1/4}/2 − 6ξ^{−1/2})/(ξ log ξ)`. -/
theorem caC_ge (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    (1 - (1 / 2) * (Work.RHPlan.caXi ε : ℝ) ^ (-(1 / 4 : ℝ))
        - 6 * (Work.RHPlan.caXi ε : ℝ) ^ (-(1 / 2 : ℝ)))
      / ((Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ))
      ≤ Work.RHContract.Margin.caC ε := by
  unfold Work.RHContract.Margin.caC
  exact caC_ge_real _ hξ
    (Work.RHContract.A.psi_sub_le_of_RH h _ (le_trans (by norm_num : (200 : ℝ) ≤ (10 : ℝ) ^ 8) hξ))

end

end Work.RHContract.A.R3
