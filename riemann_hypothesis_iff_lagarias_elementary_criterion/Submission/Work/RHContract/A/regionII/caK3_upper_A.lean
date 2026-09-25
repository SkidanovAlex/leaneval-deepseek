import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.caLevel_le
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.Corpus
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt
import Submission.Commons.NumberTheory.Primes.prime_gap_123
import Submission.Work.RHContract.A.RegionIII.caK3_upper_regionIII

/-!
# Region II: the deep-level loss `caK3` is at most `4%` of the margin scale

For `ξ = ξ(ε) = caXi ε ∈ [3·10^4, 10^5)` we prove

`Margin.caK3 ε ≤ (4/100) · caU ξ`,   `caU ξ = 1/(√ξ · log ξ)`.

This is the region-II analogue of `RegionIII.caK3_upper_regionIII`, with the crude per-summand
constant `1/100` replaced by the sharper `1/25`: on `[59,10^5]` the certified Chebyshev bracket
gives `θ ξ ≤ ξ` (rather than `1.1056 ξ`), so `ψ ξ ≤ ξ + 3√ξ` and
`caC ε = (1−3/√ξ)/(ψ log ψ) ≥ (24/25)/(ξ log ξ)`.
-/

namespace Work.RHContract.A.regionII

open scoped BigOperators

noncomputable section


/-- `∑_{p ≤ 71} log p/(p-1) ≤ 4` (certified finite computation; the true value is ≈ 3.858). -/
lemma sum_log_div_sub_one_le_71 :
    (∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ) / ((p:ℝ)-1)) ≤ 4 := by
  have hset : Nat.primesLE 71 = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ) := by decide
  rw [hset]
  rw [Finset.sum_insert (by decide : (2:ℕ) ∉ ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (3:ℕ) ∉ ({5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (5:ℕ) ∉ ({7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (7:ℕ) ∉ ({11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (11:ℕ) ∉ ({13,17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (13:ℕ) ∉ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (17:ℕ) ∉ ({19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (19:ℕ) ∉ ({23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (23:ℕ) ∉ ({29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (29:ℕ) ∉ ({31,37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (31:ℕ) ∉ ({37,41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (37:ℕ) ∉ ({41,43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (41:ℕ) ∉ ({43,47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (43:ℕ) ∉ ({47,53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (47:ℕ) ∉ ({53,59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (53:ℕ) ∉ ({59,61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (59:ℕ) ∉ ({61,67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (61:ℕ) ∉ ({67,71} : Finset ℕ))]
  rw [Finset.sum_insert (by decide : (67:ℕ) ∉ ({71} : Finset ℕ))]
  rw [Finset.sum_singleton]
  have e2 : Real.log (2:ℝ)/((2:ℝ)-1) ≤ (7/10)/((2:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/10 by norm_num) 25
      have h2 : (2:ℝ) ≤ ∑ i ∈ Finset.range 25, (7/10:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e3 : Real.log (3:ℝ)/((3:ℝ)-1) ≤ (11/10)/((3:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 11/10 by norm_num) 25
      have h2 : (3:ℝ) ≤ ∑ i ∈ Finset.range 25, (11/10:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e5 : Real.log (5:ℝ)/((5:ℝ)-1) ≤ (161/100)/((5:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 161/100 by norm_num) 25
      have h2 : (5:ℝ) ≤ ∑ i ∈ Finset.range 25, (161/100:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e7 : Real.log (7:ℝ)/((7:ℝ)-1) ≤ (39/20)/((7:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 39/20 by norm_num) 25
      have h2 : (7:ℝ) ≤ ∑ i ∈ Finset.range 25, (39/20:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e11 : Real.log (11:ℝ)/((11:ℝ)-1) ≤ (12/5)/((11:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 12/5 by norm_num) 25
      have h2 : (11:ℝ) ≤ ∑ i ∈ Finset.range 25, (12/5:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e13 : Real.log (13:ℝ)/((13:ℝ)-1) ≤ (257/100)/((13:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 257/100 by norm_num) 25
      have h2 : (13:ℝ) ≤ ∑ i ∈ Finset.range 25, (257/100:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e17 : Real.log (17:ℝ)/((17:ℝ)-1) ≤ (71/25)/((17:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 71/25 by norm_num) 25
      have h2 : (17:ℝ) ≤ ∑ i ∈ Finset.range 25, (71/25:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e19 : Real.log (19:ℝ)/((19:ℝ)-1) ≤ (59/20)/((19:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 59/20 by norm_num) 25
      have h2 : (19:ℝ) ≤ ∑ i ∈ Finset.range 25, (59/20:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e23 : Real.log (23:ℝ)/((23:ℝ)-1) ≤ (157/50)/((23:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 157/50 by norm_num) 25
      have h2 : (23:ℝ) ≤ ∑ i ∈ Finset.range 25, (157/50:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e29 : Real.log (29:ℝ)/((29:ℝ)-1) ≤ (337/100)/((29:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 337/100 by norm_num) 25
      have h2 : (29:ℝ) ≤ ∑ i ∈ Finset.range 25, (337/100:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e31 : Real.log (31:ℝ)/((31:ℝ)-1) ≤ (86/25)/((31:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 86/25 by norm_num) 25
      have h2 : (31:ℝ) ≤ ∑ i ∈ Finset.range 25, (86/25:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e37 : Real.log (37:ℝ)/((37:ℝ)-1) ≤ (181/50)/((37:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 181/50 by norm_num) 25
      have h2 : (37:ℝ) ≤ ∑ i ∈ Finset.range 25, (181/50:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e41 : Real.log (41:ℝ)/((41:ℝ)-1) ≤ (93/25)/((41:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 93/25 by norm_num) 25
      have h2 : (41:ℝ) ≤ ∑ i ∈ Finset.range 25, (93/25:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e43 : Real.log (43:ℝ)/((43:ℝ)-1) ≤ (377/100)/((43:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 377/100 by norm_num) 25
      have h2 : (43:ℝ) ≤ ∑ i ∈ Finset.range 25, (377/100:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e47 : Real.log (47:ℝ)/((47:ℝ)-1) ≤ (193/50)/((47:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 193/50 by norm_num) 25
      have h2 : (47:ℝ) ≤ ∑ i ∈ Finset.range 25, (193/50:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e53 : Real.log (53:ℝ)/((53:ℝ)-1) ≤ (199/50)/((53:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 199/50 by norm_num) 25
      have h2 : (53:ℝ) ≤ ∑ i ∈ Finset.range 25, (199/50:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e59 : Real.log (59:ℝ)/((59:ℝ)-1) ≤ (102/25)/((59:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 102/25 by norm_num) 25
      have h2 : (59:ℝ) ≤ ∑ i ∈ Finset.range 25, (102/25:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e61 : Real.log (61:ℝ)/((61:ℝ)-1) ≤ (103/25)/((61:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 103/25 by norm_num) 25
      have h2 : (61:ℝ) ≤ ∑ i ∈ Finset.range 25, (103/25:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e67 : Real.log (67:ℝ)/((67:ℝ)-1) ≤ (421/100)/((67:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 421/100 by norm_num) 25
      have h2 : (67:ℝ) ≤ ∑ i ∈ Finset.range 25, (421/100:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have e71 : Real.log (71:ℝ)/((71:ℝ)-1) ≤ (427/100)/((71:ℝ)-1) := by
    apply div_le_div_of_nonneg_right
    · rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 427/100 by norm_num) 25
      have h2 : (71:ℝ) ≤ ∑ i ∈ Finset.range 25, (427/100:ℝ)^i/(i.factorial) := by norm_num
      linarith
    · norm_num
  have hnum : (7/10)/((2:ℝ)-1) + (11/10)/((3:ℝ)-1) + (161/100)/((5:ℝ)-1) + (39/20)/((7:ℝ)-1) + (12/5)/((11:ℝ)-1) + (257/100)/((13:ℝ)-1) + (71/25)/((17:ℝ)-1) + (59/20)/((19:ℝ)-1) + (157/50)/((23:ℝ)-1) + (337/100)/((29:ℝ)-1) + (86/25)/((31:ℝ)-1) + (181/50)/((37:ℝ)-1) + (93/25)/((41:ℝ)-1) + (377/100)/((43:ℝ)-1) + (193/50)/((47:ℝ)-1) + (199/50)/((53:ℝ)-1) + (102/25)/((59:ℝ)-1) + (103/25)/((61:ℝ)-1) + (421/100)/((67:ℝ)-1) + (427/100)/((71:ℝ)-1) ≤ 4 := by norm_num
  linarith [e2, e3, e5, e7, e11, e13, e17, e19, e23, e29, e31, e37, e41, e43, e47, e53, e59, e61, e67, e71, hnum]

/-- **Lower bound for `caC ε` on Region II.**  For `ξ = caXi ε ∈ [3·10^4, 10^5)` one has
`(24/25)/(ξ log ξ) ≤ caC ε`. -/
lemma caC_ge_regionII (ε : ℝ) (ξ : ℝ) (hξ : (Work.RHPlan.caXi ε : ℝ) = ξ)
    (hε : 0 < ε) (hlo : 30000 ≤ ξ) (hhi : ξ < 100000) :
    (24/25 : ℝ) / (ξ * Real.log ξ) ≤ Work.RHContract.Margin.caC ε := by
  have hξ1 : 1 < ξ := by linarith
  have hξ0 : 0 < ξ := by linarith
  have hLpos : 0 < Real.log ξ := Real.log_pos hξ1
  set s : ℝ := Real.sqrt ξ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hξ0
  have hs2 : s ^ 2 = ξ := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt hξ0)
  have hs173 : 173 ≤ s := by
    rw [hsdef]
    have h1 : (173:ℝ) ≤ Real.sqrt 30000 := by
      have h : (173:ℝ) ^ 2 ≤ 30000 := by norm_num
      calc (173:ℝ) = Real.sqrt ((173:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt 30000 := Real.sqrt_le_sqrt h
    exact le_trans h1 (Real.sqrt_le_sqrt hlo)
  have hlogs5 : 5 ≤ Real.log s := by
    have h1 : Real.log 173 ≤ Real.log s := Real.log_le_log (by norm_num) hs173
    have h2 : (5:ℝ) ≤ Real.log 173 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have hexp : Real.exp (5:ℝ) = (Real.exp 1)^5 := by
        rw [show (5:ℝ) = ((5:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [hexp]
      have he1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
      have h3 : (Real.exp 1)^5 < (2.72:ℝ)^5 :=
        pow_lt_pow_left₀ he1 (le_of_lt (Real.exp_pos 1)) (by norm_num)
      have h4 : (2.72:ℝ)^5 ≤ 173 := by norm_num
      linarith
    linarith
  have hL_eq : Real.log ξ = 2 * Real.log s := by rw [← hs2, Real.log_pow]; ring
  have h59 : 59 ≤ Work.RHPlan.caXi ε := by
    have h : (59:ℝ) ≤ ((Work.RHPlan.caXi ε : ℕ) : ℝ) := by rw [hξ]; linarith
    exact_mod_cast h
  have h1e5 : Work.RHPlan.caXi ε ≤ 10^5 := by
    have h2 : Work.RHPlan.caXi ε < 100000 := by
      have h : (((Work.RHPlan.caXi ε : ℕ)):ℝ) < 100000 := by rw [hξ]; exact hhi
      exact_mod_cast h
    omega
  obtain ⟨hbrk, hθle⟩ :=
    Commons.NumberTheory.Chebyshev.theta_bracket_finite_range (Work.RHPlan.caXi ε) h59 h1e5
  have hθle' : Chebyshev.theta ξ ≤ ξ := by rw [← hξ]; exact hθle
  have hθpos : 0 < Chebyshev.theta ξ := by
    have h2mem : 2 ∈ Nat.primesLE (Work.RHPlan.caXi ε) :=
      Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
    have hle : Real.log (2:ℝ) ≤ Chebyshev.theta ξ := by
      rw [← hξ, Chebyshev.theta_eq_sum_primesLE_log]
      exact Finset.single_le_sum (f := fun p : ℕ => Real.log (p:ℝ))
        (fun p hp => Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Nat.mem_primesLE.mp hp).2)))
        h2mem
    linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have hψpos : 0 < Chebyshev.psi ξ := lt_of_lt_of_le hθpos (Chebyshev.theta_le_psi ξ)
  have hψub : Chebyshev.psi ξ ≤ s ^ 2 + 3 * s := by
    have h := Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt ξ (by linarith)
    have h1 : Chebyshev.psi ξ - Chebyshev.theta ξ ≤ 3 * s := by simpa only [hsdef] using h
    linarith [h1, hθle', hs2]
  have hlogψ : Real.log (Chebyshev.psi ξ) ≤ 2 * Real.log s + 3/s := by
    have h1 : Real.log (Chebyshev.psi ξ) ≤ Real.log (s*(s+3)) := by
      apply Real.log_le_log hψpos
      have : s*(s+3) = s^2 + 3*s := by ring
      rw [this]; exact hψub
    have h2 : Real.log (s*(s+3)) = Real.log s + Real.log (s+3) :=
      Real.log_mul (ne_of_gt hs0) (by positivity)
    have h3 : Real.log (s+3) ≤ Real.log s + 3/s := by
      have he : s + 3 = s * (1 + 3/s) := by field_simp <;> ring_nf
      rw [he, Real.log_mul (ne_of_gt hs0) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 3/s by positivity)
      linarith
    linarith
  have hRHSpos : 0 < (s^2 + 3*s) * (2 * Real.log s + 3/s) := by
    have h1 : 0 < 2 * Real.log s + 3/s := by
      have := Real.log_pos (by linarith : (1:ℝ) < s); positivity
    have h2 : 0 < s^2 + 3*s := by positivity
    positivity
  have hprod : Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)
      ≤ (s^2 + 3*s) * (2 * Real.log s + 3/s) := by
    rcases lt_or_ge (Real.log (Chebyshev.psi ξ)) 0 with hlg | hlg
    · have h1 : Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hψpos) (le_of_lt hlg)
      linarith [h1, le_of_lt hRHSpos]
    · exact mul_le_mul hψub hlogψ hlg (by positivity)
  have hquad : (0:ℝ) ≤ 10*s^2 - 1542*s - 216 := by
    have h1 : (0:ℝ) ≤ s - 173 := by linarith
    have h2 : 10*s^2 - 1542*s - 216 = 10*(s-173)^2 + 1918*(s-173) + 32308 := by ring
    rw [h2]; nlinarith [sq_nonneg (s - 173), h1]
  have hslog : 5 * s * (2*s - 294) ≤ s * Real.log s * (2*s - 294) := by
    have h2 : (0:ℝ) ≤ s * (2*s - 294) := by
      have : (0:ℝ) ≤ 2*s - 294 := by linarith
      positivity
    have h3 := mul_le_mul_of_nonneg_right hlogs5 h2
    nlinarith [h3]
  have hfinal : (0:ℝ) ≤ 2*s^2*Real.log s - 294*s*Real.log s - 72*s - 216 := by
    have hid : 2*s^2*Real.log s - 294*s*Real.log s = s * Real.log s * (2*s - 294) := by ring
    have hid2 : 5 * s * (2*s - 294) = 10*s^2 - 1470*s := by ring
    rw [hid]; linarith [hslog, hid2, hquad]
  have hkey : 24 * (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ))
      ≤ 25 * (1 - 3/s) * ξ * Real.log ξ := by
    have h1 : 24 * (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ))
        ≤ 24 * ((s^2 + 3*s) * (2 * Real.log s + 3/s)) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    have hLHSid : (s^2+3*s)*(2*Real.log s + 3/s)
        = 2*s^2*Real.log s + 6*s*Real.log s + 3*s + 9 := by
      field_simp <;> ring_nf
    have hRHSid : 25 * (1 - 3/s) * ξ * Real.log ξ = 50*s^2*Real.log s - 150*s*Real.log s := by
      rw [hL_eq, ← hs2]; field_simp <;> ring_nf
    have h2 : 24 * ((s^2 + 3*s) * (2 * Real.log s + 3/s))
        ≤ 25 * (1 - 3/s) * ξ * Real.log ξ := by
      rw [hLHSid, hRHSid]; nlinarith [hfinal]
    linarith [h1, h2]
  have hψgt1 : 1 < Chebyshev.psi ξ := by
    have hθ23 : Real.log 2 + Real.log 3 ≤ Chebyshev.theta ξ := by
      rw [← hξ, Chebyshev.theta_eq_sum_primesLE_log]
      have hsub : ({2,3} : Finset ℕ) ⊆ Nat.primesLE (Work.RHPlan.caXi ε) := by
        intro q hq
        rw [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
        · exact Nat.mem_primesLE.mpr ⟨by omega, by norm_num⟩
      have h2 : (∑ x ∈ ({2,3} : Finset ℕ), Real.log (x:ℝ))
          ≤ ∑ x ∈ Nat.primesLE (Work.RHPlan.caXi ε), Real.log (x:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hi _ => Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Nat.mem_primesLE.mp hi).2)))
      rwa [Finset.sum_insert (by decide), Finset.sum_singleton] at h2
    have hlog6 : (1:ℝ) < Real.log 2 + Real.log 3 := by
      have h : (1:ℝ) < Real.log 6 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith [Real.exp_one_lt_d9]
      rwa [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at h
    linarith [Chebyshev.theta_le_psi ξ, hθ23, hlog6]
  have hcaC : Work.RHContract.Margin.caC ε
      = (1 - 3/s)/(Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) := by
    unfold Work.RHContract.Margin.caC
    rw [hξ, show Real.sqrt ξ = s from hsdef.symm]
  have hlogψpos : 0 < Real.log (Chebyshev.psi ξ) := Real.log_pos hψgt1
  rw [hcaC, div_le_div_iff₀ (by positivity) (mul_pos hψpos hlogψpos)]
  linarith [hkey]

/-- **Per-summand numeric core (Region II).** -/
lemma caK3_term_core {ξ : ℝ} (hξ1 : 1 < ξ) {p e : ℕ} (hp2 : 2 ≤ p)
    (hpow : ξ < (p:ℝ) ^ (e+1)) {c : ℝ}
    (hc : (24/25 : ℝ)/(ξ * Real.log ξ) ≤ c) :
    max 0 ((p:ℝ) ^ (-(((e:ℝ) + 1))) / (((e:ℝ) + 1) * (1 - 1/(p:ℝ)))
        - c * Real.log (p:ℝ))
      ≤ Real.log (p:ℝ) / (ξ * Real.log ξ) * (1/((p:ℝ)-1) + 1/25) := by
  have hξ0 : 0 < ξ := by linarith
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξ1
  have hP0 : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hP1 : 1 < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogP : 0 < Real.log (p:ℝ) := Real.log_pos hP1
  have hkR : 0 < ((e:ℝ) + 1) := by positivity
  have hpowR : ξ < (p:ℝ) ^ (((e:ℝ)+1)) := by
    have hc2 : (p:ℝ) ^ (((e:ℝ)+1)) = (p:ℝ) ^ (e+1) := by
      rw [show (((e:ℝ)+1)) = ((e+1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hc2]; exact hpow
  have hloglt : Real.log ξ < ((e:ℝ) + 1) * Real.log (p:ℝ) := by
    have h := Real.log_lt_log hξ0 hpowR
    rwa [Real.log_rpow hP0] at h
  have hlogdiv : Real.log ξ / ((e:ℝ)+1) < Real.log (p:ℝ) := by
    rw [div_lt_iff₀ hkR]; linarith
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hden : 0 < (((e:ℝ) + 1) * (1 - 1/(p:ℝ))) := by
    refine mul_pos hkR ?_
    rw [sub_pos, div_lt_one hP0]; linarith
  have hinv : (p:ℝ) ^ (-(((e:ℝ) + 1))) ≤ 1/ξ := by
    rw [Real.rpow_neg (le_of_lt hP0), inv_eq_one_div]
    exact le_of_lt (one_div_lt_one_div_of_lt hξ0 hpowR)
  have hA : (p:ℝ) ^ (-(((e:ℝ) + 1))) / (((e:ℝ) + 1) * (1 - 1/(p:ℝ)))
      ≤ (1/ξ) * (1/((e:ℝ)+1)) * (1 + 1/((p:ℝ)-1)) := by
    have hstep : (p:ℝ) ^ (-(((e:ℝ) + 1))) / (((e:ℝ) + 1) * (1 - 1/(p:ℝ)))
        ≤ (1/ξ) / (((e:ℝ) + 1) * (1 - 1/(p:ℝ))) :=
      div_le_div_of_nonneg_right hinv (le_of_lt hden)
    refine le_trans hstep ?_
    have heq : (1/ξ) / (((e:ℝ) + 1) * (1 - 1/(p:ℝ)))
        = (1/ξ) * (1/((e:ℝ)+1)) * (1 + 1/((p:ℝ)-1)) := by
      have hpne : (p:ℝ) - 1 ≠ 0 := by linarith
      have hkne : ((e:ℝ)+1) ≠ 0 := ne_of_gt hkR
      field_simp <;> ring_nf
    rw [heq]
  have hc_log : (24/25 : ℝ) / (((e:ℝ)+1) * ξ) ≤ c * Real.log (p:ℝ) := by
    have h1 : (24/25 : ℝ) / (((e:ℝ)+1) * ξ)
        = ((24/25 : ℝ)/(ξ * Real.log ξ)) * (Real.log ξ / ((e:ℝ)+1)) := by
      field_simp <;> ring_nf
    rw [h1]
    have h2 : ((24/25 : ℝ)/(ξ * Real.log ξ)) * (Real.log ξ / ((e:ℝ)+1))
        ≤ c * (Real.log ξ / ((e:ℝ)+1)) := mul_le_mul_of_nonneg_right hc (by positivity)
    have h3 : c * (Real.log ξ / ((e:ℝ)+1)) ≤ c * Real.log (p:ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlogdiv) hc0
    linarith [h2, h3]
  have hT : (p:ℝ) ^ (-(((e:ℝ) + 1))) / (((e:ℝ) + 1) * (1 - 1/(p:ℝ))) - c * Real.log (p:ℝ)
      ≤ (1/ξ) * (1/((e:ℝ)+1)) * (1 + 1/((p:ℝ)-1)) - (24/25 : ℝ) / (((e:ℝ)+1) * ξ) := by
    linarith [hA, hc_log]
  have hfin : (1/ξ) * (1/((e:ℝ)+1)) * (1 + 1/((p:ℝ)-1)) - (24/25 : ℝ) / (((e:ℝ)+1) * ξ)
      ≤ Real.log (p:ℝ) / (ξ * Real.log ξ) * (1/((p:ℝ)-1) + 1/25) := by
    have heq : (1/ξ) * (1/((e:ℝ)+1)) * (1 + 1/((p:ℝ)-1)) - (24/25 : ℝ) / (((e:ℝ)+1) * ξ)
        = (1/(ξ * ((e:ℝ)+1))) * (1/((p:ℝ)-1) + 1/25) := by
      have hpne : (p:ℝ) - 1 ≠ 0 := by linarith
      have hkne : ((e:ℝ)+1) ≠ 0 := ne_of_gt hkR
      field_simp <;> ring_nf
    rw [heq]
    have hcoef : (1/(ξ * ((e:ℝ)+1))) ≤ Real.log (p:ℝ) / (ξ * Real.log ξ) := by
      rw [div_le_div_iff₀ (mul_pos hξ0 hkR) (mul_pos hξ0 hlogξ)]
      nlinarith [hloglt, hξ0.le, hlogξ]
    have hinner : 0 ≤ 1/((p:ℝ)-1) + 1/25 := by
      have : 0 < (p:ℝ) - 1 := by linarith
      positivity
    exact mul_le_mul_of_nonneg_right hcoef hinner
  exact max_le (by positivity) (le_trans hT hfin)

/-- **The `Margin.caK3 ε` index set lies in the primes `≤ 71`** for `ξ ∈ [3·10^4, 10^5)`. -/
lemma caK3_index_le_71 (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 100000)
    {p : ℕ}
    (hp : p ∈ (Nat.primesLE ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊).filter
        (fun q : ℕ => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊)) :
    p ∈ Nat.primesLE 71 := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ : (Work.RHPlan.caXi ε : ℝ) = ξ := hξdef.symm
  have hξ30000 : 30000 ≤ ξ := by rw [← hξ]; exact hlo
  have hξ0 : 0 < ξ := by linarith
  have hξNpos : 0 < Work.RHPlan.caXi ε := by
    have : (0:ℝ) < ((Work.RHPlan.caXi ε : ℕ) : ℝ) := by rw [hξ]; linarith
    exact_mod_cast this
  have hp_mem1 : p ∈ Nat.primesLE ⌊Real.sqrt ξ⌋₊ := (Finset.mem_filter.mp hp).1
  have hp_cond : Work.RHContract.Margin.caExpFloor ε p < ⌊Work.RHPlan.caMu p ε⌋₊ :=
    (Finset.mem_filter.mp hp).2
  have hp_prime : Nat.Prime p := (Nat.mem_primesLE.mp hp_mem1).2
  have hp_le : p ≤ ⌊Real.sqrt ξ⌋₊ := (Nat.mem_primesLE.mp hp_mem1).1
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hp1r : 1 < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0r : (0:ℝ) < (p:ℝ) := by linarith
  have hp2floor : p^2 ≤ ⌊ξ⌋₊ := by
    apply Nat.le_floor
    have hle1 : (p:ℝ) ≤ ((⌊Real.sqrt ξ⌋₊ : ℕ):ℝ) := by exact_mod_cast hp_le
    have hle2 : ((⌊Real.sqrt ξ⌋₊ : ℕ):ℝ) ≤ Real.sqrt ξ := Nat.floor_le (Real.sqrt_nonneg ξ)
    have hξsq : (Real.sqrt ξ)^2 = ξ := Real.sq_sqrt (le_of_lt hξ0)
    push_cast
    calc (p:ℝ)^2 ≤ ((⌊Real.sqrt ξ⌋₊ : ℕ):ℝ)^2 := by nlinarith
      _ ≤ (Real.sqrt ξ)^2 := by nlinarith [Real.sqrt_nonneg ξ]
      _ = ξ := hξsq
  have hfloorpos : ⌊ξ⌋₊ ≠ 0 := by
    have : 0 < ⌊ξ⌋₊ := Nat.floor_pos.mpr (by linarith : (1:ℝ) ≤ ξ)
    omega
  have he2 : 2 ≤ Work.RHContract.Margin.caExpFloor ε p := by
    rw [Work.RHContract.Margin.caExpFloor, hξ]
    exact (Nat.le_log_iff_pow_le (by omega : 1 < p) hfloorpos).mpr hp2floor
  have ha3 : 3 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by omega
  have hμpos : 0 < Work.RHPlan.caMu p ε := Commons.NumberTheory.Robin.caMu_pos hp2 hε
  have hmu3 : (3:ℝ) ≤ Work.RHPlan.caMu p ε :=
    le_trans (by exact_mod_cast ha3) (Nat.floor_le (le_of_lt hμpos))
  have hεFf : ε ≤ Work.RHContract.A.caFf 3 (p:ℝ) :=
    (Work.RHContract.A.caMu_ge_iff_caFf p hp2 ε hε 3 (by norm_num)).mp hmu3
  have hG : Work.RHContract.A.caG (1.23 * ξ) < ε := by
    have h := Work.RHContract.A.RegionIII.caG_mul_xi_lt ε hε
      (by rw [hξ]; linarith)
    rwa [hξ] at h
  have hp3le : (p:ℝ)^3 ≤ 3.69 * ξ := by
    have h := Work.RHContract.A.caG_le_caFf_imp (1.23 * ξ) (p:ℝ) (by nlinarith) hp1r 3 (by norm_num)
      (le_trans (le_of_lt hG) hεFf)
    nlinarith [h]
  have hfloor_le : p ≤ ⌊(3.69 * ξ)^(1/3:ℝ)⌋₊ := by
    have hcbrt : ((p:ℝ)^3)^(1/3:ℝ) = (p:ℝ) := by
      rw [show ((p:ℝ)^3) = (p:ℝ)^((3:ℕ):ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_mul (le_of_lt hp0r),
        show ((3:ℕ):ℝ)*(1/3:ℝ) = 1 by norm_num, Real.rpow_one]
    have hple : (p:ℝ) ≤ (3.69*ξ)^(1/3:ℝ) := by
      rw [← hcbrt]
      exact Real.rpow_le_rpow (by positivity) hp3le (by norm_num)
    exact Nat.le_floor hple
  have hM71 : ⌊(3.69 * ξ)^(1/3:ℝ)⌋₊ ≤ 71 := by
    have hlt : (3.69*ξ)^(1/3:ℝ) < 72 := by
      have h2 : (3.69:ℝ)*ξ < 72^3 := by
        have hh : (3.69:ℝ)*ξ < 3.69 * 100000 := by
          refine mul_lt_mul_of_pos_left ?_ (by norm_num)
          rw [← hξ]; exact hhi
        linarith [show (3.69:ℝ)*100000 < 72^3 by norm_num]
      have h3 := Real.rpow_lt_rpow (by positivity) h2 (by norm_num : (0:ℝ) < 1/3)
      rwa [show ((72:ℝ)^3)^(1/3:ℝ) = 72 by
        rw [show ((72:ℝ)^3) = (72:ℝ)^((3:ℕ):ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 72),
          show ((3:ℕ):ℝ)*(1/3:ℝ) = 1 by norm_num, Real.rpow_one]] at h3
    have hMlt : ⌊(3.69*ξ)^(1/3:ℝ)⌋₊ < 72 := by
      have h1 := Nat.floor_le (by positivity : (0:ℝ) ≤ (3.69*ξ)^(1/3:ℝ))
      have h2 : ((⌊(3.69*ξ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) < 72 := by linarith
      exact_mod_cast h2
    omega
  exact Nat.mem_primesLE.mpr ⟨le_trans hfloor_le hM71, hp_prime⟩

/-- **Region II bound: `Margin.caK3 ε ≤ (4/100)·caU ξ`** for `ξ = caXi ε ∈ [3·10^4,10^5)`. -/
theorem caK3_upper_A (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 100000) :
    Work.RHContract.Margin.caK3 ε
      ≤ (4/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) := by
  set S : Finset ℕ := (Nat.primesLE ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊).filter
        (fun q : ℕ => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊) with hSdef
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ : (Work.RHPlan.caXi ε : ℝ) = ξ := hξdef.symm
  have hξ30000 : 30000 ≤ ξ := by rw [← hξ]; exact hlo
  have hξ1e5 : ξ < 100000 := by rw [← hξ]; exact hhi
  have hξ1 : 1 < ξ := by linarith
  have hξ0 : 0 < ξ := by linarith
  have hLpos : 0 < Real.log ξ := Real.log_pos hξ1
  set s : ℝ := Real.sqrt ξ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hξ0
  have hs2 : s^2 = ξ := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt hξ0)
  have hs173 : 173 ≤ s := by
    rw [hsdef]
    have h1 : (173:ℝ) ≤ Real.sqrt 30000 := by
      have h : (173:ℝ) ^ 2 ≤ 30000 := by norm_num
      calc (173:ℝ) = Real.sqrt ((173:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt 30000 := Real.sqrt_le_sqrt h
    exact le_trans h1 (Real.sqrt_le_sqrt hξ30000)
  have hcC : (24/25 : ℝ)/(ξ * Real.log ξ) ≤ Work.RHContract.Margin.caC ε :=
    caC_ge_regionII ε ξ hξ hε hξ30000 hξ1e5
  have hcaK3 : Work.RHContract.Margin.caK3 ε = ∑ p ∈ S,
      max 0 ((p:ℝ)^(-(((Work.RHContract.Margin.caExpFloor ε p : ℝ)+1))) /
                (((Work.RHContract.Margin.caExpFloor ε p : ℝ)+1) * (1 - 1/(p:ℝ)))
              - Work.RHContract.Margin.caC ε * Real.log (p:ℝ)) := by
    rw [Work.RHContract.Margin.caK3, hξ, ← hSdef]
  have hstep1 : Work.RHContract.Margin.caK3 ε ≤ ∑ p ∈ S,
      Real.log (p:ℝ)/(ξ * Real.log ξ) * (1/((p:ℝ)-1) + 1/25) := by
    rw [hcaK3]
    refine Finset.sum_le_sum ?_
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.two_le
    have hpow : ξ < (p:ℝ) ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by
      have hlog : Nat.log p (Work.RHPlan.caXi ε) = Work.RHContract.Margin.caExpFloor ε p := by
        rw [Work.RHContract.Margin.caExpFloor, Nat.floor_natCast]
      have h1 : 1 < p := by omega
      have h := Nat.lt_pow_succ_log_self h1 (Work.RHPlan.caXi ε)
      rw [hlog] at h
      have h3 : ((p ^ (Work.RHContract.Margin.caExpFloor ε p + 1) : ℕ) : ℝ)
          = (p:ℝ) ^ (Work.RHContract.Margin.caExpFloor ε p + 1) := by push_cast; ring
      have h2 : ξ < ((p ^ (Work.RHContract.Margin.caExpFloor ε p + 1) : ℕ) : ℝ) := by
        rw [← hξ]; exact_mod_cast h
      rwa [h3] at h2
    exact caK3_term_core hξ1 hp2 hpow hcC
  have hSsub : S ⊆ Nat.primesLE 71 := fun p hp => caK3_index_le_71 ε hε hlo hhi hp
  have hnn : ∀ p ∈ Nat.primesLE 71, 0 ≤ Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25) := by
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    have hp1 : (1:ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ 1/((p:ℝ)-1) + 1/25 := by
      have : 0 < (p:ℝ)-1 := by linarith
      positivity
    positivity
  have hstep2 : ∑ p ∈ S, Real.log (p:ℝ)/(ξ * Real.log ξ) * (1/((p:ℝ)-1) + 1/25)
      ≤ (1/(ξ * Real.log ξ)) * (4 + 71/25) := by
    have hA : ∑ p ∈ S, Real.log (p:ℝ)/(ξ * Real.log ξ) * (1/((p:ℝ)-1) + 1/25)
        = (1/(ξ * Real.log ξ)) * ∑ p ∈ S, Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
    have hB : ∑ p ∈ S, Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25)
        ≤ ∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun i hi _ => hnn i hi)
    have hC : ∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25) ≤ 4 + 71/25 := by
      have hsplit : ∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25)
          = (∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ)/((p:ℝ)-1))
            + (1/25) * (∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p hp; ring
      rw [hsplit]
      have h1 := sum_log_div_sub_one_le_71
      have h2 : (∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ)) ≤ 71 := by
        have := (Commons.NumberTheory.Chebyshev.theta_bracket_finite_range 71 (by norm_num)
          (by norm_num)).2
        rwa [Chebyshev.theta_eq_sum_primesLE_log] at this
      linarith
    calc ∑ p ∈ S, Real.log (p:ℝ)/(ξ * Real.log ξ) * (1/((p:ℝ)-1) + 1/25)
        = (1/(ξ * Real.log ξ)) * ∑ p ∈ S, Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25) := hA
      _ ≤ (1/(ξ * Real.log ξ)) * ∑ p ∈ Nat.primesLE 71, Real.log (p:ℝ) * (1/((p:ℝ)-1) + 1/25) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ (1/(ξ * Real.log ξ)) * (4 + 71/25) := mul_le_mul_of_nonneg_left hC (by positivity)
  have hstep3 : (1/(ξ * Real.log ξ)) * (4 + 71/25) ≤ (4/100) * (1/(s * Real.log ξ)) := by
    have h1 : (4 + 71/25 : ℝ) ≤ (4/100) * s := by
      have h2 : (4/100:ℝ)*173 ≤ (4/100)*s := mul_le_mul_of_nonneg_left hs173 (by norm_num)
      have h3 : (4 + 71/25 : ℝ) = 171/25 := by norm_num
      rw [h3]; linarith [h2]
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 1/(ξ * Real.log ξ) by positivity)
    have h3 : (1/(ξ * Real.log ξ)) * ((4/100) * s) = (4/100) * (1/(s * Real.log ξ)) := by
      have hsne : s ≠ 0 := ne_of_gt hs0
      have hls : Real.log s ≠ 0 := ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < s))
      rw [show ξ = s^2 from hs2.symm, Real.log_pow]
      field_simp
    linarith [h2, h3]
  have hU : Work.RHContract.A.RegionII.caU ξ = 1/(s * Real.log ξ) := by
    rw [Work.RHContract.A.RegionII.caU, ← hsdef]
  calc Work.RHContract.Margin.caK3 ε
      ≤ (1/(ξ * Real.log ξ)) * (4 + 71/25) := le_trans hstep1 hstep2
    _ ≤ (4/100) * (1/(s * Real.log ξ)) := hstep3
    _ = (4/100) * Work.RHContract.A.RegionII.caU ξ := by rw [hU]

end

end Work.RHContract.A.regionII

