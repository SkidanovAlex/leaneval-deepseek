import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.pD0_succ_mul_log_le
import Submission.Work.BW.mul_log_one_add_le
import Submission.Work.BW.exp_ratio_le
import Submission.Work.BW.ulcm_le_four_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Arithmetic bound for the `Θ`-term: `(D₀+1)·(3+log(2+16rd)) ≤ 0.2137·11.75·r·D`
with `D₀ = pD0 r d σ`, `D = pD r d σ`, under `σ_j ≥ 1/d`.

Write `A = (32rd)^{r+1}∏σ_j`; then `r·D = 2·A·log(2rd)`, `D₀ ≤ A` and `A ≥ 262144`. -/
theorem pD0_arith {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 ≤ (d : ℝ) * σ j) :
    ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r : ℝ) * (d : ℝ)))
      ≤ 0.2137 * (11.75 * (r : ℝ) * pD r d σ) := by
  have hR2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hRnn : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hσpos : ∀ j, 0 < σ j := by intro j; have h := hσ j; nlinarith [hdpos]
  have hPnn : 0 ≤ ∏ j, σ j := Finset.prod_nonneg (fun j _ => (hσpos j).le)
  have hLpos : 0 < Real.log (2 * (r:ℝ) * (d:ℝ)) := by
    apply Real.log_pos; nlinarith
  have hDnn : 0 ≤ pD r d σ := by
    unfold pD
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hRnn r))
      (pow_nonneg (by positivity) (r+1))) (le_of_lt hLpos)) hPnn
  set A : ℝ := (32 * (r:ℝ) * (d:ℝ))^(r+1) * ∏ j, σ j with hA
  have hApos : 0 < A := by
    rw [hA]
    exact mul_pos (pow_pos (by positivity) _) (Finset.prod_pos (fun j _ => hσpos j))
  have hrel : (r:ℝ) * pD r d σ = 2 * A * Real.log (2 * (r:ℝ) * (d:ℝ)) := by
    rw [hA]
    unfold pD
    have hpow : (32*(r:ℝ)*(d:ℝ))^(r+1) = (32*(d:ℝ))^(r+1) * (r:ℝ)^(r+1) := by
      rw [show (32*(r:ℝ)*(d:ℝ)) = (32*(d:ℝ))*(r:ℝ) by ring, mul_pow]
    rw [hpow, show (r:ℝ)^(r+1) = (r:ℝ)^r * (r:ℝ) from pow_succ _ _]
    ring
  have hpD0le : (pD0 r d σ : ℝ) ≤ A := by
    have h1 : (pD0 r d σ : ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2*(r:ℝ)*(d:ℝ))) := by
      unfold pD0
      exact Nat.floor_le (by apply div_nonneg (mul_nonneg hRnn hDnn); positivity)
    have h2 : (r:ℝ) * pD r d σ / (2 * Real.log (2*(r:ℝ)*(d:ℝ))) = A := by
      rw [hrel]
      rw [show 2 * A * Real.log (2*(r:ℝ)*(d:ℝ)) = A * (2 * Real.log (2*(r:ℝ)*(d:ℝ))) by ring]
      rw [mul_div_cancel_right₀ A (by positivity)]
    linarith [h1, h2]
  have hAge : (262144:ℝ) ≤ A := by
    rw [hA]
    have hPsig : (1/(d:ℝ))^r ≤ ∏ j, σ j := by
      have h1 : ∀ j ∈ (Finset.univ : Finset (Fin r)), (1/(d:ℝ)) ≤ σ j := by
        intro j _
        rw [div_le_iff₀ hdpos]
        nlinarith [hσ j]
      have := Finset.prod_le_prod₀ (fun j _ => by positivity) h1
      rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    have h1 : (32*(r:ℝ)*(d:ℝ))^(r+1) * (1/(d:ℝ))^r ≤ (32*(r:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j :=
      mul_le_mul_of_nonneg_left hPsig (pow_nonneg (by positivity) _)
    have hpow1 : (32*(r:ℝ)*(d:ℝ))^(r+1) = 32^(r+1) * (r:ℝ)^(r+1) * (d:ℝ)^(r+1) := by
      rw [show (32*(r:ℝ)*(d:ℝ)) = 32 * (r:ℝ) * (d:ℝ) from rfl, mul_pow, mul_pow]
    have hdv : (d:ℝ)^(r+1) * (1/(d:ℝ))^r = (d:ℝ) := by
      rw [one_div, inv_pow, ← div_eq_mul_inv, pow_succ']
      rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hdne)]
    have hval : (32*(r:ℝ)*(d:ℝ))^(r+1) * (1/(d:ℝ))^r = 32^(r+1) * (r:ℝ)^(r+1) * (d:ℝ) := by
      rw [hpow1,
        show 32^(r+1) * (r:ℝ)^(r+1) * (d:ℝ)^(r+1) * (1/(d:ℝ))^r
            = 32^(r+1) * (r:ℝ)^(r+1) * ((d:ℝ)^(r+1) * (1/(d:ℝ))^r) by ring, hdv]
    have h2 : (262144:ℝ) ≤ (32*(r:ℝ)*(d:ℝ))^(r+1) * (1/(d:ℝ))^r := by
      rw [hval]
      have e1 : (32:ℝ)^3 ≤ 32^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega : 3 ≤ r+1)
      have e2 : (2:ℝ)^3 ≤ (r:ℝ)^(r+1) := by
        have ha := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hR2 (r+1)
        have hb : (2:ℝ)^3 ≤ 2^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega : 3 ≤ r+1)
        linarith
      have h32 : (0:ℝ) < 32^(r+1) := pow_pos (by norm_num) _
      have hrr : (0:ℝ) < (r:ℝ)^(r+1) := pow_pos (by linarith) _
      have hm1 : (32:ℝ)^3 * 2^3 ≤ 32^(r+1) * (r:ℝ)^(r+1) :=
        mul_le_mul e1 e2 (by norm_num) (le_of_lt h32)
      have hm2 : (32:ℝ)^3 * 2^3 * 1 ≤ 32^(r+1) * (r:ℝ)^(r+1) * (d:ℝ) :=
        mul_le_mul hm1 hd1 (by norm_num) (mul_nonneg (le_of_lt h32) (le_of_lt hrr))
      linarith [hm2]
    linarith [h1, h2]
  have hlog_rhs : 3 + Real.log (2 + 16*(r:ℝ)*(d:ℝ)) ≤ Real.log (2*(r:ℝ)*(d:ℝ)) + 5.4069 := by
    have hlog2ge : (0.6931:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hrdpos : 0 < (r:ℝ)*(d:ℝ) := by positivity
    have hsplit : Real.log (2*(r:ℝ)*(d:ℝ)) = Real.log 2 + Real.log ((r:ℝ)*(d:ℝ)) := by
      rw [show (2*(r:ℝ)*(d:ℝ)) = 2 * ((r:ℝ)*(d:ℝ)) by ring,
          Real.log_mul (by norm_num) (ne_of_gt hrdpos)]
    have hle18 : Real.log (2 + 16*(r:ℝ)*(d:ℝ)) ≤ Real.log 18 + Real.log ((r:ℝ)*(d:ℝ)) := by
      have h : (2:ℝ) + 16*(r:ℝ)*(d:ℝ) ≤ 18 * ((r:ℝ)*(d:ℝ)) := by nlinarith [hR2, hd1, hrdpos]
      calc Real.log (2 + 16*(r:ℝ)*(d:ℝ)) ≤ Real.log (18 * ((r:ℝ)*(d:ℝ))) :=
            Real.log_le_log (by nlinarith [hR2, hd1]) h
        _ = Real.log 18 + Real.log ((r:ℝ)*(d:ℝ)) :=
            Real.log_mul (by norm_num) (ne_of_gt hrdpos)
    have hlog18 : Real.log 18 ≤ 3.1 := by
      have h3 : Real.log 3 ≤ Real.log 2 + 1/2 := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3/2 by norm_num)
        rw [Real.log_div (by norm_num) (by norm_num)] at h
        linarith
      have h18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
        rw [show (18:ℝ) = 2 * 3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
            Real.log_pow]
        ring
      have h2 := Real.log_two_lt_d9
      rw [h18]; linarith
    linarith [hle18, hlog18, hsplit]
  have hLbig : (1.3862943:ℝ) ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := by
    have h4 : (1.3862943:ℝ) ≤ Real.log 4 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; linarith [Real.log_two_gt_d9]
    refine le_trans h4 ?_
    apply Real.log_le_log (by norm_num)
    nlinarith [hR2, hd1]
  have hstep3 : (1 + 1/262144) * A * (3 + Real.log (2 + 16*(r:ℝ)*(d:ℝ)))
      ≤ 0.2137 * (11.75 * (r:ℝ) * pD r d σ) := by
    have hc : (1 + (1:ℝ)/262144) * (Real.log (2*(r:ℝ)*(d:ℝ)) + 5.4069)
        ≤ 5.02195 * Real.log (2*(r:ℝ)*(d:ℝ)) := by nlinarith [hLbig]
    calc (1 + 1/262144) * A * (3 + Real.log (2 + 16*(r:ℝ)*(d:ℝ)))
        ≤ (1 + 1/262144) * A * (Real.log (2*(r:ℝ)*(d:ℝ)) + 5.4069) :=
          mul_le_mul_of_nonneg_left hlog_rhs (by positivity)
      _ = A * ((1 + 1/262144) * (Real.log (2*(r:ℝ)*(d:ℝ)) + 5.4069)) := by ring
      _ ≤ A * (5.02195 * Real.log (2*(r:ℝ)*(d:ℝ))) :=
          mul_le_mul_of_nonneg_left hc (le_of_lt hApos)
      _ = 0.2137 * (11.75 * (r:ℝ) * pD r d σ) := by
          rw [show (11.75 * (r:ℝ) * pD r d σ) = 11.75 * ((r:ℝ) * pD r d σ) by ring, hrel]
          ring
  have hfinal : ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16*(r:ℝ)*(d:ℝ)))
      ≤ (1 + 1/262144) * A * (3 + Real.log (2 + 16*(r:ℝ)*(d:ℝ))) := by
    have hY : (0:ℝ) ≤ 3 + Real.log (2 + 16*(r:ℝ)*(d:ℝ)) := by
      have := Real.log_nonneg (show (1:ℝ) ≤ 2 + 16*(r:ℝ)*(d:ℝ) by nlinarith [hR2, hd1])
      linarith
    apply mul_le_mul_of_nonneg_right _ hY
    have hAinv : 1/A ≤ 1/262144 := one_div_le_one_div_of_le (by norm_num) hAge
    calc (pD0 r d σ : ℝ) + 1 ≤ A + 1 := by linarith [hpD0le]
      _ = A * (1 + 1/A) := by rw [mul_add, mul_one, mul_one_div, div_self (ne_of_gt hApos)]
      _ ≤ A * (1 + 1/262144) :=
          mul_le_mul_of_nonneg_left (by linarith [hAinv]) (le_of_lt hApos)
      _ = (1 + 1/262144) * A := by ring
  exact le_trans hfinal hstep3

/-- Arithmetic core of the row-height bound: the logarithm of the explicit bound `M` for
`|coefRat|` is at most `1.7·h·(11.75 r D)`. Here `G0` bounds `|γ_m|`, `t0 + ∑t ≤ T`. -/
theorem sysRow_arith {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h)
    (σ : Fin r → ℝ) (hσ : ∀ j, 1 ≤ (d : ℝ) * σ j)
    (G0 : ℝ) (hG0 : 0 ≤ G0) (hG0le : G0 ≤ 2 * Real.exp ((h : ℝ) + 1) * pD r d σ)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (hsum : t0 + ∑ m, t m ≤ pT r d σ) :
    (∑ m, (t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ))))
      + (t0 : ℝ) * Real.log (ulcm h : ℝ)
      + (h : ℝ) * ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r : ℝ) * (d : ℝ)))
      ≤ 1.7 * (h : ℝ) * (11.75 * (r : ℝ) * pD r d σ) := by
  have hRnn : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
  have hR2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hHnn : (0:ℝ) ≤ (h:ℝ) := Nat.cast_nonneg h
  have hH19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hσpos : ∀ j, 0 < σ j := by
    intro j; have h := hσ j; nlinarith [hdpos]
  have hprod : 0 ≤ ∏ j, σ j := Finset.prod_nonneg (fun j _ => (hσpos j).le)
  have hlogpos : 0 ≤ Real.log (2 * (r:ℝ) * (d:ℝ)) := by
    apply Real.log_nonneg; nlinarith [hR2, hd1]
  have hDnn : 0 ≤ pD r d σ := by
    unfold pD
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hRnn r))
      (pow_nonneg (by positivity) (r+1))) hlogpos) hprod
  have hTnn : 0 ≤ 11.75 * (r:ℝ) * pD r d σ :=
    mul_nonneg (mul_nonneg (by norm_num) hRnn) hDnn
  have hpT : ((pT r d σ : ℕ):ℝ) ≤ 11.75 * (r:ℝ) * pD r d σ := by
    unfold pT
    exact Nat.floor_le hTnn
  have hsumR : (t0:ℝ) + ∑ m, (t m : ℝ) ≤ 11.75 * (r:ℝ) * pD r d σ := by
    have h1 : (t0:ℝ) + ∑ m, (t m : ℝ) ≤ (pT r d σ : ℝ) := by exact_mod_cast hsum
    linarith [h1, hpT]
  have hSnn : (0:ℝ) ≤ ∑ m, (t m : ℝ) := by positivity
  -- Term 1
  have hGexp : G0 * Real.exp (1 - (h:ℝ)) ≤ 15 * pD r d σ := by
    have hexpnn : (0:ℝ) ≤ Real.exp (1 - (h:ℝ)) := (Real.exp_pos _).le
    have h1 : G0 * Real.exp (1 - (h:ℝ)) ≤ (2 * Real.exp ((h:ℝ) + 1) * pD r d σ) * Real.exp (1 - (h:ℝ)) :=
      mul_le_mul_of_nonneg_right hG0le hexpnn
    have hexp2 : Real.exp ((h:ℝ) + 1) * Real.exp (1 - (h:ℝ)) = Real.exp 2 := by
      rw [← Real.exp_add]; congr 1; ring
    have h2e : 2 * Real.exp 2 ≤ 15 := by
      have h1e := Real.exp_one_lt_d9
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      rw [he2]; nlinarith [Real.exp_pos 1, h1e]
    calc G0 * Real.exp (1 - (h:ℝ))
        ≤ (2 * Real.exp ((h:ℝ) + 1) * pD r d σ) * Real.exp (1 - (h:ℝ)) := h1
      _ = 2 * pD r d σ * (Real.exp ((h:ℝ) + 1) * Real.exp (1 - (h:ℝ))) := by ring
      _ = 2 * pD r d σ * Real.exp 2 := by rw [hexp2]
      _ ≤ 15 * pD r d σ := by
          have := mul_le_mul_of_nonneg_right h2e hDnn
          nlinarith [this]
  have hB1 : (∑ m, (t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ))))
      ≤ (h:ℝ) * (∑ m, (t m : ℝ)) + 15 * (r:ℝ) * pD r d σ := by
    have hstep : (∑ m, (t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ))))
        ≤ ∑ m, ((t m : ℝ) * (h:ℝ) + G0 * Real.exp (1 - (h:ℝ))) := by
      apply Finset.sum_le_sum
      intro m _
      exact mul_log_one_add_le hG0 (by linarith [hH19]) (Nat.cast_nonneg _)
    have hsplit : (∑ m, ((t m : ℝ) * (h:ℝ) + G0 * Real.exp (1 - (h:ℝ))))
        = (h:ℝ) * (∑ m, (t m : ℝ)) + ((r - 1 : ℕ) : ℝ) * (G0 * Real.exp (1 - (h:ℝ))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.sum_mul]; ring
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
    rw [hsplit] at hstep
    refine le_trans hstep ?_
    have hrm1 : ((r - 1 : ℕ) : ℝ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r 1
    have hmul := mul_le_mul hrm1 hGexp (mul_nonneg hG0 (Real.exp_pos _).le) hRnn
    nlinarith [hmul]
  -- Term 2
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [h4]; linarith
  have hulcm : Real.log (ulcm h : ℝ) ≤ (h:ℝ) * 1.3863 := by
    have hpos : 0 < (ulcm h : ℝ) := by exact_mod_cast ulcm_pos h
    have hle : (ulcm h : ℝ) ≤ 4^h := ulcm_le_four_pow h
    calc Real.log (ulcm h : ℝ) ≤ Real.log (4^h : ℝ) := Real.log_le_log hpos hle
      _ = (h:ℝ) * Real.log 4 := by rw [Real.log_pow]
      _ ≤ (h:ℝ) * 1.3863 := mul_le_mul_of_nonneg_left hlog4 hHnn
  have hB2 : (t0:ℝ) * Real.log (ulcm h : ℝ) ≤ 1.3863 * (h:ℝ) * (t0:ℝ) := by
    have := mul_le_mul_of_nonneg_left hulcm (Nat.cast_nonneg t0)
    nlinarith [this]
  -- Term 3
  have hB3 : (h:ℝ) * ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r:ℝ) * (d:ℝ)))
      ≤ 0.2137 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ)) := by
    have hpD0 := pD0_arith hr hd σ hσ
    calc (h:ℝ) * ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r:ℝ) * (d:ℝ)))
        = (h:ℝ) * (((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r:ℝ) * (d:ℝ)))) := by ring
      _ ≤ (h:ℝ) * (0.2137 * (11.75 * (r:ℝ) * pD r d σ)) := mul_le_mul_of_nonneg_left hpD0 hHnn
      _ = 0.2137 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ)) := by ring
  -- final assembly
  have hkey : (h:ℝ) * (∑ m, (t m : ℝ)) + 1.3863 * (h:ℝ) * (t0:ℝ)
      ≤ 1.3863 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ)) := by
    have ht0leT : (t0:ℝ) ≤ 11.75 * (r:ℝ) * pD r d σ := by linarith [hsumR, hSnn]
    have hS1 : (∑ m, (t m : ℝ)) + 1.3863 * (t0:ℝ) ≤ 1.3863 * (11.75 * (r:ℝ) * pD r d σ) := by
      nlinarith [hsumR, ht0leT]
    nlinarith [hS1, hHnn]
  have h10 : 15 * (r:ℝ) * pD r d σ ≤ 0.1 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ)) := by
    have hA : (0:ℝ) ≤ 1.175 * (h:ℝ) - 15 := by nlinarith [hH19]
    have hB : (0:ℝ) ≤ (r:ℝ) * pD r d σ := mul_nonneg hRnn hDnn
    have hm := mul_nonneg hA hB
    nlinarith [hm]
  have hfin : (∑ m, (t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ))))
        + (t0 : ℝ) * Real.log (ulcm h : ℝ)
        + (h : ℝ) * ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r : ℝ) * (d : ℝ)))
      ≤ 1.3863 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ))
        + 0.2137 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ))
        + 0.1 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ)) := by
    linarith [hB1, hB2, hB3, hkey, h10]
  calc (∑ m, (t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ))))
        + (t0 : ℝ) * Real.log (ulcm h : ℝ)
        + (h : ℝ) * ((pD0 r d σ : ℝ) + 1) * (3 + Real.log (2 + 16 * (r : ℝ) * (d : ℝ)))
      ≤ 1.3863 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ))
        + 0.2137 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ))
        + 0.1 * ((h:ℝ) * (11.75 * (r:ℝ) * pD r d σ)) := hfin
    _ = 1.7 * (h:ℝ) * (11.75 * (r:ℝ) * pD r d σ) := by ring

end Work.BW
