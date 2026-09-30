import Mathlib
import Submission.Work.BW.split_aux
import Submission.Work.BW.split_E23_aux
import Submission.Work.BW.split_E23_facE2
import Submission.Work.BW.split_E23_facE3
import Submission.Work.BW.split_E23_two_pxi_ge
import Submission.Work.BW.split_E23_pow115
import Submission.Work.BW.split_E23_Ddiv
import Submission.Work.BW.split_E23_zpow1
import Submission.Work.BW.split_E23_zpow2
import Submission.Work.BW.split_E23_log2rd
import Submission.Work.BW.split_E23_numE2
import Submission.Work.BW.split_E23_numE3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! The two "big" conjuncts of `split_conditions` (E2/E3 of `multiplicity_prop`). -/

set_option maxHeartbeats 2000000

namespace Work.BW

open Finset

/-- `0 < (pxi r)^n` for an integer exponent `n`. -/
lemma zpow_pxi_pos {r : ℕ} (hr : 2 ≤ r) (n : ℤ) : (0:ℝ) < (pxi r) ^ n :=
  zpow_pos (pxi_pos hr) n

lemma zpow_pxi_nonneg {r : ℕ} (n : ℤ) : (0:ℝ) ≤ (pxi r) ^ n :=
  zpow_nonneg (pxi_nonneg r) n

lemma pxi_pow_nonneg (r n : ℕ) : (0:ℝ) ≤ (pxi r)^n := pow_nonneg (pxi_nonneg r) n

lemma two_pxi_pred_nonneg {r : ℕ} : (0:ℝ) ≤ 2 * (pxi r)^(r-1) :=
  mul_nonneg (by norm_num) (pxi_pow_nonneg r (r-1))

lemma two_pxi_pred2_nonneg {r : ℕ} : (0:ℝ) ≤ 2 * (pxi r)^(r-2) :=
  mul_nonneg (by norm_num) (pxi_pow_nonneg r (r-2))

/-! ### Exponent bookkeeping -/

lemma exp6r6 (r : ℕ) : 6*r+6 = 5*r+6+r := by ring

lemma exp6r5 {r : ℕ} (hr : 2 ≤ r) : 6*r+5 = 5*r+6+(r-1) := by omega

lemma two_pow_six_r_six (r : ℕ) : (2:ℝ)^(6*r+6) = (2:ℝ)^(5*r+6) * (2:ℝ)^r := by
  rw [exp6r6 r, pow_add]

lemma two_pow_six_r_five {r : ℕ} (hr : 2 ≤ r) :
    (2:ℝ)^(6*r+5) = (2:ℝ)^(5*r+6) * (2:ℝ)^(r-1) := by
  rw [exp6r5 hr, pow_add]

/-- `11 · r · D / (2 r) = 11 D / 2`. -/
lemma eleven_rD_div_two_r {r : ℕ} (hr : 2 ≤ r) (D : ℝ) :
    (11:ℝ)*(r:ℝ)*D/(2*(r:ℝ)) = 11*D/2 := by
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  rw [div_eq_div_iff (by positivity) (by norm_num : (2:ℝ) ≠ 0)]
  ring

/-- `∏_j ⌊D/(r d σ_j)⌋ ≤ D^r / (r^r d^r ∏σ)`. -/
lemma prod_pDj_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d:ℝ) ≤ σ j) :
    ∏ j : Fin r, (pDj r d σ j : ℝ)
      ≤ (pD r d σ)^r / ((r:ℝ)^r * (d:ℝ)^r * ∏ j, σ j) := by
  have hprod : (∏ j : Fin r, ((r:ℝ)*(d:ℝ)*σ j)) = ((r:ℝ)*(d:ℝ))^r * ∏ j, σ j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ∏ j : Fin r, (pDj r d σ j : ℝ)
      ≤ ∏ j : Fin r, (pD r d σ / ((r:ℝ)*(d:ℝ)*σ j)) := by
    have h := prod_le_prod_of_nonneg (s := (Finset.univ : Finset (Fin r)))
        (f := fun j => (pDj r d σ j : ℝ)) (g := fun j => pD r d σ / ((r:ℝ)*(d:ℝ)*σ j))
        (fun j _ => by positivity) (fun j _ => pDj_le hr hd σ hσ j)
    simpa using h
  have h2 : ∏ j : Fin r, (pD r d σ / ((r:ℝ)*(d:ℝ)*σ j))
      = (pD r d σ)^r / ((r:ℝ)^r * (d:ℝ)^r * ∏ j, σ j) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hprod, mul_pow]
  exact le_of_le_of_eq h1 h2

/-- The `E2` exclusion inequality (with the floors in place of `halfSplit`). -/
lemma E2_ineq {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d : ℝ) ≤ σ j) :
    ((r + 1).factorial : ℝ) * ∏ i, calD r d h σ i <
      ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℝ) + 1) *
        ((⌊calT r d σ / (2*(r:ℝ))⌋₊ + r).choose r : ℝ) := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : 1 ≤ r := by omega
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hhpos : (0:ℝ) < (h:ℝ) := by exact_mod_cast (by omega : 0 < h)
  have hσpos : ∀ j, 0 < σ j := by
    intro j
    have h1 : (0:ℝ) < 1/(d:ℝ) := by positivity
    linarith [hσ j]
  have hPpos : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => hσpos j)
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hLpos : 0 < Real.log (2*(r:ℝ)*d) := log_2rd_pos hr hd
  -- the product identity
  have hprod0 : ∏ i : Fin (r+1), calD r d h σ i
      = (h:ℝ) * ((pD0 r d σ : ℝ) + 1)
        * ∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d)) := by
    have hsucc : ∏ i : Fin r, calD r d h σ i.succ
        = ∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d)) :=
      Finset.prod_congr rfl (fun j _ => calD_succ r d h σ j)
    calc ∏ i : Fin (r+1), calD r d h σ i
        = calD r d h σ 0 * ∏ i : Fin r, calD r d h σ i.succ :=
          Fin.prod_univ_succ (calD r d h σ)
      _ = (h:ℝ) * ((pD0 r d σ : ℝ) + 1) * ∏ i : Fin r, calD r d h σ i.succ := by
          rw [calD_zero]
      _ = (h:ℝ) * ((pD0 r d σ : ℝ) + 1)
            * ∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d)) := by rw [hsucc]
  -- `D₀ + 1 ≤ r D / log (2 r d)`
  have hD0b : (pD0 r d σ : ℝ) + 1 ≤ (r:ℝ) * pD r d σ / Real.log (2*(r:ℝ)*d) := by
    have h2L : (0:ℝ) < 2 * Real.log (2*(r:ℝ)*d) := by linarith
    have h1 : (pD0 r d σ : ℝ) ≤ (r:ℝ) * pD r d σ / (2 * Real.log (2*(r:ℝ)*d)) :=
      Nat.floor_le (by positivity)
    have hone : (1:ℝ) ≤ (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ) := by
      have a1 : (1:ℝ) ≤ (r:ℝ)^(r+1) := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ r))
      have a2 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
      have a3 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      calc (1:ℝ) = 1*1*1 := by norm_num
        _ ≤ (r:ℝ)^(r+1) * (32:ℝ)^(r+1) * (d:ℝ) :=
            mul_le_mul (mul_le_mul a1 a2 (by norm_num) (by positivity)) a3
              (by norm_num) (by positivity)
    have hDl := pD_low hr hd σ hσ
    have h3 : 2*Real.log (2*(r:ℝ)*d) * ((r:ℝ)^(r+1)*(32:ℝ)^(r+1)*(d:ℝ))
        = (r:ℝ)*(2*(r:ℝ)^r*(32:ℝ)^(r+1)*(d:ℝ)*Real.log (2*(r:ℝ)*d)) := by
      rw [show (r:ℝ)^(r+1) = (r:ℝ)^r * (r:ℝ) by rw [pow_succ]]
      ring
    have h4 : (2:ℝ)*Real.log (2*(r:ℝ)*d) ≤ (r:ℝ) * pD r d σ := by
      calc (2:ℝ)*Real.log (2*(r:ℝ)*d) = 2*Real.log (2*(r:ℝ)*d) * 1 := by ring
        _ ≤ 2*Real.log (2*(r:ℝ)*d) * ((r:ℝ)^(r+1)*(32:ℝ)^(r+1)*(d:ℝ)) :=
            mul_le_mul_of_nonneg_left hone (by positivity)
        _ = (r:ℝ)*(2*(r:ℝ)^r*(32:ℝ)^(r+1)*(d:ℝ)*Real.log (2*(r:ℝ)*d)) := h3
        _ ≤ (r:ℝ)*pD r d σ := mul_le_mul_of_nonneg_left hDl (le_of_lt hrpos)
    have h2 : (1:ℝ) ≤ (r:ℝ)*pD r d σ/(2*Real.log (2*(r:ℝ)*d)) := by
      rw [le_div_iff₀ h2L]
      linarith
    have h5 : (pD0 r d σ : ℝ) + 1
        ≤ (r:ℝ)*pD r d σ/(2*Real.log (2*(r:ℝ)*d))
          + (r:ℝ)*pD r d σ/(2*Real.log (2*(r:ℝ)*d)) := by linarith
    have he : (r:ℝ)*pD r d σ/(2*Real.log (2*(r:ℝ)*d))
        + (r:ℝ)*pD r d σ/(2*Real.log (2*(r:ℝ)*d))
        = (r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d) := by
      have h : (r:ℝ)*pD r d σ/(2*Real.log (2*(r:ℝ)*d))
          + (r:ℝ)*pD r d σ/(2*Real.log (2*(r:ℝ)*d))
          = (2*((r:ℝ)*pD r d σ))/(2*Real.log (2*(r:ℝ)*d)) := by ring
      rw [h]
      rw [div_eq_div_iff (by positivity) (ne_of_gt hLpos)]
      ring
    linarith
  -- the `pD`-product bound and the `D`-division identity
  have hprodb := prod_pDj_le hr hd σ hσ
  have hkey := split_E23_Ddiv hr1 hd σ hPpos
  have hDr : (pD r d σ)^r = (pD r d σ)^(r-1) * pD r d σ := by
    rw [← pow_succ (pD r d σ) (r-1), Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hDr' : (pD r d σ)^r = pD r d σ * (pD r d σ)^(r-1) := by rw [hDr, mul_comm]
  have hDr2 : (pD r d σ)^r / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j))
      = (pD r d σ)^(r-1) * (Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ))) := by
    rw [hDr]
    rw [show (pD r d σ)^(r-1) * pD r d σ / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j))
          = (pD r d σ)^(r-1) * (pD r d σ / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j))) by ring]
    rw [hkey]
  -- the product of the `𝒟_j` as a product of quotients
  have hprodform2 : ∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d))
      ≤ (pD r d σ)^r / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j)) / (2:ℝ)^(pI r d * r) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    exact div_le_div_of_nonneg_right hprodb (by positivity)
  -- `(r+1)! ∏ 𝒟_i ≤ X₂`
  have hA2 : ((r+1).factorial : ℝ) * ∏ i : Fin (r+1), calD r d h σ i
      ≤ ((r+1).factorial : ℝ) * (h:ℝ) * (r:ℝ) * (2:ℝ)^(5*r+6) * (d:ℝ) * (pD r d σ)^r
        / (2:ℝ)^((pI r d) * r) := by
    rw [hprod0]
    have hstep : (h:ℝ) * ((pD0 r d σ : ℝ) + 1)
          * (∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d)))
        ≤ (h:ℝ) * ((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d))
          * ((pD r d σ)^r / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j)) / (2:ℝ)^(pI r d * r)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hD0b (le_of_lt hhpos)
      · exact hprodform2
      · positivity
      · positivity
    have hnum : (h:ℝ) * ((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d))
          * ((pD r d σ)^(r-1) * (Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ))))
        = (h:ℝ) * (r:ℝ) * ((2:ℝ)^(5*r+6)*(d:ℝ)) * (pD r d σ)^r := by
      calc (h:ℝ) * ((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d))
            * ((pD r d σ)^(r-1) * (Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ))))
          = (h:ℝ) * (((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d))
              * (Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ)))) * (pD r d σ)^(r-1) := by ring
        _ = (h:ℝ) * (((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d)
              * Real.log (2*(r:ℝ)*d)) * ((2:ℝ)^(5*r+6)*(d:ℝ))) * (pD r d σ)^(r-1) := by ring
        _ = (h:ℝ) * ((r:ℝ)*pD r d σ * ((2:ℝ)^(5*r+6)*(d:ℝ))) * (pD r d σ)^(r-1) := by
              rw [div_mul_cancel₀ ((r:ℝ)*pD r d σ) (ne_of_gt hLpos)]
        _ = (h:ℝ) * (r:ℝ) * ((2:ℝ)^(5*r+6)*(d:ℝ)) * (pD r d σ)^r := by
              rw [show (h:ℝ) * ((r:ℝ)*pD r d σ * ((2:ℝ)^(5*r+6)*(d:ℝ))) * (pD r d σ)^(r-1)
                    = (h:ℝ) * (r:ℝ) * ((2:ℝ)^(5*r+6)*(d:ℝ))
                      * (pD r d σ * (pD r d σ)^(r-1)) by ring,
                  ← hDr']
    calc ((r+1).factorial : ℝ) * ((h:ℝ) * ((pD0 r d σ : ℝ) + 1)
            * (∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d))))
        ≤ ((r+1).factorial : ℝ) * ((h:ℝ) * ((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d))
            * ((pD r d σ)^r / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j)) / (2:ℝ)^(pI r d * r))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = ((r+1).factorial : ℝ) * (h:ℝ) * (r:ℝ) * (2:ℝ)^(5*r+6) * (d:ℝ) * (pD r d σ)^r
            / (2:ℝ)^((pI r d) * r) := by
          rw [hDr2]
          rw [show ((r+1).factorial : ℝ) * ((h:ℝ) * ((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d))
                * ((pD r d σ)^(r-1) * (Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ)))
                    / (2:ℝ)^(pI r d * r)))
              = (((r+1).factorial : ℝ) * ((h:ℝ) * ((r:ℝ)*pD r d σ/Real.log (2*(r:ℝ)*d))
                  * ((pD r d σ)^(r-1) * (Real.log (2*(r:ℝ)*d)
                      * ((2:ℝ)^(5*r+6)*(d:ℝ))))))
                / (2:ℝ)^(pI r d * r) by ring]
          congr 1
          rw [hnum]
          ring
  -- the numerical star condition
  have hstar2 : ((r+1).factorial : ℝ) * (r.factorial : ℝ) * (r:ℝ) * (2:ℝ)^(6*r+6)
      < (2:ℝ)^4 * (11:ℝ)^r *
          ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^(r * (r * pI r d + 1))
            * (2:ℝ)^(r * pI r d)) := by
    have hpow : (2*(r:ℝ)*d)^(6*r) ≤ (2 * (pxi r)^(r-1))^(r * pI r d) := by
      have h115 : (2*(r:ℝ)*d)^6 ≤ (1.15:ℝ)^(pI r d) := split_E23_pow115 hr hd
      have h2ξ : (1.15:ℝ) ≤ 2 * (pxi r)^(r-1) := split_E23_two_pxi_ge hr
      calc (2*(r:ℝ)*d)^(6*r) = ((2*(r:ℝ)*d)^6)^r := by rw [← pow_mul]
        _ ≤ ((1.15:ℝ)^(pI r d))^r := pow_le_pow_left₀ (by positivity) h115 r
        _ = (1.15:ℝ)^(r * pI r d) := by rw [← pow_mul, Nat.mul_comm (pI r d) r]
        _ ≤ (2 * (pxi r)^(r-1))^(r * pI r d) := pow_le_pow_left₀ (by norm_num) h2ξ _
    have hgle : (2*(r:ℝ)*d)^(6*r) ≤ 2 * ((pxi r)^r * (2 * (pxi r)^(r-1))^(r * pI r d)) := by
      have h2ξr : (1:ℝ) ≤ 2*(pxi r)^r := one_le_two_mul_pxi_pow hr
      have hBnn : (0:ℝ) ≤ (2 * (pxi r)^(r-1))^(r * pI r d) :=
        pow_nonneg two_pxi_pred_nonneg _
      calc (2*(r:ℝ)*d)^(6*r) ≤ (2 * (pxi r)^(r-1))^(r * pI r d) := hpow
        _ ≤ (2 * (pxi r)^(r-1))^(r * pI r d) * (2 * (pxi r)^r) :=
            le_mul_of_one_le_right hBnn h2ξr
        _ = 2 * ((pxi r)^r * (2 * (pxi r)^(r-1))^(r * pI r d)) := by ring
    have hfin : (2:ℝ)^3 * (11:ℝ)^r * (2*(r:ℝ)*d)^(6*r)
        ≤ (2:ℝ)^4 * (11:ℝ)^r *
          ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^(r * (r * pI r d + 1))
            * (2:ℝ)^(r * pI r d)) := by
      rw [split_E23_zpow1 hr]
      calc (2:ℝ)^3 * (11:ℝ)^r * (2*(r:ℝ)*d)^(6*r)
          ≤ (2:ℝ)^3 * (11:ℝ)^r
              * (2 * ((pxi r)^r * (2 * (pxi r)^(r-1))^(r * pI r d))) :=
            mul_le_mul_of_nonneg_left hgle (by positivity)
        _ = (2:ℝ)^4 * (11:ℝ)^r
              * ((pxi r)^r * (2 * (pxi r)^(r-1))^(r * pI r d)) := by ring
    have hnum := split_E23_numE2 hr hd
    have hfac := split_E23_facE2 r hr
    linarith [hfac, hnum, hfin]
  -- the comparison
  have hcmp2 : ((r+1).factorial : ℝ) * (h:ℝ) * (r:ℝ) * (2:ℝ)^(5*r+6) * (d:ℝ) * (pD r d σ)^r
        / (2:ℝ)^((pI r d) * r)
      < (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
        * (((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^r
            / (r.factorial:ℝ)) := by
    have hrf : (0:ℝ) < (r.factorial : ℝ) := by exact_mod_cast r.factorial_pos
    have hq : (0:ℝ) < (h:ℝ)*(d:ℝ)*(pD r d σ)^r
        / ((2:ℝ)^(r*pI r d + r) * (r.factorial:ℝ)) := by positivity
    have hlt := mul_lt_mul_of_pos_right hstar2 hq
    have e1 : ((r+1).factorial : ℝ) * (h:ℝ) * (r:ℝ) * (2:ℝ)^(5*r+6) * (d:ℝ)
          * (pD r d σ)^r / (2:ℝ)^((pI r d)*r)
        = (((r+1).factorial : ℝ) * (r.factorial:ℝ) * (r:ℝ) * (2:ℝ)^(6*r+6))
          * ((h:ℝ)*(d:ℝ)*(pD r d σ)^r
              / ((2:ℝ)^(r*pI r d + r) * (r.factorial:ℝ))) := by
      rw [two_pow_six_r_six r,
        show (2:ℝ)^(r*pI r d + r) = (2:ℝ)^(r*pI r d) * (2:ℝ)^r by rw [pow_add],
        show (2:ℝ)^((pI r d)*r) = (2:ℝ)^(r*pI r d) by rw [Nat.mul_comm (pI r d) r]]
      field_simp <;> ring
    have e2 : (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
          * (((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^r
              / (r.factorial:ℝ))
        = ((2:ℝ)^4 * (11:ℝ)^r *
            ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^(r * (r * pI r d + 1))
              * (2:ℝ)^(r * pI r d)))
          * ((h:ℝ)*(d:ℝ)*(pD r d σ)^r
              / ((2:ℝ)^(r*pI r d + r) * (r.factorial:ℝ))) := by
      rw [mul_pow]
      rw [show ((pxi r)^(r*pI r d + 1))^r = (pxi r)^(r * (r*pI r d + 1)) by
            rw [← pow_mul, Nat.mul_comm (r*pI r d + 1) r],
        show (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))^r = (11:ℝ)^r * (pD r d σ)^r / (2:ℝ)^r by
          rw [eleven_rD_div_two_r hr (pD r d σ), div_pow, mul_pow],
        show (16:ℝ) = (2:ℝ)^4 by norm_num,
        show (2:ℝ)^(r*pI r d + r) = (2:ℝ)^(r*pI r d) * (2:ℝ)^r by rw [pow_add]]
      field_simp <;> ring
    rw [← e1, ← e2] at hlt
    exact hlt
  -- the lower bound `LB₂`
  have hbase_nn : (0:ℝ) ≤ (pxi r)^(r*pI r d + 1)
      * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))) :=
    mul_nonneg (pow_nonneg (pxi_nonneg r) _) (by positivity)
  have hTmain : (pxi r)^(r * pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))
      ≤ calT r d σ / (2*(r:ℝ)) := by
    rw [calT_eq]
    rw [show pxi r * (pxi r)^(r*pI r d) * (pT r d σ : ℝ) / (2*(r:ℝ))
          = ((pxi r)^(r*pI r d + 1) * (pT r d σ : ℝ)) / (2*(r:ℝ)) by
        rw [show pxi r * (pxi r)^(r*pI r d) = (pxi r)^(r*pI r d + 1) by
              rw [mul_comm (pxi r) ((pxi r)^(r*pI r d)), ← pow_succ]]]
    rw [show (pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))
          = ((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)))/(2*(r:ℝ)) by ring]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pT_ge hr hd σ hσ) (pow_nonneg (pxi_nonneg r) _))
      (by positivity)
  have hCbound : ((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^r
        / (r.factorial : ℝ)
      ≤ ((⌊calT r d σ/(2*(r:ℝ))⌋₊ + r).choose r : ℝ) := by
    have h1 : (pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))
        ≤ ((⌊calT r d σ/(2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1 :=
      le_trans hTmain (le_of_lt (Nat.lt_floor_add_one _))
    calc ((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^r
          / (r.factorial : ℝ)
        ≤ (((⌊calT r d σ/(2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1)^r / (r.factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hbase_nn h1 r) (by positivity)
      _ ≤ ((⌊calT r d σ/(2*(r:ℝ))⌋₊ + r).choose r : ℝ) := by
          simpa using choose_lower (⌊calT r d σ/(2*(r:ℝ))⌋₊) r
  have hLB2 : (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
        * (((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^r
            / (r.factorial : ℝ))
      ≤ ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℝ) + 1)
        * ((⌊calT r d σ / (2*(r:ℝ))⌋₊ + r).choose r : ℝ) := by
    have hSmain := calS_div_two_r (r := r) (d := d) (h := h) hr0
    have h1 : (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
        ≤ ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1 := by
      rw [← hSmain]
      exact le_of_lt (Nat.lt_floor_add_one _)
    have h4 : (0:ℝ) ≤ ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1 := by positivity
    have hc : (0:ℝ) ≤ ((pxi r)^(r*pI r d + 1)
        * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^r / (r.factorial : ℝ) :=
      div_nonneg (pow_nonneg hbase_nn _) (by positivity)
    exact mul_le_mul h1 hCbound hc h4
  exact lt_of_le_of_lt hA2 (lt_of_lt_of_le hcmp2 hLB2)

/-- The `E3` exclusion inequality (with the floors in place of `halfSplit`). -/
lemma E3_ineq {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d : ℝ) ≤ σ j) :
    ((r + 1).factorial : ℝ) * ∏ i : Fin r, calD r d h σ i.succ <
      ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℝ) + 1) *
        ((⌊calT r d σ / (2*(r:ℝ))⌋₊ + (r - 1)).choose (r - 1) : ℝ) := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : 1 ≤ r := by omega
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hhpos : (0:ℝ) < (h:ℝ) := by exact_mod_cast (by omega : 0 < h)
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hσpos : ∀ j, 0 < σ j := by
    intro j
    have h1 : (0:ℝ) < 1/(d:ℝ) := by positivity
    linarith [hσ j]
  have hPpos : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => hσpos j)
  have hDpos : 0 < pD r d σ := pD_pos hr hd σ hσ
  have hLpos : 0 < Real.log (2*(r:ℝ)*d) := log_2rd_pos hr hd
  have hprodb := prod_pDj_le hr hd σ hσ
  have hkey := split_E23_Ddiv hr1 hd σ hPpos
  have hDr : (pD r d σ)^r = (pD r d σ)^(r-1) * pD r d σ := by
    rw [← pow_succ (pD r d σ) (r-1), Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hDr2 : (pD r d σ)^r / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j))
      = (pD r d σ)^(r-1) * (Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ))) := by
    rw [hDr]
    rw [show (pD r d σ)^(r-1) * pD r d σ / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j))
          = (pD r d σ)^(r-1) * (pD r d σ / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j))) by ring]
    rw [hkey]
  have hprodform2 : ∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d))
      ≤ (pD r d σ)^r / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j)) / (2:ℝ)^(pI r d * r) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    exact div_le_div_of_nonneg_right hprodb (by positivity)
  -- `(r+1)! ∏_{j} 𝒟_{j+1} ≤ X₃`
  have hA3 : ((r+1).factorial : ℝ) * ∏ i : Fin r, calD r d h σ i.succ
      ≤ ((r+1).factorial : ℝ) * (pD r d σ)^(r-1) * (2:ℝ)^(5*r+6)
          * Real.log (2*(r:ℝ)*d) * (d:ℝ) / (2:ℝ)^((pI r d) * r) := by
    rw [show (∏ i : Fin r, calD r d h σ i.succ)
          = ∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d)) from
        Finset.prod_congr rfl (fun j _ => calD_succ r d h σ j)]
    calc ((r+1).factorial : ℝ) * ∏ j : Fin r, ((pDj r d σ j : ℝ) / (2:ℝ)^(pI r d))
        ≤ ((r+1).factorial : ℝ)
            * ((pD r d σ)^r / ((r:ℝ)^r*(d:ℝ)^r*(∏ j, σ j)) / (2:ℝ)^(pI r d * r)) :=
          mul_le_mul_of_nonneg_left hprodform2 (by positivity)
      _ = ((r+1).factorial : ℝ) * (pD r d σ)^(r-1) * (2:ℝ)^(5*r+6)
            * Real.log (2*(r:ℝ)*d) * (d:ℝ) / (2:ℝ)^((pI r d) * r) := by
          rw [hDr2]
          ring
  -- the numerical star condition
  have hstar3 : ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5)
        * Real.log (2*(r:ℝ)*d)
      < (2:ℝ)^4 * (11:ℝ)^(r-1) *
          ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^((r * pI r d + 1) * (r-1))
            * (2:ℝ)^(r * pI r d)) := by
    have hpow3 : (2*(r:ℝ)*d)^(6*r)
        ≤ 2 * ((pxi r)^(r-1) * (2 * (pxi r)^(r-2))^(r * pI r d)) := by
      have hbase : (1.15:ℝ) ≤ 2 * (pxi r)^(r-2) := by
        have h1 : (pxi r)^(r-1) ≤ (pxi r)^(r-2) :=
          pow_le_pow_of_le_one (pxi_nonneg r) (pxi_le_one r) (by omega : r-2 ≤ r-1)
        linarith [split_E23_two_pxi_ge hr, h1]
      have h115 : (2*(r:ℝ)*d)^6 ≤ (1.15:ℝ)^(pI r d) := split_E23_pow115 hr hd
      have h3 : (2*(r:ℝ)*d)^(6*r) ≤ (2*(pxi r)^(r-2))^(r*pI r d) := by
        calc (2*(r:ℝ)*d)^(6*r) = ((2*(r:ℝ)*d)^6)^r := by rw [← pow_mul]
          _ ≤ ((1.15:ℝ)^(pI r d))^r := pow_le_pow_left₀ (by positivity) h115 r
          _ = (1.15:ℝ)^(r*pI r d) := by rw [← pow_mul, Nat.mul_comm (pI r d) r]
          _ ≤ (2*(pxi r)^(r-2))^(r*pI r d) := pow_le_pow_left₀ (by norm_num) hbase _
      have h4 : (1:ℝ) ≤ 2*(pxi r)^(r-1) := one_le_two_mul_pxi_pow_pred hr
      have hBnn : (0:ℝ) ≤ (2*(pxi r)^(r-2))^(r*pI r d) :=
        pow_nonneg two_pxi_pred2_nonneg _
      calc (2*(r:ℝ)*d)^(6*r) ≤ (2*(pxi r)^(r-2))^(r*pI r d) := h3
        _ ≤ (2*(pxi r)^(r-2))^(r*pI r d) * (2*(pxi r)^(r-1)) :=
            le_mul_of_one_le_right hBnn h4
        _ = 2 * ((pxi r)^(r-1) * (2 * (pxi r)^(r-2))^(r * pI r d)) := by ring
    have hL : Real.log (2*(r:ℝ)*d) ≤ 2*(r:ℝ)*d := by
      have := split_E23_log2rd hr hd
      linarith
    have hfac := split_E23_facE3 r d hr
    have hLHS : ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5)
          * Real.log (2*(r:ℝ)*d)
        ≤ (2:ℝ)^(8*r+7) * (r:ℝ)^(2*r+1) * (d:ℝ) := by
      have h1 : ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5)
            * Real.log (2*(r:ℝ)*d)
          ≤ ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5)
            * (2*(r:ℝ)*d) := mul_le_mul_of_nonneg_left hL (by positivity)
      linarith [h1, hfac]
    have hRHS : (2:ℝ)^3 * (11:ℝ)^(r-1) * (2*(r:ℝ)*d)^(6*r)
        ≤ (2:ℝ)^4 * (11:ℝ)^(r-1) *
          ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^((r * pI r d + 1) * (r-1))
            * (2:ℝ)^(r * pI r d)) := by
      rw [split_E23_zpow2 hr]
      have h11 : (0:ℝ) < (11:ℝ)^(r-1) := by positivity
      have h := mul_le_mul_of_nonneg_left hpow3 (le_of_lt h11)
      calc (2:ℝ)^3 * (11:ℝ)^(r-1) * (2*(r:ℝ)*d)^(6*r)
          = (2:ℝ)^3 * ((11:ℝ)^(r-1) * (2*(r:ℝ)*d)^(6*r)) := by ring
        _ ≤ (2:ℝ)^3 * ((11:ℝ)^(r-1)
              * (2 * ((pxi r)^(r-1) * (2 * (pxi r)^(r-2))^(r * pI r d)))) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = (2:ℝ)^4 * (11:ℝ)^(r-1)
              * ((pxi r)^(r-1) * (2 * (pxi r)^(r-2))^(r * pI r d)) := by ring
    have hnum := split_E23_numE3 hr hd
    linarith [hLHS, hnum, hRHS]
  -- the comparison: `X₃ < LB₃`, via the positive multiplier `P = 2^N (r-1)! / (d D^{r-1})`
  have hcmp3 : ((r+1).factorial : ℝ) * (pD r d σ)^(r-1) * (2:ℝ)^(5*r+6)
        * Real.log (2*(r:ℝ)*d) * (d:ℝ) / (2:ℝ)^((pI r d) * r)
      < (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
        * (((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^(r-1)
            / ((r-1).factorial : ℝ)) := by
    have hPpos : (0:ℝ) < (2:ℝ)^(r*pI r d) * ((r-1).factorial : ℝ)
        / ((d:ℝ)*(pD r d σ)^(r-1)) := by positivity
    -- `a < b₀`, where `b₀ = H₃ / 2^{r-1}`
    have hab : ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(5*r+6)
          * Real.log (2*(r:ℝ)*d)
        < ((2:ℝ)^4 * (11:ℝ)^(r-1)
            * ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^((r * pI r d + 1) * (r-1))
              * (2:ℝ)^(r * pI r d))) / (2:ℝ)^(r-1) := by
      have hK2 : ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(6*r+5)
            * Real.log (2*(r:ℝ)*d) / (2:ℝ)^(r-1)
          = ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(5*r+6)
            * Real.log (2*(r:ℝ)*d) := by
        rw [exp6r5 hr, pow_add]
        rw [show ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ)
              * ((2:ℝ)^(5*r+6) * (2:ℝ)^(r-1)) * Real.log (2*(r:ℝ)*d) / (2:ℝ)^(r-1)
            = ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(5*r+6)
              * Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(r-1) / (2:ℝ)^(r-1)) by ring]
        rw [div_self (by positivity : (2:ℝ)^(r-1) ≠ 0), mul_one]
      have h1 := div_lt_div_of_pos_right hstar3 (by positivity : (0:ℝ) < (2:ℝ)^(r-1))
      rw [hK2] at h1
      exact h1
    have hb₀nn : (0:ℝ) ≤ ((2:ℝ)^4 * (11:ℝ)^(r-1)
            * ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^((r * pI r d + 1) * (r-1))
              * (2:ℝ)^(r * pI r d))) / (2:ℝ)^(r-1) := by
      have h1 : (0:ℝ) ≤ (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) := zpow_pxi_nonneg _
      have h2 : (0:ℝ) ≤ (pxi r)^((r * pI r d + 1) * (r-1)) := pxi_pow_nonneg r _
      positivity
    have hab' : ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(5*r+6)
          * Real.log (2*(r:ℝ)*d)
        < (((2:ℝ)^4 * (11:ℝ)^(r-1)
            * ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^((r * pI r d + 1) * (r-1))
              * (2:ℝ)^(r * pI r d))) / (2:ℝ)^(r-1)) * (h:ℝ) :=
      lt_of_lt_of_le hab (le_mul_of_one_le_right hb₀nn hh1)
    -- the two product identities
    have hAP : (((r+1).factorial : ℝ) * (pD r d σ)^(r-1) * (2:ℝ)^(5*r+6)
          * Real.log (2*(r:ℝ)*d) * (d:ℝ) / (2:ℝ)^((pI r d) * r))
        * ((2:ℝ)^(r*pI r d) * ((r-1).factorial : ℝ) / ((d:ℝ)*(pD r d σ)^(r-1)))
        = ((r+1).factorial : ℝ) * ((r-1).factorial : ℝ) * (2:ℝ)^(5*r+6)
          * Real.log (2*(r:ℝ)*d) := by
      field_simp <;> ring
    have hBP : ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
          * (((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^(r-1)
              / ((r-1).factorial : ℝ)))
        * ((2:ℝ)^(r*pI r d) * ((r-1).factorial : ℝ) / ((d:ℝ)*(pD r d σ)^(r-1)))
        = (((2:ℝ)^4 * (11:ℝ)^(r-1)
            * ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^((r * pI r d + 1) * (r-1))
              * (2:ℝ)^(r * pI r d))) / (2:ℝ)^(r-1)) * (h:ℝ) := by
      rw [mul_pow]
      rw [show ((pxi r)^(r*pI r d + 1))^(r-1) = (pxi r)^((r*pI r d + 1) * (r-1)) by
            rw [pow_mul],
        show (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))^(r-1)
              = (11:ℝ)^(r-1) * (pD r d σ)^(r-1) / (2:ℝ)^(r-1) by
          rw [eleven_rD_div_two_r hr (pD r d σ), div_pow, mul_pow]]
      field_simp <;> ring
    have hlt : (((r+1).factorial : ℝ) * (pD r d σ)^(r-1) * (2:ℝ)^(5*r+6)
          * Real.log (2*(r:ℝ)*d) * (d:ℝ) / (2:ℝ)^((pI r d) * r))
        * ((2:ℝ)^(r*pI r d) * ((r-1).factorial : ℝ) / ((d:ℝ)*(pD r d σ)^(r-1)))
      < ((pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
          * (((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^(r-1)
              / ((r-1).factorial : ℝ)))
        * ((2:ℝ)^(r*pI r d) * ((r-1).factorial : ℝ) / ((d:ℝ)*(pD r d σ)^(r-1))) := by
      rw [hAP, hBP]
      exact hab'
    exact lt_of_mul_lt_mul_right hlt (le_of_lt hPpos)
  -- the lower bound `LB₃`
  have hbase_nn : (0:ℝ) ≤ (pxi r)^(r*pI r d + 1)
      * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))) :=
    mul_nonneg (pow_nonneg (pxi_nonneg r) _) (by positivity)
  have hTmain : (pxi r)^(r * pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))
      ≤ calT r d σ / (2*(r:ℝ)) := by
    rw [calT_eq]
    rw [show pxi r * (pxi r)^(r*pI r d) * (pT r d σ : ℝ) / (2*(r:ℝ))
          = ((pxi r)^(r*pI r d + 1) * (pT r d σ : ℝ)) / (2*(r:ℝ)) by
        rw [show pxi r * (pxi r)^(r*pI r d) = (pxi r)^(r*pI r d + 1) by
              rw [mul_comm (pxi r) ((pxi r)^(r*pI r d)), ← pow_succ]]]
    rw [show (pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))
          = ((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)))/(2*(r:ℝ)) by ring]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pT_ge hr hd σ hσ) (pow_nonneg (pxi_nonneg r) _))
      (by positivity)
  have hCbound : ((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^(r-1)
        / ((r-1).factorial : ℝ)
      ≤ ((⌊calT r d σ/(2*(r:ℝ))⌋₊ + (r-1)).choose (r-1) : ℝ) := by
    have h1 : (pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ)))
        ≤ ((⌊calT r d σ/(2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1 :=
      le_trans hTmain (le_of_lt (Nat.lt_floor_add_one _))
    calc ((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^(r-1)
          / ((r-1).factorial : ℝ)
        ≤ (((⌊calT r d σ/(2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1)^(r-1) / ((r-1).factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hbase_nn h1 (r-1)) (by positivity)
      _ ≤ ((⌊calT r d σ/(2*(r:ℝ))⌋₊ + (r-1)).choose (r-1) : ℝ) := by
          simpa using choose_lower (⌊calT r d σ/(2*(r:ℝ))⌋₊) (r-1)
  have hLB3 : (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
        * (((pxi r)^(r*pI r d + 1) * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^(r-1)
            / ((r-1).factorial : ℝ))
      ≤ ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℝ) + 1)
        * ((⌊calT r d σ / (2*(r:ℝ))⌋₊ + (r-1)).choose (r-1) : ℝ) := by
    have hSmain := calS_div_two_r (r := r) (d := d) (h := h) hr0
    have h1 : (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (16*(d:ℝ)*(h:ℝ))
        ≤ ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1 := by
      rw [← hSmain]
      exact le_of_lt (Nat.lt_floor_add_one _)
    have h4 : (0:ℝ) ≤ ((⌊calS r d h / (2*(r:ℝ))⌋₊ : ℕ) : ℝ) + 1 := by positivity
    have hc : (0:ℝ) ≤ ((pxi r)^(r*pI r d + 1)
        * (11*(r:ℝ)*(pD r d σ)/(2*(r:ℝ))))^(r-1) / ((r-1).factorial : ℝ) :=
      div_nonneg (pow_nonneg hbase_nn _) (by positivity)
    exact mul_le_mul h1 hCbound hc h4
  exact lt_of_le_of_lt hA3 (lt_of_lt_of_le hcmp3 hLB3)

theorem split_E23 {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1/(d : ℝ) ≤ σ j) :
    ((r + 1).factorial : ℝ) * ∏ i, calD r d h σ i <
      ((halfSplit r (calS r d h) r : ℝ) + 1) *
        ((halfSplit r (calT r d σ) r + r).choose r : ℝ) ∧
    ((r + 1).factorial : ℝ) * ∏ i : Fin r, calD r d h σ i.succ <
      ((halfSplit r (calS r d h) (r - 1) : ℝ) + 1) *
        ((halfSplit r (calT r d σ) (r - 1) + (r - 1)).choose (r - 1) : ℝ) := by
  have hr0 : r ≠ 0 := by omega
  have hr10 : r - 1 ≠ 0 := by omega
  constructor
  · rw [halfSplit_ne_zero hr0 (calS r d h), halfSplit_ne_zero hr0 (calT r d σ)]
    simpa using E2_ineq hr hd hh σ hσ
  · rw [halfSplit_ne_zero hr10 (calS r d h), halfSplit_ne_zero hr10 (calT r d σ)]
    simpa using E3_ineq hr hd hh σ hσ

end Work.BW
