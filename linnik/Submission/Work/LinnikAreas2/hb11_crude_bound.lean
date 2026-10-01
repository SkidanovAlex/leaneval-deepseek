import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikAreas.Density4.det_split
import Submission.Work.LinnikAreas.Density4.tsum_nat_mul_exp_neg_div_le

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas2

/-! ## Auxiliary estimates for the crude HB (11.16) bound -/

/-- For `q ≥ 2`, twice HB's `λ₀ = (1/3) log log log q` is at most `log q`. -/
lemma hb11_lamMax_le_half_log (q : ℕ) (hq : 2 ≤ q) :
    2 * Work.LinnikContract2.lamMax q ≤ Real.log (q:ℝ) := by
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq1 : (1:ℝ) < (q:ℝ) := by linarith
  have hA : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hL2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hA2 : Real.log 2 ≤ Real.log (q:ℝ) := Real.log_le_log (by norm_num) hq2
  have hkey : Real.log (Real.log (Real.log (q:ℝ))) ≤ 3 * Real.log (q:ℝ) / 2 := by
    by_cases hz : 0 ≤ Real.log (Real.log (q:ℝ))
    · have h1 : Real.log (Real.log (Real.log (q:ℝ))) ≤ Real.log (Real.log (q:ℝ)) :=
        Real.log_le_self hz
      have h2 : Real.log (Real.log (q:ℝ)) ≤ Real.log (q:ℝ) := Real.log_le_self hA.le
      linarith
    · have hzlt : Real.log (Real.log (q:ℝ)) < 0 := lt_of_not_ge hz
      have hzlb : Real.log (Real.log 2) ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log hL2 hA2
      have hlogL2 : -Real.log (Real.log 2) ≤ 1 := by
        have h1 : (Real.log 2)⁻¹ ≤ 2 := by
          rw [inv_le_iff_one_le_mul₀ hL2]
          linarith [Real.log_two_gt_d9]
        have h2 : Real.log ((Real.log 2)⁻¹) ≤ Real.log 2 := Real.log_le_log (inv_pos.mpr hL2) h1
        have h3 : Real.log ((Real.log 2)⁻¹) = -Real.log (Real.log 2) := Real.log_inv _
        have h4 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
        linarith
      have hlogz : Real.log (Real.log (Real.log (q:ℝ)))
          = Real.log (-(Real.log (Real.log (q:ℝ)))) := by
        rw [Real.log_neg_eq_log]
      rw [hlogz]
      have h5 : Real.log (-(Real.log (Real.log (q:ℝ)))) ≤ -(Real.log (Real.log (q:ℝ))) - 1 :=
        Real.log_le_sub_one_of_pos (by linarith [hzlt])
      linarith
  rw [Work.LinnikContract2.lamMax]
  linarith

/-- Each summand of HB's (11.7) mollifier is bounded by `1` in modulus (for `W > 1`). -/
lemma abs_thetaM_le_one {W : ℝ} (hW : 1 < W) (d : ℕ) :
    |Work.LinnikAreas.Density4.thetaM W d| ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [Work.LinnikAreas.Density4.thetaM]
  · have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    rw [Work.LinnikAreas.Density4.thetaM]
    split_ifs with hdle
    · have hlogW : 0 < Real.log W := Real.log_pos hW
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        rw [← Int.cast_abs]
        exact_mod_cast h
      have hWd1 : 1 ≤ W / (d:ℝ) := (one_le_div₀ hdpos).mpr (by linarith)
      have hWdle : W / (d:ℝ) ≤ W := by
        rw [div_le_iff₀ hdpos]; nlinarith [hd1, hW]
      have hlognn : 0 ≤ Real.log (W / (d:ℝ)) := Real.log_nonneg hWd1
      have hlogle : Real.log (W / (d:ℝ)) ≤ Real.log W := Real.log_le_log (by linarith) hWdle
      rw [abs_div, abs_mul, abs_of_nonneg hlognn, abs_of_pos hlogW, div_le_one₀ hlogW]
      calc |(ArithmeticFunction.moebius d : ℝ)| * Real.log (W / (d:ℝ))
          ≤ 1 * Real.log W := mul_le_mul hmu hlogle hlognn (by norm_num)
        _ = Real.log W := one_mul _
    · simp

/-- The divisor sum of HB's (11.7) mollifier is bounded by `n`. -/
lemma hb11_theta_sum_le (W : ℝ) (hW : 1 < W) (n : ℕ) :
    ‖((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)‖ ≤ (n : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc |∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d|
      ≤ ∑ d ∈ n.divisors, |Work.LinnikAreas.Density4.thetaM W d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, (1:ℝ) := Finset.sum_le_sum (fun d _ => abs_thetaM_le_one hW d)
    _ = (n.divisors.card : ℝ) := by simp
    _ ≤ (n : ℝ) := by exact_mod_cast Nat.card_divisors_le_self n

/-- The majorant `Σ n² e^{-n/Z}` converges with bound `2 Z (2Z+1)²`. -/
lemma hb11_majorant (Z : ℝ) (hZ : 1 ≤ Z) :
    Summable (fun n : ℕ => (n : ℝ)^2 * Real.exp (-(n : ℝ) / Z)) ∧
      (∑' n : ℕ, (n : ℝ)^2 * Real.exp (-(n : ℝ) / Z)) ≤ 2 * Z * (2 * Z + 1)^2 := by
  have hZpos : 0 < Z := by linarith
  have hnorm : ‖Real.exp (-(1/(2*Z)))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    have : 0 < 1/(2*Z) := by positivity
    linarith
  have hsum_base : Summable (fun n : ℕ => (n:ℝ) * Real.exp (-(1/(2*Z)))^n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hbase_exp : ∀ n : ℕ, Real.exp (-(1/(2*Z)))^n = Real.exp (-(n:ℝ)/(2*Z)) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum2 : Summable (fun n : ℕ => (n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))) :=
    hsum_base.congr (fun n => by rw [hbase_exp n])
  have hmax : ∀ n : ℕ, (n:ℝ) * Real.exp (-(n:ℝ)/(2*Z)) ≤ 2*Z := by
    intro n
    have h1 : (n:ℝ)/(2*Z) ≤ Real.exp ((n:ℝ)/(2*Z)) := by
      have := Real.add_one_le_exp ((n:ℝ)/(2*Z)); linarith
    have h3 : ((n:ℝ)/(2*Z)) * Real.exp (-(n:ℝ)/(2*Z)) ≤ 1 := by
      calc ((n:ℝ)/(2*Z)) * Real.exp (-(n:ℝ)/(2*Z))
          ≤ Real.exp ((n:ℝ)/(2*Z)) * Real.exp (-(n:ℝ)/(2*Z)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 := by
            rw [← Real.exp_add, show (n:ℝ)/(2*Z) + -(n:ℝ)/(2*Z) = 0 by ring, Real.exp_zero]
    have h2Zr : (2:ℝ)*Z * ((n:ℝ)/(2*Z)) = (n:ℝ) := by
      rw [mul_comm ((2:ℝ)*Z) ((n:ℝ)/(2*Z)),
        div_mul_cancel₀ (n:ℝ) (ne_of_gt (by linarith : (0:ℝ) < 2*Z))]
    have hkey : (2:ℝ)*Z * (((n:ℝ)/(2*Z)) * Real.exp (-(n:ℝ)/(2*Z)))
        = (n:ℝ) * Real.exp (-(n:ℝ)/(2*Z)) := by
      rw [← mul_assoc, h2Zr]
    calc (n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))
        = 2*Z * (((n:ℝ)/(2*Z)) * Real.exp (-(n:ℝ)/(2*Z))) := hkey.symm
      _ ≤ 2*Z * 1 := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = 2*Z := by ring
  have hle : ∀ n : ℕ, (n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)
      ≤ 2*Z * ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))) := by
    intro n
    have hsq : ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z)))^2 = (n:ℝ)^2 * Real.exp (-(n:ℝ)/Z) := by
      have h1 : (Real.exp (-(n:ℝ)/(2*Z)))^2 = Real.exp (-(n:ℝ)/Z) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [mul_pow, h1]
    calc (n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)
        = ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z)))^2 := hsq.symm
      _ = ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))) * ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))) := by
          rw [pow_two]
      _ ≤ (2*Z) * ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))) :=
          mul_le_mul_of_nonneg_right (hmax n) (by positivity)
  have hsum_maj : Summable (fun n : ℕ => 2*Z * ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z)))) :=
    hsum2.mul_left (2*Z)
  have hsumg : Summable (fun n : ℕ => (n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hsum_maj
  refine ⟨hsumg, ?_⟩
  calc (∑' n : ℕ, (n:ℝ)^2 * Real.exp (-(n:ℝ)/Z))
      ≤ ∑' n : ℕ, 2*Z * ((n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))) :=
        Summable.tsum_le_tsum hle hsumg hsum_maj
    _ = 2*Z * (∑' n : ℕ, (n:ℝ) * Real.exp (-(n:ℝ)/(2*Z))) := tsum_mul_left
    _ ≤ 2*Z * (2*Z+1)^2 := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have hc : (∑' n : ℕ, (n:ℝ) * Real.exp (-(n:ℝ)/(2*Z)))
            = (∑' n : ℕ, (n:ℝ) * Real.exp (-(1/(2*Z)))^n) :=
          tsum_congr (fun n => by rw [hbase_exp n])
        rw [hc]
        exact Work.LinnikAreas.Density4.tsum_nat_mul_exp_neg_div_le (2*Z) (by linarith)

/-- The summand of HB (11.16). -/
def hb11S (q : ℕ) [NeZero q] (u w x : ℝ) (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ)
    (n : ℕ) : ℂ :=
  (((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ)^2 *
    (χ (n : ZMod q) * (starRingEnd ℂ (χ' (n : ZMod q)))) *
    ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ ρ'))) *
    (((Real.exp (-(n : ℝ) / (q:ℝ)^x)
        - Real.exp (-(n : ℝ) * (Real.log q)^2 / (q:ℝ)^u)) : ℝ) : ℂ)

/-- Pointwise bound for the summand of HB (11.16) on the working region. -/
lemma hb11S_norm_le (q : ℕ) [NeZero q] (hq : 2 ≤ q) {u w x Z : ℝ} (hw : 0 < w)
    (hZ1 : 1 ≤ Z) (hZX : (q:ℝ)^x ≤ Z) (hZY : (q:ℝ)^u / (Real.log q)^2 ≤ Z)
    (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ)
    (hρ : Work.LinnikContract2.IsZ χ ρ)
    (hlam : Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q)
    (hρ' : Work.LinnikContract2.IsZ χ' ρ')
    (hlam' : Work.LinnikContract2.lamOf q ρ' ≤ Work.LinnikContract2.lamMax q) (n : ℕ) :
    ‖hb11S q u w x χ χ' ρ ρ' n‖ ≤ 2 * ((n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [hb11S, Nat.divisors_zero]
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hq1 : (1:ℝ) < (q:ℝ) := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hlam2 : 2 * Work.LinnikContract2.lamMax q ≤ Real.log (q:ℝ) := hb11_lamMax_le_half_log q hq
  have hL1 : 2 * (Work.LinnikContract2.lamMax q / Real.log (q:ℝ)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one₀ hlogq]
    exact hlam2
  have hρre : 1 - Work.LinnikContract2.lamMax q / Real.log (q:ℝ) ≤ ρ.re := by
    have h := hlam
    rw [Work.LinnikContract2.lamOf] at h
    have := (le_div_iff₀ hlogq).mpr h
    linarith
  have hρre' : 1 - Work.LinnikContract2.lamMax q / Real.log (q:ℝ) ≤ ρ'.re := by
    have h := hlam'
    rw [Work.LinnikContract2.lamOf] at h
    have := (le_div_iff₀ hlogq).mpr h
    linarith
  have hRe : (1 - ρ - (starRingEnd ℂ ρ')).re ≤ 0 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hW : 1 < (q:ℝ)^w := Real.one_lt_rpow hq1 hw
  set A : ℂ := ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ) : ℂ)
    with hA
  set B : ℂ := (χ (n : ZMod q) * (starRingEnd ℂ (χ' (n : ZMod q)))) with hB
  set Cc : ℂ := ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ ρ'))) with hC
  set D : ℂ := (((Real.exp (-(n : ℝ) / (q:ℝ)^x)
      - Real.exp (-(n : ℝ) * (Real.log q)^2 / (q:ℝ)^u)) : ℝ) : ℂ) with hD
  have hdef : hb11S q u w x χ χ' ρ ρ' n = A^2 * B * Cc * D := by
    simp only [hb11S, hA, hB, hC, hD]
  have hAn : ‖A‖ ≤ (n:ℝ) := hb11_theta_sum_le ((q:ℝ)^w) hW n
  have hA2 : ‖A^2‖ ≤ (n:ℝ)^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hAn 2
  have hB1 : ‖B‖ ≤ 1 := by
    rw [hB, norm_mul, Complex.norm_conj]
    calc ‖χ (n : ZMod q)‖ * ‖χ' (n : ZMod q)‖ ≤ 1 * 1 :=
          mul_le_mul (DirichletCharacter.norm_le_one χ _) (DirichletCharacter.norm_le_one χ' _)
            (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hC1 : ‖Cc‖ ≤ 1 := by
    rw [hC, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 hRe
  have hD1 : ‖D‖ ≤ 2 * Real.exp (-(n:ℝ)/Z) := by
    rw [hD, Complex.norm_real, Real.norm_eq_abs]
    have hXpos : 0 < (q:ℝ)^x := Real.rpow_pos_of_pos (by positivity) x
    have hYpos : 0 < (q:ℝ)^u / (Real.log q)^2 :=
      div_pos (Real.rpow_pos_of_pos (by positivity) u) (pow_pos hlogq 2)
    have e1 : Real.exp (-(n:ℝ)/(q:ℝ)^x) ≤ Real.exp (-(n:ℝ)/Z) := by
      rw [Real.exp_le_exp]
      simp only [neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left (le_of_lt hn0) hXpos hZX)
    have e2 : Real.exp (-(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u) ≤ Real.exp (-(n:ℝ)/Z) := by
      rw [show -(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u
            = -(n:ℝ)/((q:ℝ)^u / (Real.log q)^2) by field_simp]
      rw [Real.exp_le_exp]
      simp only [neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left (le_of_lt hn0) hYpos hZY)
    have hsub : |Real.exp (-(n:ℝ)/(q:ℝ)^x)
        - Real.exp (-(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u)|
        ≤ |Real.exp (-(n:ℝ)/(q:ℝ)^x)| + |Real.exp (-(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u)| := by
      have h := abs_add_le (Real.exp (-(n:ℝ)/(q:ℝ)^x))
        (-(Real.exp (-(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u)))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h
    calc |Real.exp (-(n:ℝ)/(q:ℝ)^x) - Real.exp (-(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u)|
        ≤ |Real.exp (-(n:ℝ)/(q:ℝ)^x)| + |Real.exp (-(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u)| := hsub
      _ = Real.exp (-(n:ℝ)/(q:ℝ)^x) + Real.exp (-(n:ℝ) * (Real.log q)^2 / (q:ℝ)^u) := by
          rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n:ℝ)/Z) + Real.exp (-(n:ℝ)/Z) := add_le_add e1 e2
      _ = 2 * Real.exp (-(n:ℝ)/Z) := by ring
  rw [hdef, norm_mul, norm_mul, norm_mul]
  have h1 : ‖A^2‖ * ‖B‖ ≤ (n:ℝ)^2 * 1 := mul_le_mul hA2 hB1 (norm_nonneg _) (by positivity)
  have h2 : ‖A^2‖ * ‖B‖ * ‖Cc‖ ≤ (n:ℝ)^2 * 1 * 1 :=
    mul_le_mul h1 hC1 (norm_nonneg _) (by positivity)
  have h3 : ‖A^2‖ * ‖B‖ * ‖Cc‖ * ‖D‖
      ≤ (n:ℝ)^2 * 1 * 1 * (2 * Real.exp (-(n:ℝ)/Z)) :=
    mul_le_mul h2 hD1 (norm_nonneg _) (by positivity)
  calc ‖A^2‖ * ‖B‖ * ‖Cc‖ * ‖D‖ ≤ (n:ℝ)^2 * 1 * 1 * (2 * Real.exp (-(n:ℝ)/Z)) := h3
    _ = 2 * ((n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)) := by ring

/-- The crude HB (11.16) bound for a fixed `q`: the smoothed twisted sum is `O(1)`. -/
theorem norm_hb11S_tsum_le (q : ℕ) [NeZero q] (hq : 2 ≤ q) {u w x Z : ℝ} (hw : 0 < w)
    (hZ1 : 1 ≤ Z) (hZX : (q:ℝ)^x ≤ Z) (hZY : (q:ℝ)^u / (Real.log q)^2 ≤ Z)
    (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ)
    (hρ : Work.LinnikContract2.IsZ χ ρ)
    (hlam : Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q)
    (hρ' : Work.LinnikContract2.IsZ χ' ρ')
    (hlam' : Work.LinnikContract2.lamOf q ρ' ≤ Work.LinnikContract2.lamMax q) :
    ‖∑' n : ℕ, hb11S q u w x χ χ' ρ ρ' n‖ ≤ 4 * Z * (2*Z+1)^2 := by
  have hpt : ∀ n : ℕ, ‖hb11S q u w x χ χ' ρ ρ' n‖
      ≤ 2 * ((n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)) :=
    fun n => hb11S_norm_le q hq hw hZ1 hZX hZY χ χ' ρ ρ' hρ hlam hρ' hlam' n
  have hsum_maj : Summable (fun n : ℕ => 2 * ((n:ℝ)^2 * Real.exp (-(n:ℝ)/Z))) :=
    (hb11_majorant Z hZ1).1.mul_left 2
  have hsum_norm : Summable (fun n : ℕ => ‖hb11S q u w x χ χ' ρ ρ' n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt hsum_maj
  calc ‖∑' n : ℕ, hb11S q u w x χ χ' ρ ρ' n‖
      ≤ ∑' n : ℕ, ‖hb11S q u w x χ χ' ρ ρ' n‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, 2 * ((n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)) :=
        Summable.tsum_le_tsum hpt hsum_norm hsum_maj
    _ = 2 * (∑' n : ℕ, (n:ℝ)^2 * Real.exp (-(n:ℝ)/Z)) := tsum_mul_left
    _ ≤ 2 * (2 * Z * (2*Z+1)^2) :=
        mul_le_mul_of_nonneg_left (hb11_majorant Z hZ1).2 (by norm_num)
    _ = 4 * Z * (2*Z+1)^2 := by ring

/-- **HB (1992) §11, (11.16), crude form.**  For the finitely many moduli `q < Q` the smoothed
twisted sum of the non-diagonal terms of the mollified density computation is `O(1/log q)`,
uniformly over the characters `χ ≠ χ'` and over the zeros `ρ, ρ'` of the working region with
`λ(ρ), λ(ρ') ≤ λ₀`. -/
theorem hb11_crude_bound (u w x : ℝ) (hw : 0 < w) (hwu : w < u) (hux : u < x) (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q → q < Q →
      ∀ (χ χ' : DirichletCharacter ℂ q), χ * χ'⁻¹ ≠ 1 →
      ∀ (ρ ρ' : ℂ), Work.LinnikContract2.IsZ χ ρ →
        Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q →
        Work.LinnikContract2.IsZ χ' ρ' →
        Work.LinnikContract2.lamOf q ρ' ≤ Work.LinnikContract2.lamMax q →
        ‖∑' n : ℕ,
            (((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ)^2 *
            (χ (n : ZMod q) * (starRingEnd ℂ (χ' (n : ZMod q)))) *
            ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ ρ'))) *
            (((Real.exp (-(n : ℝ) / (q:ℝ)^x)
                - Real.exp (-(n : ℝ) * (Real.log q)^2 / (q:ℝ)^u)) : ℝ) : ℂ)‖
          ≤ C / Real.log q := by
  set Z : ℝ := max ((Q:ℝ)^x) ((Q:ℝ)^u / (Real.log 2)^2) + 1 with hZdef
  set S : ℝ := ∑ i ∈ Finset.range Q, |Real.log (i:ℝ)| with hSdef
  have hZ1 : 1 ≤ Z := by
    rw [hZdef]
    have hA : 0 ≤ (Q:ℝ)^x := Real.rpow_nonneg (Nat.cast_nonneg Q) x
    have hB : 0 ≤ (Q:ℝ)^u / (Real.log 2)^2 :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Q) u) (sq_nonneg _)
    have h1 := le_max_left ((Q:ℝ)^x) ((Q:ℝ)^u / (Real.log 2)^2)
    have h2 := le_max_right ((Q:ℝ)^x) ((Q:ℝ)^u / (Real.log 2)^2)
    linarith
  have hSnn : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hMpos : 0 < 4 * Z * (2*Z+1)^2 := by
    have : 0 < Z := by linarith
    positivity
  refine ⟨1 + 4 * Z * (2*Z+1)^2 * S, ?_, ?_⟩
  · have : 0 ≤ 4 * Z * (2*Z+1)^2 * S := mul_nonneg hMpos.le hSnn
    linarith
  · intro q hqN hq2 hqQ χ χ' _ ρ ρ' hρ hlam hρ' hlam'
    have hq2' : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
    have hqQ' : (q:ℝ) < (Q:ℝ) := by exact_mod_cast hqQ
    have hxpos : 0 < x := by linarith
    have hupos : 0 < u := by linarith
    have hqx : (q:ℝ)^x ≤ Z := by
      rw [hZdef]
      have h1 : (q:ℝ)^x ≤ (Q:ℝ)^x := Real.rpow_le_rpow (by positivity) hqQ'.le hxpos.le
      have h2 : (Q:ℝ)^x ≤ max ((Q:ℝ)^x) ((Q:ℝ)^u / (Real.log 2)^2) := le_max_left _ _
      linarith
    have hqy : (q:ℝ)^u / (Real.log (q:ℝ))^2 ≤ Z := by
      rw [hZdef]
      have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
      have hL2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have h1 : (q:ℝ)^u ≤ (Q:ℝ)^u := Real.rpow_le_rpow (by positivity) hqQ'.le hupos.le
      have hlogmono : Real.log 2 ≤ Real.log (q:ℝ) := Real.log_le_log (by norm_num) hq2'
      have h2 : (Real.log 2)^2 ≤ (Real.log (q:ℝ))^2 := pow_le_pow_left₀ hL2.le hlogmono 2
      have h3 : (q:ℝ)^u / (Real.log (q:ℝ))^2 ≤ (Q:ℝ)^u / (Real.log 2)^2 := by
        rw [div_le_div_iff₀ (pow_pos hlogq 2) (pow_pos hL2 2)]
        exact mul_le_mul h1 h2 (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg Q) u)
      have h4 : (Q:ℝ)^u / (Real.log 2)^2 ≤ max ((Q:ℝ)^x) ((Q:ℝ)^u / (Real.log 2)^2) :=
        le_max_right _ _
      linarith
    have hM := norm_hb11S_tsum_le q hq2 hw hZ1 hqx hqy χ χ' ρ ρ' hρ hlam hρ' hlam'
    have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlogq]
    change ‖∑' n : ℕ, hb11S q u w x χ χ' ρ ρ' n‖ * Real.log (q:ℝ)
        ≤ 1 + 4 * Z * (2*Z+1)^2 * S
    have hmem : q ∈ Finset.range Q := Finset.mem_range.mpr hqQ
    have hSle : |Real.log (q:ℝ)| ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (f := fun i : ℕ => |Real.log (i:ℝ)|) (a := q)
        (fun i _ => abs_nonneg _) hmem
    have hMnn : 0 ≤ 4 * Z * (2*Z+1)^2 := le_of_lt hMpos
    calc ‖∑' n : ℕ, hb11S q u w x χ χ' ρ ρ' n‖ * Real.log (q:ℝ)
        ≤ (4 * Z * (2*Z+1)^2) * Real.log (q:ℝ) := mul_le_mul_of_nonneg_right hM hlogq.le
      _ = (4 * Z * (2*Z+1)^2) * |Real.log (q:ℝ)| := by rw [abs_of_pos hlogq]
      _ ≤ (4 * Z * (2*Z+1)^2) * S := mul_le_mul_of_nonneg_left hSle hMnn
      _ ≤ 1 + 4 * Z * (2*Z+1)^2 * S := by linarith

end Work.LinnikAreas2
