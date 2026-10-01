import Mathlib
import Submission.Work.LinnikAreas.Density4.selTheta_asymptotic
import Submission.Work.LinnikAreas.Density4.ThetaPow.log_ratio_gen
import Submission.Work.LinnikAreas.Density4.ThetaPow.rpow_neg_mul_log_rpow_bounded

namespace Work.LinnikAreas.Density4.ThetaPow

open scoped BigOperators
open Finset

noncomputable section

/-- `LpowA A Q = (log (2+Q))^{-A}` with a real exponent. -/
def LpowA (A Q : ℝ) : ℝ := (Real.log (2 + Q)) ^ (-A)

lemma LpowA_pos {A Q : ℝ} (hQ : 1 ≤ Q) : 0 < LpowA A Q := by
  rw [LpowA]
  exact Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _

/-- Base case at exponent `A`: the exponential decay of `selU` (`selberg_U_decay`)
beats every power of `log`, so `|selU Q - 1| ≤ c (log(2+Q))^{-A}` for every `A > 0`. -/
theorem selU_pow_bound (A : ℝ) (_hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 1 ≤ Q →
      |selU Q - 1| ≤ c * (Real.log (2 + Q)) ^ (-A) := by
  by_cases hA3 : A ≤ 3
  · obtain ⟨c3, hc3, hb3⟩ := selU_sub_one_bound
    refine ⟨c3, hc3, fun Q hQ => ?_⟩
    refine le_trans (hb3 Q hQ) ?_
    apply mul_le_mul_of_nonneg_left _ hc3.le
    have hlog1 : (1:ℝ) ≤ Real.log (2 + Q) := by
      have h4 : Real.log 3 ≤ Real.log (2 + Q) := Real.log_le_log (by norm_num) (by linarith)
      have h5 : (1:ℝ) ≤ Real.log 3 :=
        (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three.le
      linarith
    rw [← Real.rpow_intCast (Real.log (2 + Q)) (-3)]
    apply Real.rpow_le_rpow_of_exponent_le hlog1
    push_cast
    linarith
  · push_neg at hA3
    obtain ⟨c3, hc3, hb3⟩ := selU_sub_one_bound
    obtain ⟨c, C, hc, hC, hdec⟩ := selberg_U_decay
    set n : ℕ := Nat.ceil (2*A+1) with hn
    set B : ℝ := C * (2:ℝ)^A * 2 * max 1 ((n.factorial : ℝ) / c^n) with hB
    have hBpos : 0 < B := by
      rw [hB]
      have h1 : (1:ℝ) ≤ max 1 ((n.factorial:ℝ)/c^n) := le_max_left _ _
      have h3 : 0 < max 1 ((n.factorial:ℝ)/c^n) := lt_of_lt_of_le one_pos h1
      have h2 : 0 < (2:ℝ)^A := Real.rpow_pos_of_pos (by norm_num) A
      positivity
    refine ⟨max (c3 * (Real.log 4) ^ (A - 3)) B, lt_max_of_lt_right hBpos, fun Q hQ => ?_⟩
    have hlog1 : (1:ℝ) ≤ Real.log (2 + Q) := by
      have h4 : Real.log 3 ≤ Real.log (2 + Q) := Real.log_le_log (by norm_num) (by linarith)
      have h5 : (1:ℝ) ≤ Real.log 3 :=
        (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three.le
      linarith
    rcases lt_or_ge Q 2 with hQ2 | hQ2
    · have hlog4 : Real.log (2 + Q) ≤ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
      have hsplit : (Real.log (2+Q)) ^ (-3:ℤ)
          = (Real.log (2+Q)) ^ (-A) * (Real.log (2+Q)) ^ (A-3) := by
        rw [← Real.rpow_intCast (Real.log (2+Q)) (-3),
            ← Real.rpow_add (Real.log_pos (by linarith))]
        congr 1; push_cast; ring
      have hb3' : (Real.log (2+Q)) ^ (A-3) ≤ (Real.log 4)^(A-3) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog4 (by linarith)
      calc |selU Q - 1|
          ≤ c3 * (Real.log (2+Q)) ^ (-3:ℤ) := hb3 Q hQ
        _ = c3 * ((Real.log (2+Q)) ^ (-A) * (Real.log (2+Q)) ^ (A-3)) := by rw [hsplit]
        _ ≤ c3 * ((Real.log (2+Q)) ^ (-A) * (Real.log 4)^(A-3)) := by
              apply mul_le_mul_of_nonneg_left _ hc3.le
              exact mul_le_mul_of_nonneg_left hb3' (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
        _ = (c3 * (Real.log 4)^(A-3)) * (Real.log (2+Q))^(-A) := by ring
        _ ≤ max (c3 * (Real.log 4)^(A-3)) B * (Real.log (2+Q))^(-A) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
    · have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
      have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
      set s : ℝ := Real.sqrt (Real.log Q) with hs
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s^2 = Real.log Q := Real.sq_sqrt hlogQ.le
      have hs2' : s ^ (2:ℝ) = Real.log Q := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, hs2]
      have hlog2Q0 : 0 ≤ Real.log (2 + Q) := Real.log_nonneg (by linarith)
      have hlog2Q_le : Real.log (2 + Q) ≤ 2 * Real.log Q :=
        log_add_two_le_two_mul_log Q hQ2
      have hpow_le : (Real.log (2 + Q))^A ≤ (2:ℝ)^A * s^(2*A) := by
        calc (Real.log (2 + Q))^A ≤ (2 * Real.log Q)^A :=
              Real.rpow_le_rpow hlog2Q0 hlog2Q_le (by linarith)
          _ = (2:ℝ)^A * (Real.log Q)^A := Real.mul_rpow (by norm_num) hlogQ.le
          _ = (2:ℝ)^A * s^(2*A) := by rw [← hs2', ← Real.rpow_mul hs0]
      have hbound : C * (1 + s) * Real.exp (-(c*s)) * ((2:ℝ)^A * s^(2*A)) ≤ B := by
        have hmain : (1 + s) * s^(2*A) * Real.exp (-(c*s)) ≤ 2 * max 1 ((n.factorial:ℝ)/c^n) := by
          rcases lt_or_ge s 1 with hs1 | hs1
          · have hs2A : s^(2*A) ≤ 1 := Real.rpow_le_one hs0 (le_of_lt hs1) (by positivity)
            have he : Real.exp (-(c*s)) ≤ 1 :=
              Real.exp_le_one_iff.mpr (by nlinarith [hc.le, hs0])
            have h2A_nn : 0 ≤ s^(2*A) := Real.rpow_nonneg hs0 _
            calc (1 + s) * s^(2*A) * Real.exp (-(c*s)) ≤ 2 * 1 * 1 := by
                  apply mul_le_mul (mul_le_mul (by linarith) hs2A h2A_nn (by norm_num)) he
                    (Real.exp_pos _).le (by norm_num)
              _ = 2 := by norm_num
              _ ≤ 2 * max 1 ((n.factorial:ℝ)/c^n) := by
                  have h1 : (1:ℝ) ≤ max 1 ((n.factorial:ℝ)/c^n) := le_max_left _ _
                  nlinarith
          · have hs1pos : 0 < s := by linarith
            have hsm : s * s^(2*A) = s^(2*A+1) := by
              have hh := Real.rpow_add hs1pos (1:ℝ) (2*A)
              rw [Real.rpow_one, show (1:ℝ) + 2*A = 2*A + 1 by ring] at hh
              exact hh.symm
            have hcs : 0 < c * s := mul_pos hc hs1pos
            have hfac := Real.pow_div_factorial_le_exp (c*s) hcs.le n
            have hA0pos : 0 < (c*s)^n / (n.factorial:ℝ) := by positivity
            have hexp : Real.exp (-(c*s)) ≤ (n.factorial:ℝ) / (c*s)^n := by
              rw [Real.exp_neg, show (n.factorial:ℝ)/(c*s)^n = ((c*s)^n/(n.factorial:ℝ))⁻¹ by rw [inv_div]]
              rw [inv_le_inv₀ (Real.exp_pos _) hA0pos]
              exact hfac
            have hkey : s^(2*A+1) * Real.exp (-(c*s)) ≤ (n.factorial:ℝ)/c^n := by
              calc s^(2*A+1) * Real.exp (-(c*s))
                  ≤ s^(2*A+1) * ((n.factorial:ℝ)/(c*s)^n) :=
                    mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hs0 _)
                _ = ((n.factorial:ℝ)/c^n) * (s^(2*A+1) / s^n) := by rw [mul_pow]; ring
                _ = ((n.factorial:ℝ)/c^n) * s^(2*A+1 - n) := by
                    rw [← Real.rpow_natCast s n, ← Real.rpow_sub hs1pos]
                _ ≤ ((n.factorial:ℝ)/c^n) * 1 := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    apply Real.rpow_le_one_of_one_le_of_nonpos hs1
                    have hle : (2*A+1) ≤ (n:ℝ) := by rw [hn]; exact Nat.le_ceil (2*A+1)
                    linarith
                _ = (n.factorial:ℝ)/c^n := by ring
            calc (1 + s) * s^(2*A) * Real.exp (-(c*s))
                ≤ (2 * s) * s^(2*A) * Real.exp (-(c*s)) := by
                  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
                  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs0 _)
                  linarith
              _ = 2 * (s * s^(2*A)) * Real.exp (-(c*s)) := by ring
              _ = 2 * (s^(2*A+1) * Real.exp (-(c*s))) := by rw [hsm]; ring
              _ ≤ 2 * ((n.factorial:ℝ)/c^n) := mul_le_mul_of_nonneg_left hkey (by norm_num)
              _ ≤ 2 * max 1 ((n.factorial:ℝ)/c^n) :=
                  mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
        calc C * (1 + s) * Real.exp (-(c*s)) * ((2:ℝ)^A * s^(2*A))
            = C * (2:ℝ)^A * ((1+s) * s^(2*A) * Real.exp (-(c*s))) := by ring
          _ ≤ C * (2:ℝ)^A * (2 * max 1 ((n.factorial:ℝ)/c^n)) := by
                apply mul_le_mul_of_nonneg_left hmain
                exact mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) A)
          _ = B := by rw [hB]; ring
      calc |selU Q - 1|
          = |selU Q - 1| * (Real.log (2+Q))^A * ((Real.log (2+Q))^A)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A)), mul_one]
        _ ≤ (C * (1+s) * Real.exp (-(c*s)) * ((2:ℝ)^A * s^(2*A))) * ((Real.log (2+Q))^A)⁻¹ := by
              apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.rpow_nonneg hlog2Q0 A))
              calc |selU Q - 1| * (Real.log (2+Q))^A
                  ≤ (C * (1 + Real.sqrt (Real.log Q)) * Real.exp (-(c * Real.sqrt (Real.log Q)))) * (Real.log (2+Q))^A :=
                    mul_le_mul_of_nonneg_right (hdec Q hQ2) (Real.rpow_nonneg hlog2Q0 A)
                _ = C * (1 + s) * Real.exp (-(c*s)) * (Real.log (2+Q))^A := by rw [← hs]
                _ ≤ C * (1 + s) * Real.exp (-(c*s)) * ((2:ℝ)^A * s^(2*A)) := by
                    apply mul_le_mul_of_nonneg_left hpow_le
                    exact mul_nonneg (mul_nonneg hC.le (by positivity)) (Real.exp_pos _).le
        _ ≤ B * ((Real.log (2+Q))^A)⁻¹ :=
              mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr (Real.rpow_nonneg hlog2Q0 A))
        _ = B * (Real.log (2+Q))^(-A) := by rw [Real.rpow_neg hlog2Q0]
        _ ≤ max (c3 * (Real.log 4)^(A-3)) B * (Real.log (2+Q))^(-A) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hlog2Q0 _)

/-- Existence of a splitting power `M` for which the recursion still contracts:
`(1 - 1/M)^{-A} < 10/9`. -/
lemma exists_split_M (A : ℝ) (hA : 0 < A) :
    ∃ M : ℝ, 1 < M ∧ (9/10) * (1 - 1/M) ^ (-A) < 1 := by
  set c : ℝ := (10/9:ℝ) ^ (1/A) with hcdef
  have hc_gt1 : 1 < c := by
    rw [hcdef]
    exact Real.one_lt_rpow (by norm_num) (by positivity)
  have hcA : c ^ A = 10/9 := by
    rw [hcdef, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10/9)]
    rw [show 1/A * A = 1 by field_simp]
    rw [Real.rpow_one]
  have hdelta : 0 < c - 1 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (c - 1))
  have hNpos : 0 < N := by
    have h1 : (0:ℝ) < 1/(c-1) := by positivity
    have : (0:ℝ) < (N:ℝ) := lt_trans h1 hN
    exact_mod_cast this
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hkey : 1 / (N:ℝ) < c - 1 := by
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hdelta] at hN
    linarith
  have hratio : 1 + 1/(N:ℝ) < c := by linarith
  refine ⟨(N:ℝ) + 1, by linarith, ?_⟩
  have hMsimp : 1 - 1/((N:ℝ)+1) = (N:ℝ)/((N:ℝ)+1) := by
    field_simp
    ring
  have hxinv : ((N:ℝ)/((N:ℝ)+1))⁻¹ = 1 + 1/(N:ℝ) := by
    rw [inv_div]; field_simp
  have hpow : (1 - 1/((N:ℝ)+1)) ^ (-A) = (1 + 1/(N:ℝ)) ^ A := by
    have hxle : (0:ℝ) ≤ 1 - 1/((N:ℝ)+1) := by rw [hMsimp]; positivity
    rw [Real.rpow_neg hxle A, ← Real.inv_rpow hxle A, hMsimp, hxinv]
  have hlt : (1 + 1/(N:ℝ)) ^ A < (10/9:ℝ) := by
    have h := Real.rpow_lt_rpow (by positivity : (0:ℝ) ≤ 1 + 1/(N:ℝ)) hratio hA
    rwa [hcA] at h
  calc (9/10) * (1 - 1/((N:ℝ)+1)) ^ (-A) = (9/10) * (1 + 1/(N:ℝ)) ^ A := by rw [hpow]
    _ < (9/10) * (10/9) := by
        exact mul_lt_mul_of_pos_left hlt (by norm_num)
    _ = 1 := by norm_num

/-- Base case at exponent `A`: `|Tsel 1 Q| = |1 - selU Q|`. -/
lemma Tsel_one_bound_pow (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 1 ≤ Q → |Tsel 1 Q| ≤ c * LpowA A Q := by
  obtain ⟨c, hc, hb⟩ := selU_pow_bound A hA
  refine ⟨c, hc, fun Q hQ => ?_⟩
  have heq : Tsel 1 Q = 1 - selU Q := by
    rw [Tsel, Nat.totient_one, Nat.cast_one, div_one, selTheta_one_eq_selU]
  rw [heq]
  simpa [LpowA, abs_sub_comm] using hb Q hQ

/-- The large-divisor piece of the recursion, bounded with the trivial estimate for `T_d`,
general exponent `A` and general splitting power `M`. -/
lemma window_bound (A M : ℝ) (hM : 1 < M) (hA : 0 < A) :
    ∃ Kw : ℝ, 0 < Kw ∧ ∀ Q : ℝ, 1 ≤ Q →
      Q ^ (-(1/(2*M))) *
        (1000 + Real.log (2 + Q ^ ((M-1)/M)) * (1 + Real.log (2 + Q ^ ((M-1)/M))))
        * (Real.log (2 + Q)) ^ A ≤ Kw := by
  obtain ⟨K1, hK1pos, hK1⟩ := rpow_neg_mul_log_rpow_bounded (1/(2*M)) (A+2) (by positivity) (by linarith)
  obtain ⟨K2, hK2pos, hK2⟩ := rpow_neg_mul_log_rpow_bounded (1/(2*M)) A (by positivity) hA.le
  refine ⟨1002*K1 + 1000*K2 + 1, by positivity, ?_⟩
  intro Q hQ
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  set Ml : ℝ := Real.log (2 + Q) with hMldef
  set L : ℝ := Real.log (2 + Q ^ ((M-1)/M)) with hLdef
  have hMpos : 0 < M := by linarith
  have hMl_pos : 0 < Ml := by rw [hMldef]; exact Real.log_pos (by linarith)
  have hMl_ge1 : 1 ≤ Ml := by
    rw [hMldef]
    have h4 : Real.log 3 ≤ Real.log (2 + Q) := Real.log_le_log (by norm_num) (by linarith)
    have h5 : (1:ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three.le
    linarith
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    have h1 : (1:ℝ) ≤ Q ^ ((M-1)/M) :=
      Real.one_le_rpow hQ (div_nonneg (by linarith) hMpos.le)
    linarith
  have hLle : L ≤ Ml := by
    rw [hLdef, hMldef]
    apply Real.log_le_log (by have hpp := Real.rpow_nonneg hQpos.le ((M-1)/M); linarith)
    have h1 : Q ^ ((M-1)/M) ≤ Q := by
      have hExp : (M-1)/M ≤ 1 := by rw [div_le_one hMpos]; linarith
      have hle := Real.rpow_le_rpow_of_exponent_le hQ hExp
      rwa [Real.rpow_one] at hle
    linarith
  have hbracket : 1000 + L * (1 + L) ≤ 1002 * Ml^2 := by
    have h1 : L * (1 + L) ≤ Ml * (1 + Ml) :=
      mul_le_mul hLle (by linarith) (by linarith) hMl_pos.le
    have h2 : 1000 + Ml * (1 + Ml) ≤ 1002 * Ml^2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Ml - 1)
        (by linarith : (0:ℝ) ≤ 1001 * Ml + 1000)]
    linarith
  have h2A : Ml ^ 2 * Ml ^ A = Ml ^ (A + 2) := by
    rw [← Real.rpow_natCast Ml 2, mul_comm, ← Real.rpow_add hMl_pos]
    norm_num
  calc Q ^ (-(1/(2*M))) * (1000 + L * (1 + L)) * Ml ^ A
      ≤ Q ^ (-(1/(2*M))) * (1002 * Ml ^ 2) * Ml ^ A :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracket (Real.rpow_nonneg hQpos.le _))
          (Real.rpow_nonneg hMl_pos.le A)
    _ = 1002 * (Q ^ (-(1/(2*M))) * (Ml ^ 2 * Ml ^ A)) := by ring
    _ = 1002 * (Q ^ (-(1/(2*M))) * Ml ^ (A + 2)) := by rw [h2A]
    _ ≤ 1002 * K1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        simpa [hMldef] using hK1 Q hQ
    _ ≤ 1002 * K1 + 1000 * K2 + 1 := by linarith [hK2pos.le]

/-- The `d > Q^{1/M}` piece of the recursion, bounded with the trivial estimate for `T_d`. -/
lemma window_part_bound_gen {Q : ℝ} (hQ : 1 ≤ Q) {r : ℕ} (hr : 1 ≤ r) {Kw LY M A : ℝ}
    (hLYnn : 0 ≤ LY)
    (hwin : Q ^ (-(1/(2*M))) * (1000 + LY) * (Real.log (2 + Q)) ^ A ≤ Kw) :
    (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/M) < (d:ℝ)),
        ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
      + LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/M) < (d:ℝ)),
            ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ))
      ≤ sHalf r * Kw * LpowA A Q := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hXpos : 0 < Q ^ ((1:ℝ)/M) := Real.rpow_pos_of_pos hQpos _
  obtain ⟨ht1, ht2⟩ := divisorTail_bounds r hr (Q ^ ((1:ℝ)/M)) hXpos
  have hsqX : Real.sqrt (Q ^ ((1:ℝ)/M)) = Q ^ ((1:ℝ)/(2*M)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQpos.le]
    congr 1
    field_simp
  have hneg : Q ^ (-(1/(2*M))) = (Q ^ ((1:ℝ)/(2*M)))⁻¹ := by
    rw [show (-(1/(2*M)) : ℝ) = -((1:ℝ)/(2*M)) by ring]
    exact Real.rpow_neg hQpos.le _
  have hB : sHalf r / Real.sqrt (Q ^ ((1:ℝ)/M)) = sHalf r * Q ^ (-(1/(2*M))) := by
    rw [hsqX, hneg, div_eq_mul_inv]
  have hB2 : 1000 * (sHalf r / Real.sqrt (Q ^ ((1:ℝ)/M)))
      = sHalf r * (1000 * Q ^ (-(1/(2*M)))) := by rw [hB]; ring
  have hsHalf : 0 ≤ sHalf r := sHalf_nonneg r
  have h3 : (0:ℝ) < (Real.log (2 + Q)) ^ A :=
    Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A
  have hkey : Q ^ (-(1/(2*M))) * (1000 + LY) ≤ Kw * LpowA A Q := by
    have hLpow : LpowA A Q = ((Real.log (2+Q)) ^ A)⁻¹ := by
      rw [LpowA]; exact Real.rpow_neg (Real.log_nonneg (by linarith)) A
    rw [hLpow]
    calc Q ^ (-(1/(2*M))) * (1000 + LY)
        = (Q ^ (-(1/(2*M))) * (1000 + LY) * (Real.log (2+Q))^A) * ((Real.log (2+Q))^A)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h3), mul_one]
      _ ≤ Kw * ((Real.log (2+Q))^A)⁻¹ := mul_le_mul_of_nonneg_right hwin (by positivity)
  calc (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/M) < (d:ℝ)),
          ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
        + LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => Q ^ ((1:ℝ)/M) < (d:ℝ)),
              ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ))
      ≤ 1000 * (sHalf r / Real.sqrt (Q ^ ((1:ℝ)/M)))
        + LY * (sHalf r / Real.sqrt (Q ^ ((1:ℝ)/M))) :=
        add_le_add ht2 (mul_le_mul_of_nonneg_left ht1 hLYnn)
    _ = sHalf r * (Q ^ (-(1/(2*M))) * (1000 + LY)) := by rw [hB2, hB]; ring
    _ ≤ sHalf r * (Kw * LpowA A Q) := mul_le_mul_of_nonneg_left hkey hsHalf
    _ = sHalf r * Kw * LpowA A Q := by ring


/-- Main estimate at exponent `A`: `|T_r(Q)| ≤ K σ_{-1/2}(r) (log(2+Q))^{-A}` uniformly
in `Q ≥ 1`, `r ≥ 1`.  The induction is on `⌈Q⌉₊`, with the recursion sum split at
`X = Q^{1/M}` for an `M` chosen (depending on `A`) so that `(9/10)(1-1/M)^{-A} < 1`. -/
theorem Tsel_bound_pow (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ r : ℕ, 1 ≤ r →
      |Tsel r Q| ≤ K * sHalf r * LpowA A Q := by
  obtain ⟨M, hM1, hMr⟩ := exists_split_M A hA
  have hMpos : 0 < M := by linarith
  have h1M : 0 < 1 - 1/M := by
    rw [sub_pos, div_lt_one hMpos]; exact hM1
  set lam : ℝ := (1 - 1/M) ^ (-A) with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; exact Real.rpow_pos_of_pos h1M _
  have hden : 0 < 1 - (9/10) * lam := by rw [hlamdef]; linarith [hMr]
  obtain ⟨c1, hc1pos, hbase⟩ := Tsel_one_bound_pow A hA
  obtain ⟨Kw, hKwpos, hwin⟩ := window_bound A M hM1 hA
  set K : ℝ := max 1 (max c1 ((c1 + Kw) / (1 - (9/10) * lam))) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKc1 : c1 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbig : (c1 + Kw) / (1 - (9/10) * lam) ≤ K :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKineq : c1 + (9/10) * lam * K + Kw ≤ K := by
    have h1 : (1 - (9/10) * lam) * ((c1 + Kw) / (1 - (9/10) * lam)) ≤ (1 - (9/10) * lam) * K :=
      mul_le_mul_of_nonneg_left hKbig hden.le
    rw [mul_div_cancel₀ _ (ne_of_gt hden)] at h1
    linarith
  refine ⟨K, hKpos, ?_⟩
  have key : ∀ N : ℕ, ∀ r : ℕ, ∀ Q : ℝ, 1 ≤ Q → Nat.ceil Q ≤ N → 1 ≤ r →
      |Tsel r Q| ≤ K * sHalf r * LpowA A Q := by
    intro N
    induction N with
    | zero =>
      intro r Q hQ hN hr
      have hpos : 0 < Nat.ceil Q := Nat.ceil_pos.mpr (by linarith)
      omega
    | succ N ih =>
      intro r Q hQ hN hr
      rcases lt_or_ge (Nat.ceil Q) (N + 1) with hlt | hge
      · exact ih r Q hQ (by omega) hr
      · have hceil : Nat.ceil Q = N + 1 := le_antisymm hN hge
        have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
        have hLQnn : 0 ≤ LpowA A Q := (LpowA_pos hQ).le
        rcases eq_or_lt_of_le hr with h1 | h2
        · subst h1
          have hb := le_trans (hbase Q hQ) (mul_le_mul_of_nonneg_right hKc1 hLQnn)
          simpa [sHalf_one] using hb
        · set X : ℝ := Q ^ ((1:ℝ)/M) with hXeq
          have hXpos : 0 < X := by rw [hXeq]; exact Real.rpow_pos_of_pos hQpos _
          have hXleQ : X ≤ Q := by
            rw [hXeq]
            calc Q ^ ((1:ℝ)/M) ≤ Q ^ (1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hQ (by rw [div_le_one hMpos]; linarith)
              _ = Q := Real.rpow_one Q
          set LY : ℝ := Real.log (2 + Q ^ ((M-1)/M)) *
            (1 + Real.log (2 + Q ^ ((M-1)/M))) with hLYeq
          have hLYnn : 0 ≤ LY := by
            rw [hLYeq]
            have h2' : (1:ℝ) ≤ 2 + Q ^ ((M-1)/M) := by
              have hpp := Real.rpow_pos_of_pos hQpos ((M-1)/M)
              linarith
            have hlog2 : 0 ≤ Real.log (2 + Q ^ ((M-1)/M)) := Real.log_nonneg h2'
            exact mul_nonneg hlog2 (by linarith)
          rw [Tsel_recursion Q r hr]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have hsplit : (∑ d ∈ r.divisors,
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              = (∑ d ∈ r.divisors.filter (fun d : ℕ => d = 1),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                + (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                + (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|) := by
            rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
              ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun d _ => ?_)
            by_cases hd1 : d = 1
            · subst hd1
              simp
            · by_cases hd2 : (d:ℝ) ≤ X
              · rw [if_neg (by simpa using hd1), if_pos ⟨hd1, hd2⟩,
                  if_neg (fun h => not_le_of_gt h.2 hd2)]
                ring
              · rw [if_neg (by simpa using hd1), if_neg (fun h => hd2 h.2),
                  if_pos ⟨hd1, not_le.mp hd2⟩]
                ring
          rw [hsplit]
          have hpiece1 : (∑ d ∈ r.divisors.filter (fun d : ℕ => d = 1),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              ≤ c1 * LpowA A Q := by
            have hfil : r.divisors.filter (fun d : ℕ => d = 1) = {(1:ℕ)} := by
              ext d
              simp only [Finset.mem_filter, Finset.mem_singleton]
              constructor
              · intro h; exact h.2
              · intro h
                subst h
                exact ⟨Nat.one_mem_divisors.mpr (by omega), rfl⟩
            rw [hfil, Finset.sum_singleton]
            simpa using hbase Q hQ
          have hpiece2 : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              ≤ K * lam * LpowA A Q * ((9/10) * sHalf r) := by
            have hKL : 0 ≤ K * lam * LpowA A Q :=
              mul_nonneg (mul_nonneg hKpos.le hlampos.le) hLQnn
            have hpw : ∀ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  ≤ K * lam * LpowA A Q *
                      (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) := by
              intro d hd
              simp only [Finset.mem_filter] at hd
              obtain ⟨hdvd, hd1', hdle⟩ := hd
              have hdpos : 0 < d := Nat.pos_of_mem_divisors hdvd
              have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
              have h2d : 2 ≤ d := by omega
              have hw : 0 ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) := by positivity
              have hdiv1 : 1 ≤ Q/(d:ℝ) := by
                rw [le_div_iff₀ hdR]
                calc (1:ℝ) * (d:ℝ) = (d:ℝ) := one_mul _
                  _ ≤ X := hdle
                  _ ≤ Q := hXleQ
              have hQge2 : (2:ℝ) ≤ Q :=
                le_trans (by exact_mod_cast h2d : (2:ℝ) ≤ (d:ℝ)) (le_trans hdle hXleQ)
              have h2le : (2:ℝ) ≤ (Nat.ceil Q : ℝ) := le_trans hQge2 (Nat.le_ceil Q)
              have hN1 : 1 ≤ N := by
                have h2N : (2:ℕ) ≤ Nat.ceil Q := by exact_mod_cast h2le
                omega
              have hceil' : Nat.ceil (Q/(d:ℝ)) ≤ N := by
                rw [Nat.ceil_le, div_le_iff₀ hdR]
                have h1 : Q ≤ ((N:ℝ)+1) := by
                  have h := Nat.le_ceil Q
                  rw [hceil] at h
                  push_cast at h
                  exact h
                have h2' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast h2d
                have hNd1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
                have hmul : (N:ℝ) * 2 ≤ (N:ℝ) * (d:ℝ) :=
                  mul_le_mul_of_nonneg_left h2' (by positivity)
                nlinarith [h1, hmul, hNd1]
              have hih := ih d (Q/(d:ℝ)) hdiv1 hceil' (by omega : 1 ≤ d)
              have hlam : LpowA A (Q/(d:ℝ)) ≤ lam * LpowA A Q := by
                have hlogr := log_ratio_gen hQ (by omega : 1 ≤ d) hM1.le hdle
                have hb : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
                have hb' : 0 < (1 - 1/M) * Real.log (2 + Q) := mul_pos h1M hb
                rw [LpowA, LpowA, hlamdef]
                rw [← Real.mul_rpow h1M.le hb.le]
                exact Real.rpow_le_rpow_of_nonpos hb' hlogr (by linarith)
              calc |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  = ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * |Tsel d (Q/(d:ℝ))| := by
                    rw [abs_mul, abs_of_nonneg hw]
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      (K * sHalf d * LpowA A (Q/(d:ℝ))) := mul_le_mul_of_nonneg_left hih hw
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      (K * sHalf d * (lam * LpowA A Q)) := by
                    apply mul_le_mul_of_nonneg_left _ hw
                    exact mul_le_mul_of_nonneg_left hlam
                      (mul_nonneg hKpos.le (sHalf_nonneg d))
                _ = K * lam * LpowA A Q *
                      (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) := by ring
            calc (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                    K * lam * LpowA A Q *
                      (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) :=
                  Finset.sum_le_sum hpw
              _ = K * lam * LpowA A Q *
                    (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                      ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d) := by
                  rw [Finset.mul_sum]
              _ ≤ K * lam * LpowA A Q * ((9/10) * sHalf r) := by
                  apply mul_le_mul_of_nonneg_left _ hKL
                  calc (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ (d:ℝ) ≤ X),
                          ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d)
                      ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => 2 ≤ d),
                          ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * sHalf d := by
                        apply Finset.sum_le_sum_of_subset_of_nonneg
                        · intro d hd
                          simp only [Finset.mem_filter] at hd ⊢
                          have h1d : 1 ≤ d := Nat.pos_of_mem_divisors hd.1
                          exact ⟨hd.1, by omega⟩
                        · intro d hd _
                          have hdpos : (0:ℝ) < (d:ℝ) := by
                            exact_mod_cast Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
                          have hsnn : 0 ≤ sHalf d := sHalf_nonneg d
                          positivity
                    _ ≤ (9/10) * sHalf r := diag_weighted_sum_le_alt hr
          have hpiece3 : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
              ≤ sHalf r * Kw * LpowA A Q := by
            have hpw : ∀ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                    + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ) := by
              intro d hd
              simp only [Finset.mem_filter] at hd
              obtain ⟨hdvd, hd1', hdX⟩ := hd
              have hdpos : 0 < d := Nat.pos_of_mem_divisors hdvd
              have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
              have hw : 0 ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) := by positivity
              have hqnn : 0 ≤ Q/(d:ℝ) := by positivity
              have htriv := Tsel_abs_le hqnn (by omega : 1 ≤ d)
              have hXlt : Q ^ ((1:ℝ)/M) < (d:ℝ) := by rw [← hXeq]; exact hdX
              have hqle : Q/(d:ℝ) ≤ Q ^ ((M-1)/M) := by
                rw [div_le_iff₀ hdR]
                have hprod : Q ^ ((M-1)/M) * Q ^ ((1:ℝ)/M) = Q := by
                  rw [← Real.rpow_add hQpos]
                  have : (M-1)/M + 1/M = 1 := by field_simp; ring
                  rw [this, Real.rpow_one]
                calc Q = Q ^ ((M-1)/M) * Q ^ ((1:ℝ)/M) := hprod.symm
                  _ ≤ Q ^ ((M-1)/M) * (d:ℝ) :=
                      mul_le_mul_of_nonneg_left hXlt.le (Real.rpow_nonneg hQpos.le _)
              have hlogle : Real.log (2 + Q/(d:ℝ)) ≤ Real.log (2 + Q ^ ((M-1)/M)) :=
                Real.log_le_log (by linarith) (by linarith)
              have hLYlog : Real.log (2 + Q/(d:ℝ)) * (1 + Real.log (2 + Q/(d:ℝ))) ≤ LY := by
                rw [hLYeq]
                have h0 : 0 ≤ Real.log (2 + Q/(d:ℝ)) := Real.log_nonneg (by linarith)
                have h2' : 0 ≤ Real.log (2 + Q ^ ((M-1)/M)) := by
                  apply Real.log_nonneg
                  have hpp := Real.rpow_pos_of_pos hQpos ((M-1)/M)
                  linarith
                have h4 : (1:ℝ) + Real.log (2 + Q/(d:ℝ))
                    ≤ 1 + Real.log (2 + Q ^ ((M-1)/M)) := by linarith
                exact mul_le_mul hlogle h4 (by linarith) h2'
              have htot : ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                    ((d:ℝ)/(Nat.totient d : ℝ) + LY)
                  = ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                    + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ) := by
                have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdR
                have hφd : (Nat.totient d : ℝ) ≠ 0 := by
                  have : 0 < Nat.totient d := Nat.totient_pos.mpr hdpos
                  exact_mod_cast this.ne'
                field_simp
              calc |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|
                  = ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * |Tsel d (Q/(d:ℝ))| := by
                    rw [abs_mul, abs_of_nonneg hw]
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      ((d:ℝ)/(Nat.totient d : ℝ)
                        + Real.log (2 + Q/(d:ℝ)) * (1 + Real.log (2 + Q/(d:ℝ)))) :=
                    mul_le_mul_of_nonneg_left htriv hw
                _ ≤ ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) *
                      ((d:ℝ)/(Nat.totient d : ℝ) + LY) := by
                    apply mul_le_mul_of_nonneg_left _ hw
                    linarith
                _ = ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                      + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ) := htot
            have hsub : r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ))
                ⊆ r.divisors.filter (fun d : ℕ => X < (d:ℝ)) := by
              intro d hd
              simp only [Finset.mem_filter] at hd ⊢
              exact ⟨hd.1, hd.2.2⟩
            have hsum1' : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
                ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
            have hsum2' : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ))
                ≤ LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ)) := by
              rw [Finset.mul_sum]
              have hcong : (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ))
                  = ∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    LY * (((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ)) :=
                Finset.sum_congr rfl (fun d _ => by ring)
              rw [hcong]
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro d _ _
              exact mul_nonneg hLYnn (by positivity)
            have hwin' : Q ^ (-(1/(2*M))) * (1000 + LY) * (Real.log (2 + Q)) ^ A ≤ Kw := by
              rw [hLYeq]
              exact hwin Q hQ
            calc (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    |((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * Tsel d (Q/(d:ℝ))|)
                ≤ ∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    (((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ)
                      + ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ)) :=
                  Finset.sum_le_sum hpw
              _ = (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
                  + (∑ d ∈ r.divisors.filter (fun d : ℕ => d ≠ 1 ∧ X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 * LY / (d:ℝ)) :=
                  Finset.sum_add_distrib
              _ ≤ (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
                  + LY * (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
                    ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ)) :=
                  add_le_add hsum1' hsum2'
              _ ≤ sHalf r * Kw * LpowA A Q :=
                  window_part_bound_gen hQ hr hLYnn hwin'
          exact arith_assembly (sHalf_ge_one hr) hLQnn hc1pos hKineq hpiece1 hpiece2 hpiece3
  intro Q hQ r hr
  exact key (Nat.ceil Q) r Q hQ le_rfl hr

/-- **Target lemma.**  The `O(σ_{-1/2}(r)(log 2Q)^{-3})` asymptotic for `Θ(Q,r)` holds
with an arbitrary exponent `-A`, `A > 0`. -/
theorem selTheta_asymptotic_pow (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ r : ℕ, 1 ≤ r →
      |selTheta Q r - (r : ℝ) / (Nat.totient r : ℝ)| ≤
        C * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.log (2 + Q)) ^ (-A) := by
  obtain ⟨K, hK, hbd⟩ := Tsel_bound_pow A hA
  refine ⟨K, hK, ?_⟩
  intro Q hQ r hr
  have h := hbd Q hQ r hr
  simpa [Tsel, sHalf, LpowA, abs_sub_comm] using h

end

end Work.LinnikAreas.Density4.ThetaPow
