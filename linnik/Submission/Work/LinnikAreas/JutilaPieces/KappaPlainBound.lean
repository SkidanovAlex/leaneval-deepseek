import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.MobiusKappaAux
import Submission.Work.LinnikAreas.Density4.KappaSum.log_pow_le_const_mul_sqrt

namespace Work.LinnikAreas.JutilaPieces

open Finset
open scoped BigOperators
open Work.LinnikAreas.Density4 (kappaSum kappaLogSum kappaR sHalf sHalf_ge_one sHalf_nonneg)

noncomputable section

lemma kappaR_one_J : kappaR 1 = 1 := by simp [kappaR]

lemma kappaSum_bound (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
      |kappaSum ⌊Q⌋₊ r| ≤ C * sHalf r * (Real.log (2 + Q)) ^ (-B) := by
  obtain ⟨Cd, hCdpos, hdiff⟩ := kappaLogSum_diff (2 * B) (by linarith)
  obtain ⟨KL, hKLpos, hlog⟩ := Work.LinnikAreas.Density4.KappaSum.log_pow_le_const_mul_sqrt B hB
  have h4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h4Bpos : 0 < (Real.log 4) ^ B := Real.rpow_pos_of_pos h4pos B
  have hKpos : 0 < 2 * Cd + 1 + 2 * KL := by linarith
  refine ⟨max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL), ?_, ?_⟩
  · exact lt_max_of_lt_left h4Bpos
  · intro Q r hQ hr
    have hsh : 1 ≤ sHalf r := sHalf_ge_one hr
    have hshnn : 0 ≤ sHalf r := sHalf_nonneg r
    have hlog2Qpos : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
    have hCpos : 0 < max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) :=
      lt_of_lt_of_le h4Bpos (le_max_left _ _)
    have hCL : 0 ≤ (Real.log (2 + Q)) ^ (-B) := Real.rpow_nonneg hlog2Qpos.le _
    rcases lt_or_ge Q 2 with hQ2 | hQ2
    · -- small case: `⌊Q⌋₊ = 1`
      have hfl : ⌊Q⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith)]
        constructor <;> push_cast <;> linarith
      have hsum1 : kappaSum 1 r = 1 := by
        unfold kappaSum
        rw [Finset.Icc_self]
        have hfil : (Finset.filter (fun n => Nat.Coprime n r) ({1} : Finset ℕ)) = {1} :=
          Finset.filter_true_of_mem (fun x hx => by
            rw [Finset.mem_singleton] at hx; subst hx; exact Nat.coprime_one_left r)
        rw [hfil, Finset.sum_singleton, kappaR_one_J]
        norm_num
      rw [hfl, hsum1, abs_one]
      have h24 : Real.log (2 + Q) ≤ Real.log 4 :=
        Real.log_le_log (by linarith) (by linarith)
      have hquot : (1:ℝ) ≤ Real.log 4 / Real.log (2 + Q) := (one_le_div hlog2Qpos).mpr h24
      have hone : (1:ℝ) ≤ (Real.log 4 / Real.log (2 + Q)) ^ B := Real.one_le_rpow hquot hB.le
      have hkey : (1:ℝ) ≤ (Real.log 4) ^ B * (Real.log (2 + Q)) ^ (-B) := by
        rwa [Real.div_rpow h4pos.le hlog2Qpos.le, div_eq_mul_inv,
          ← Real.rpow_neg hlog2Qpos.le] at hone
      refine le_trans hkey ?_
      have step1 : (Real.log 4) ^ B * (Real.log (2 + Q)) ^ (-B)
          ≤ max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) * (Real.log (2 + Q)) ^ (-B) :=
        mul_le_mul_of_nonneg_right (le_max_left ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL)) hCL
      have step2 : max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) * (Real.log (2 + Q)) ^ (-B)
          ≤ max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) * sHalf r
              * (Real.log (2 + Q)) ^ (-B) := by
        have h1 : max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL)
            ≤ max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) * sHalf r :=
          le_mul_of_one_le_right (le_of_lt hCpos) hsh
        calc max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) * (Real.log (2 + Q)) ^ (-B)
            ≤ (max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) * sHalf r)
                * (Real.log (2 + Q)) ^ (-B) := mul_le_mul_of_nonneg_right h1 hCL
          _ = max ((Real.log 4) ^ B) (2 * Cd + 1 + 2 * KL) * sHalf r
                * (Real.log (2 + Q)) ^ (-B) := by ring
      exact le_trans step1 step2
    · -- main case `Q ≥ 2`: the `c`-trick
      have hQm1pos : 0 < Q - 1 := by linarith
      have hlogBpos : 0 < (Real.log (2 + Q)) ^ (-B) := Real.rpow_pos_of_pos hlog2Qpos _
      set c : ℝ := 1 + (Real.log (2 + Q)) ^ (-B) with hcdef
      have hc1 : 1 < c := by rw [hcdef]; linarith
      have hlogBge1 : 1 ≤ Real.log (2 + Q) := by
        have h3 : (1:ℝ) ≤ Real.log 3 :=
          (Real.le_log_iff_exp_le (by norm_num)).mpr Real.exp_one_lt_three.le
        have hle : Real.log 3 ≤ Real.log (2 + Q) := Real.log_le_log (by norm_num) (by linarith)
        linarith
      have hδ1 : (Real.log (2 + Q)) ^ (-B) ≤ 1 := by
        rw [Real.rpow_neg hlog2Qpos.le]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow hlogBge1 hB.le)
      have hlogc_ge : (Real.log (2 + Q)) ^ (-B) / 2 ≤ Real.log c := by
        have hcpos : 0 < c := by rw [hcdef]; linarith
        have h1 := Real.one_sub_inv_le_log_of_pos hcpos
        have h2 : 1 - c⁻¹ = (Real.log (2 + Q)) ^ (-B) / c := by
          have hcle : c - 1 = (Real.log (2 + Q)) ^ (-B) := by rw [hcdef]; ring
          have h3 : 1 - c⁻¹ = (c - 1) / c := by
            rw [sub_div, div_self (ne_of_gt hcpos)]
            ring
          rw [h3, hcle]
        rw [h2, hcdef] at h1
        have h3 : (Real.log (2 + Q)) ^ (-B) / (1 + (Real.log (2 + Q)) ^ (-B))
            ≥ (Real.log (2 + Q)) ^ (-B) / 2 := by
          rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 2)
            (by linarith : (0:ℝ) < 1 + (Real.log (2 + Q)) ^ (-B))]
          nlinarith [hlogBpos.le, hδ1]
        linarith
      have hlogcpos : 0 < Real.log c := Real.log_pos hc1
      have hlogc_le : Real.log c ≤ (Real.log (2 + Q)) ^ (-B) := by
        have h1 := Real.log_le_sub_one_of_pos (by rw [hcdef]; linarith : 0 < c)
        rw [hcdef] at h1
        linarith
      have hid := kappaSum_c_trick Q c hQ hc1 r
      have h1 : |kappaLogSum (Q * c) r - kappaLogSum Q r|
          ≤ Cd * sHalf r * (Real.log (2 + Q)) ^ (-(2 * B)) := by
        have hmin : min Q (Q * c) = Q := min_eq_left (by nlinarith [hQ, hc1.le])
        have hQc : 1 ≤ Q * c := by nlinarith [hQ, hc1.le]
        have := hdiff Q (Q * c) r hQ hQc hr
        rw [hmin] at this
        rwa [abs_sub_comm] at this
      have h2 : |∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
            (ArithmeticFunction.moebius n : ℝ) / kappaR n * Real.log (Q * c / (n : ℝ))|
          ≤ Real.log c * (Real.log c + 1 / (Q - 1)) := by
        have hw := kappaSum_window_bound Q c hQ hc1 r
        refine le_trans hw ?_
        have hfloor : Q - 1 ≤ (⌊Q⌋₊ : ℝ) := by
          have h := Nat.lt_floor_add_one Q
          linarith
        have hnum : (0:ℝ) ≤ ((⌊Q * c⌋₊ : ℕ) : ℝ) := by positivity
        have hfloorpos2 : (0:ℝ) < (((⌊Q⌋₊ : ℕ)) : ℝ) := by
          have h1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
          exact_mod_cast (by omega : 0 < ⌊Q⌋₊)
        have hratio : ((⌊Q * c⌋₊ : ℝ)) / ((⌊Q⌋₊ : ℝ)) ≤ Q * c / (Q - 1) := by
          rw [div_le_div_iff₀ hfloorpos2 hQm1pos]
          have h1 : ((⌊Q * c⌋₊ : ℕ) : ℝ) ≤ Q * c := Nat.floor_le (by positivity)
          nlinarith [h1, hfloor, hnum, hQm1pos]
        have hfloorpos : (0:ℝ) < (((⌊Q⌋₊ : ℕ)) : ℝ) := by
          have h1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
          exact_mod_cast (by omega : 0 < ⌊Q⌋₊)
        have hnumpos : (0:ℝ) < (((⌊Q * c⌋₊ : ℕ)) : ℝ) := by
          have h2 : (1:ℕ) ≤ ⌊Q * c⌋₊ :=
            Nat.le_floor (by push_cast; nlinarith [hQ, hc1.le])
          exact_mod_cast (by omega : 0 < ⌊Q * c⌋₊)
        have hlogratio : Real.log (((⌊Q * c⌋₊ : ℝ)) / ((⌊Q⌋₊ : ℝ))) ≤ Real.log (Q * c / (Q - 1)) :=
          Real.log_le_log (div_pos hnumpos hfloorpos) hratio
        have hsplit : Real.log (Q * c / (Q - 1)) = Real.log c + Real.log (Q / (Q - 1)) := by
          rw [show Q * c / (Q - 1) = c * (Q / (Q - 1)) by field_simp]
          exact Real.log_mul (ne_of_gt (lt_trans zero_lt_one hc1)) (by positivity)
        have hlast : Real.log (Q / (Q - 1)) ≤ 1 / (Q - 1) := by
          have hpos : (0:ℝ) < Q / (Q - 1) := by
            apply div_pos <;> linarith
          have h := Real.log_le_sub_one_of_pos hpos
          rw [div_sub_one (by linarith : (Q - 1) ≠ 0)] at h
          rw [show Q - (Q - 1) = 1 by ring] at h
          simpa using h
        have h3 := mul_le_mul_of_nonneg_left (le_trans hlogratio (le_of_eq hsplit)) (le_of_lt hlogcpos)
        have h4 := mul_le_mul_of_nonneg_left hlast (le_of_lt hlogcpos)
        linarith [h3, h4]
      have hb : |Real.log c * kappaSum ⌊Q⌋₊ r|
          ≤ Cd * sHalf r * (Real.log (2 + Q)) ^ (-(2 * B))
            + Real.log c * (Real.log c + 1 / (Q - 1)) := by
        have hident : Real.log c * kappaSum ⌊Q⌋₊ r
            = kappaLogSum (Q * c) r - kappaLogSum Q r
              - ∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                  (ArithmeticFunction.moebius n : ℝ) / kappaR n * Real.log (Q * c / (n : ℝ)) := by
          rw [hid]; ring
        rw [hident]
        have htri : |kappaLogSum (Q * c) r - kappaLogSum Q r
              - ∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                  (ArithmeticFunction.moebius n : ℝ) / kappaR n * Real.log (Q * c / (n : ℝ))|
            ≤ |kappaLogSum (Q * c) r - kappaLogSum Q r|
              + |∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                  (ArithmeticFunction.moebius n : ℝ) / kappaR n * Real.log (Q * c / (n : ℝ))| := by
          have h := abs_add_le (kappaLogSum (Q * c) r - kappaLogSum Q r)
            (-(∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                  (ArithmeticFunction.moebius n : ℝ) / kappaR n * Real.log (Q * c / (n : ℝ))))
          simpa [sub_eq_add_neg, abs_neg] using h
        linarith [htri, h1, h2]
      have hmain : |kappaSum ⌊Q⌋₊ r| ≤ 2 * Cd * sHalf r * (Real.log (2 + Q)) ^ (-B)
          + (Real.log c + 1 / (Q - 1)) := by
        have hdiv : |kappaSum ⌊Q⌋₊ r| = |Real.log c * kappaSum ⌊Q⌋₊ r| / Real.log c := by
          rw [abs_mul, abs_of_pos hlogcpos]
          field_simp
        rw [hdiv]
        refine le_trans (div_le_div_of_nonneg_right hb hlogcpos.le) ?_
        rw [add_div]
        have hlogB2 : (Real.log (2 + Q)) ^ (-(2 * B)) * (Real.log (2 + Q)) ^ B
            = (Real.log (2 + Q)) ^ (-B) := by
          rw [← Real.rpow_add hlog2Qpos]
          congr 1
          ring
        have hinv : 1 / Real.log c ≤ 2 * (Real.log (2 + Q)) ^ B := by
          have h1 : 1 / Real.log c ≤ 1 / ((Real.log (2 + Q)) ^ (-B) / 2) :=
            one_div_le_one_div_of_le (by positivity) hlogc_ge
          rw [one_div_div] at h1
          have h2 : 2 / (Real.log (2 + Q)) ^ (-B) = 2 * (Real.log (2 + Q)) ^ B := by
            rw [Real.rpow_neg hlog2Qpos.le]
            field_simp
          linarith [h1, le_of_eq h2]
        have hstep : Cd * sHalf r * (Real.log (2 + Q)) ^ (-(2 * B)) / Real.log c
            ≤ 2 * Cd * sHalf r * (Real.log (2 + Q)) ^ (-B) := by
          calc Cd * sHalf r * (Real.log (2 + Q)) ^ (-(2 * B)) / Real.log c
              = Cd * sHalf r * (Real.log (2 + Q)) ^ (-(2 * B)) * (1 / Real.log c) := by ring
            _ ≤ Cd * sHalf r * (Real.log (2 + Q)) ^ (-(2 * B))
                  * (2 * (Real.log (2 + Q)) ^ B) :=
                mul_le_mul_of_nonneg_left hinv
                  (mul_nonneg (mul_nonneg hCdpos.le hshnn) (Real.rpow_nonneg hlog2Qpos.le _))
            _ = 2 * Cd * sHalf r
                  * ((Real.log (2 + Q)) ^ (-(2 * B)) * (Real.log (2 + Q)) ^ B) := by ring
            _ = 2 * Cd * sHalf r * (Real.log (2 + Q)) ^ (-B) := by rw [hlogB2]
        have hcancel : (Real.log c * (Real.log c + 1 / (Q - 1))) / Real.log c
            = Real.log c + 1 / (Q - 1) := by
          field_simp
        rw [hcancel]
        linarith [hstep]
      refine le_trans hmain ?_
      have hwin : Real.log c + 1 / (Q - 1) ≤ (1 + 2 * KL) * (Real.log (2 + Q)) ^ (-B) := by
        have h2 : 1 / (Q - 1) ≤ 2 * KL * (Real.log (2 + Q)) ^ (-B) := by
          have h3 : (Real.log (2 + Q)) ^ B ≤ KL * Q := by
            have h := hlog Q hQ
            have hsqQ : Real.sqrt Q ≤ Q := by
              have hsq : Real.sqrt (Q ^ 2) = Q := Real.sqrt_sq (by linarith : (0:ℝ) ≤ Q)
              calc Real.sqrt Q ≤ Real.sqrt (Q ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
                _ = Q := hsq
            have hsq : KL * Real.sqrt Q ≤ KL * Q :=
              mul_le_mul_of_nonneg_left hsqQ hKLpos.le
            linarith
          have h4 : 1 / Q ≤ KL * (Real.log (2 + Q)) ^ (-B) := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < Q)]
            have h5 := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hlog2Qpos.le (-B))
            have h6 : (Real.log (2 + Q)) ^ B * (Real.log (2 + Q)) ^ (-B) = 1 := by
              rw [← Real.rpow_add hlog2Qpos]
              norm_num
            rw [h6] at h5
            nlinarith [h5]
          have h5 : 1 / (Q - 1) ≤ 2 / Q := by
            rw [div_le_div_iff₀ hQm1pos (by linarith : (0:ℝ) < Q)]
            linarith
          have h5' : 2 / Q ≤ 2 * (1 / Q) := le_of_eq (div_eq_mul_one_div 2 Q)
          have h6 : 2 * (1 / Q) ≤ 2 * (KL * (Real.log (2 + Q)) ^ (-B)) :=
            mul_le_mul_of_nonneg_left h4 (by norm_num)
          have h7 : 2 * (KL * (Real.log (2 + Q)) ^ (-B)) = 2 * KL * (Real.log (2 + Q)) ^ (-B) := by
            ring
          linarith [h5, h5', h6, h7]
        linarith [hlogc_le, h2]
      have hwin2 : Real.log c + 1 / (Q - 1)
          ≤ (1 + 2 * KL) * sHalf r * (Real.log (2 + Q)) ^ (-B) := by
        refine le_trans hwin ?_
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hsh) hCL
      have hcomb : 2 * Cd * sHalf r * (Real.log (2 + Q)) ^ (-B) + (Real.log c + 1 / (Q - 1))
          ≤ (2 * Cd + 1 + 2 * KL) * sHalf r * (Real.log (2 + Q)) ^ (-B) := by
        have hexpand : (2 * Cd + 1 + 2 * KL) * sHalf r * (Real.log (2 + Q)) ^ (-B)
            = 2 * Cd * sHalf r * (Real.log (2 + Q)) ^ (-B)
              + (1 + 2 * KL) * sHalf r * (Real.log (2 + Q)) ^ (-B) := by ring
        linarith [hwin2, hexpand]
      refine le_trans hcomb ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hshnn) hCL

end

end Work.LinnikAreas.JutilaPieces
