import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.MobiusKappaAux

import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.MobiusKappaAux

/-!
# The unweighted `1/κ`-weighted Möbius sum

`kappaSum_bound_pow` : for every `E > 0`, `Σ_{n ≤ N, (n,r)=1} μ(n)/κ(n) = O(σ_{-1/2}(r)·(log(2+Q))^{-E})`,
obtained from the Selberg-diagonalisation inputs of `MobiusKappaAux` by the `c`-trick
(comparing the smoothed sums `kappaLogSum` at the scales `Q` and `Q(1+δ)`).
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas.JutilaPieces

noncomputable section

lemma one_le_log_two_add' {Q : ℝ} (hQ : 1 ≤ Q) : (1:ℝ) ≤ Real.log (2 + Q) := by
  have h4 : Real.log 3 ≤ Real.log (2 + Q) := Real.log_le_log (by norm_num) (by linarith)
  have h5 : (1:ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three.le
  linarith

lemma one_le_log_four : (1:ℝ) ≤ Real.log 4 := by
  have h4 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h5 : (1:ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr Real.exp_one_lt_three.le
  linarith

theorem kappaSum_bound_pow (E : ℝ) (hE : 0 < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
      |Work.LinnikAreas.Density4.kappaSum ⌊Q⌋₊ r|
        ≤ C * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + Q)) ^ (-E) := by
  obtain ⟨Kd, hKdpos, hdiff⟩ := kappaLogSum_diff (2*E) (by linarith)
  obtain ⟨Kinv, hKinvpos, hinv⟩ := inv_pred_le_log_rpow E hE
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h4E : 0 ≤ (Real.log 4)^E := Real.rpow_nonneg hlog4pos.le E
  refine ⟨2*Kd + (1 + Kinv) + ((Real.log 4)^E + 1), by positivity, ?_⟩
  intro Q r hQ hr
  set C : ℝ := 2*Kd + (1 + Kinv) + ((Real.log 4)^E + 1) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; nlinarith [h4E, hKdpos, hKinvpos]
  have hCE : (Real.log 4)^E ≤ C := by
    rw [hCdef]; nlinarith [h4E, hKdpos, hKinvpos]
  have hC1 : 2*Kd ≤ C := by rw [hCdef]; nlinarith [h4E, hKdpos, hKinvpos]
  have hC2 : 1 + Kinv ≤ C := by rw [hCdef]; nlinarith [h4E, hKdpos, hKinvpos]
  have hsh1 : 1 ≤ Work.LinnikAreas.Density4.sHalf r := Work.LinnikAreas.Density4.sHalf_ge_one hr
  have hshnn : 0 ≤ Work.LinnikAreas.Density4.sHalf r := Work.LinnikAreas.Density4.sHalf_nonneg r
  have hlog2Q1 : 1 ≤ Real.log (2 + Q) := one_le_log_two_add' hQ
  have hlog2Qpos : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
  rcases lt_or_ge Q 2 with hQlt | hQge
  · have hfl : ⌊Q⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> push_cast <;> linarith
    rw [hfl]
    have hsum1 : Work.LinnikAreas.Density4.kappaSum 1 r = 1 := by
      rw [Work.LinnikAreas.Density4.kappaSum, Finset.Icc_self]
      rw [Finset.filter_true_of_mem (fun x hx => by
        rw [Finset.mem_singleton] at hx; subst hx; exact Nat.coprime_one_left r)]
      rw [Finset.sum_singleton]
      simp [Work.LinnikAreas.Density4.kappaR]
    rw [hsum1, abs_one]
    have hlogQle4 : Real.log (2 + Q) ≤ Real.log 4 :=
      Real.log_le_log (by linarith) (by linarith)
    have hpow4 : (Real.log 4)^(-E) ≤ (Real.log (2 + Q))^(-E) :=
      Real.rpow_le_rpow_of_nonpos hlog2Qpos hlogQle4 (by linarith)
    have hkey : (1:ℝ) ≤ (Real.log 4)^E * (Real.log (2 + Q))^(-E) := by
      have hEq : (Real.log 4)^E * (Real.log 4)^(-E) = 1 := by
        rw [← Real.rpow_add hlog4pos]; norm_num
      calc (1:ℝ) = (Real.log 4)^E * (Real.log 4)^(-E) := hEq.symm
        _ ≤ (Real.log 4)^E * (Real.log (2 + Q))^(-E) :=
            mul_le_mul_of_nonneg_left hpow4 (Real.rpow_nonneg hlog4pos.le E)
    refine le_trans hkey ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlog2Qpos.le _)
    nlinarith [hCE, hsh1, hCpos]
  · have hQ2 : 2 ≤ Q := hQge
    have hQm1pos : 0 < Q - 1 := by linarith
    set δ : ℝ := (Real.log (2 + Q))^(-E) with hδdef
    have hδpos' : 0 < δ := Real.rpow_pos_of_pos hlog2Qpos _
    have hδle1' : δ ≤ 1 := by
      rw [hδdef, Real.rpow_neg hlog2Qpos.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow hlog2Q1 hE.le)
    set c : ℝ := 1 + δ with hcdef
    have hc1 : 1 < c := by rw [hcdef]; linarith
    have hcpos : 0 < c := by linarith
    have hlogcpos : 0 < Real.log c := Real.log_pos hc1
    have hlogc_le : Real.log c ≤ δ := by
      have h := Real.log_le_sub_one_of_pos hcpos
      rw [hcdef] at h; linarith
    have hlogc_ge : δ/2 ≤ Real.log c := by
      have h := Real.one_sub_inv_le_log_of_pos hcpos
      have h2 : 1 - c⁻¹ = δ/c := by
        rw [hcdef]; field_simp; ring
      rw [h2] at h
      have h3 : δ/2 ≤ δ/c := by
        rw [div_le_div_iff₀ (by norm_num) hcpos]
        nlinarith [hδpos'.le, hδle1']
      linarith [h, h3]
    have hid := kappaSum_c_trick Q c hQ hc1 r
    have hQc1 : 1 ≤ Q * c := by nlinarith [hQ, hc1]
    have hmin : min Q (Q * c) = Q := min_eq_left (by nlinarith [hQ, hc1])
    have hΔ : |Work.LinnikAreas.Density4.kappaLogSum (Q*c) r
        - Work.LinnikAreas.Density4.kappaLogSum Q r|
        ≤ Kd * Work.LinnikAreas.Density4.sHalf r * (Real.log (2+Q))^(-(2*E)) := by
      have h := hdiff Q (Q*c) r hQ hQc1 hr
      rw [hmin] at h
      rwa [abs_sub_comm] at h
    have hwindow := kappaSum_window_bound Q c hQ hc1 r
    have hlogratio : Real.log (((⌊Q*c⌋₊:ℕ):ℝ) / ((⌊Q⌋₊:ℕ):ℝ)) ≤ Real.log c + 1/(Q-1) := by
      have hfloor : Q - 1 ≤ ((⌊Q⌋₊:ℕ):ℝ) := by have h := Nat.lt_floor_add_one Q; linarith
      have hden : (0:ℝ) < ((⌊Q⌋₊:ℕ):ℝ) := by
        have h1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
        exact_mod_cast (by omega : 0 < ⌊Q⌋₊)
      have hnumpos : (0:ℝ) < ((⌊Q*c⌋₊:ℕ):ℝ) := by
        have h1 : 1 ≤ ⌊Q*c⌋₊ := Nat.le_floor (by push_cast; nlinarith [hQ, hc1])
        exact_mod_cast (by omega : 0 < ⌊Q*c⌋₊)
      have hratio : ((⌊Q*c⌋₊:ℕ):ℝ) / ((⌊Q⌋₊:ℕ):ℝ) ≤ Q*c/(Q-1) := by
        rw [div_le_div_iff₀ hden hQm1pos]
        have h1 : ((⌊Q*c⌋₊:ℕ):ℝ) ≤ Q*c := Nat.floor_le (by positivity)
        have hd1nn : (0:ℝ) ≤ ((⌊Q*c⌋₊:ℕ):ℝ) := by positivity
        have hflnn : (0:ℝ) ≤ ((⌊Q⌋₊:ℕ):ℝ) := by positivity
        calc ((⌊Q*c⌋₊:ℕ):ℝ) * (Q - 1) ≤ ((⌊Q*c⌋₊:ℕ):ℝ) * ((⌊Q⌋₊:ℕ):ℝ) :=
              mul_le_mul_of_nonneg_left hfloor hd1nn
          _ ≤ (Q*c) * ((⌊Q⌋₊:ℕ):ℝ) := mul_le_mul_of_nonneg_right h1 hflnn
      have hlogratio1 : Real.log (((⌊Q*c⌋₊:ℕ):ℝ) / ((⌊Q⌋₊:ℕ):ℝ)) ≤ Real.log (Q*c/(Q-1)) :=
        Real.log_le_log (div_pos hnumpos hden) hratio
      have hsplit : Real.log (Q*c/(Q-1)) = Real.log c + Real.log (Q/(Q-1)) := by
        rw [show Q*c/(Q-1) = c * (Q/(Q-1)) by field_simp]
        exact Real.log_mul (ne_of_gt (lt_trans zero_lt_one hc1)) (by positivity)
      have hlast : Real.log (Q/(Q-1)) ≤ 1/(Q-1) := by
        have hpos : (0:ℝ) < Q/(Q-1) := by positivity
        have h := Real.log_le_sub_one_of_pos hpos
        rw [div_sub_one (by linarith : (Q-1) ≠ 0)] at h
        rw [show Q - (Q-1) = 1 by ring] at h
        simpa using h
      rw [hsplit] at hlogratio1
      linarith [hlogratio1, hlast]
    have hwin2 : |∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n
          * Real.log (Q * c / (n : ℝ))|
        ≤ Real.log c * (Real.log c + 1/(Q-1)) :=
      le_trans hwindow (mul_le_mul_of_nonneg_left hlogratio hlogcpos.le)
    have hcomb : |Real.log c * Work.LinnikAreas.Density4.kappaSum ⌊Q⌋₊ r|
        ≤ Kd * Work.LinnikAreas.Density4.sHalf r * (Real.log (2+Q))^(-(2*E))
          + Real.log c * (Real.log c + 1/(Q-1)) := by
      have h1 : Real.log c * Work.LinnikAreas.Density4.kappaSum ⌊Q⌋₊ r
          = (Work.LinnikAreas.Density4.kappaLogSum (Q*c) r
              - Work.LinnikAreas.Density4.kappaLogSum Q r)
            - (∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n
                  * Real.log (Q * c / (n : ℝ))) := by
        rw [hid]; ring
      rw [h1]
      have habs : |(Work.LinnikAreas.Density4.kappaLogSum (Q*c) r
              - Work.LinnikAreas.Density4.kappaLogSum Q r)
            - (∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n
                  * Real.log (Q * c / (n : ℝ)))| ≤
          |Work.LinnikAreas.Density4.kappaLogSum (Q*c) r
              - Work.LinnikAreas.Density4.kappaLogSum Q r|
            + |∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n
                  * Real.log (Q * c / (n : ℝ))| := by
        have h := abs_sub_le (Work.LinnikAreas.Density4.kappaLogSum (Q*c) r
              - Work.LinnikAreas.Density4.kappaLogSum Q r) 0
              (∑ n ∈ (Finset.Icc (⌊Q⌋₊ + 1) ⌊Q * c⌋₊).filter (fun n => Nat.Coprime n r),
                (ArithmeticFunction.moebius n : ℝ) / Work.LinnikAreas.Density4.kappaR n
                  * Real.log (Q * c / (n : ℝ)))
        simpa using h
      exact le_trans habs (add_le_add hΔ hwin2)
    have hdiv : |Work.LinnikAreas.Density4.kappaSum ⌊Q⌋₊ r|
        = |Real.log c * Work.LinnikAreas.Density4.kappaSum ⌊Q⌋₊ r| / Real.log c := by
      rw [abs_mul, abs_of_pos hlogcpos]
      field_simp
    rw [hdiv]
    refine le_trans (div_le_div_of_nonneg_right hcomb hlogcpos.le) ?_
    rw [add_div]
    have hδ2 : (Real.log (2+Q))^(-(2*E)) = δ * δ := by
      rw [hδdef, ← Real.rpow_add hlog2Qpos]
      congr 1
      ring
    have ht1 : Kd * Work.LinnikAreas.Density4.sHalf r * (Real.log (2+Q))^(-(2*E))
          / Real.log c ≤ 2 * Kd * Work.LinnikAreas.Density4.sHalf r * δ := by
      rw [hδ2, div_le_iff₀ hlogcpos]
      have hL : Kd * Work.LinnikAreas.Density4.sHalf r * (δ * δ)
          = 2 * Kd * Work.LinnikAreas.Density4.sHalf r * δ * (δ/2) := by ring
      rw [hL]
      exact mul_le_mul_of_nonneg_left hlogc_ge (by positivity)
    have ht2 : Real.log c * (Real.log c + 1/(Q-1)) / Real.log c ≤ (1 + Kinv) * δ := by
      rw [mul_div_cancel_left₀ _ (ne_of_gt hlogcpos)]
      have h1 : 1/(Q-1) ≤ Kinv * δ := by
        rw [hδdef]; exact hinv Q hQ2
      linarith [hlogc_le, h1]
    have hsum : 2 * Kd * Work.LinnikAreas.Density4.sHalf r * δ + (1 + Kinv) * δ
        ≤ C * Work.LinnikAreas.Density4.sHalf r * δ := by
      have h1 : 2 * Kd * Work.LinnikAreas.Density4.sHalf r * δ
          = (2*Kd) * (Work.LinnikAreas.Density4.sHalf r * δ) := by ring
      have hδs : δ ≤ Work.LinnikAreas.Density4.sHalf r * δ := by
        nlinarith [hsh1, hδpos'.le]
      have h2 : (1 + Kinv) * δ ≤ (1 + Kinv) * (Work.LinnikAreas.Density4.sHalf r * δ) :=
        mul_le_mul_of_nonneg_left hδs (by linarith [hKinvpos])
      have h3 : (2*Kd) * (Work.LinnikAreas.Density4.sHalf r * δ)
            + (1+Kinv) * (Work.LinnikAreas.Density4.sHalf r * δ)
          = (2*Kd + (1+Kinv)) * (Work.LinnikAreas.Density4.sHalf r * δ) := by ring
      have h4 : (2*Kd + (1+Kinv)) * (Work.LinnikAreas.Density4.sHalf r * δ)
          ≤ C * (Work.LinnikAreas.Density4.sHalf r * δ) :=
        mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith [h4E, hKinvpos, hKdpos])
          (by positivity)
      calc 2 * Kd * Work.LinnikAreas.Density4.sHalf r * δ + (1 + Kinv) * δ
          = (2*Kd) * (Work.LinnikAreas.Density4.sHalf r * δ) + (1 + Kinv) * δ := by rw [h1]
        _ ≤ (2*Kd) * (Work.LinnikAreas.Density4.sHalf r * δ)
              + (1 + Kinv) * (Work.LinnikAreas.Density4.sHalf r * δ) :=
            add_le_add le_rfl h2
        _ = (2*Kd + (1+Kinv)) * (Work.LinnikAreas.Density4.sHalf r * δ) := h3
        _ ≤ C * (Work.LinnikAreas.Density4.sHalf r * δ) := h4
        _ = C * Work.LinnikAreas.Density4.sHalf r * δ := by ring
    calc Kd * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + Q)) ^ (-(2 * E)) / Real.log c
          + Real.log c * (Real.log c + 1 / (Q - 1)) / Real.log c
        ≤ 2 * Kd * Work.LinnikAreas.Density4.sHalf r * δ + (1 + Kinv) * δ :=
          add_le_add ht1 ht2
      _ ≤ C * Work.LinnikAreas.Density4.sHalf r * δ := hsum
      _ = C * Work.LinnikAreas.Density4.sHalf r * (Real.log (2 + Q)) ^ (-E) := by rw [hδdef]


end

end Work.LinnikAreas.JutilaPieces
