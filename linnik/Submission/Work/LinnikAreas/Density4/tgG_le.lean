import Mathlib
import Submission.Work.LinnikAreas.Density4.ThetaLogsumDefs
import Submission.Work.LinnikAreas.Density4.log_ge_two_mul_div
import Submission.Work.LinnikAreas.Density4.harmonic_le_log
import Submission.Work.LinnikAreas.Density4.amgm_pow_le

namespace Work.LinnikAreas.Density4

open scoped BigOperators
noncomputable section

set_option linter.unusedVariables false

/-- Rational lower bound for `Real.log 2`. -/
def lo2 : ℝ := 6931471803/10000000000
/-- Rational upper bound for `Real.log 2`. -/
def hi2 : ℝ := 6931471808/10000000000

/-- Reindex the harmonic sum `∑_{k=1}^{m} 1/k` as a range sum. -/
lemma sum_Icc_inv_eq (m : ℕ) :
    (∑ k ∈ Finset.Icc (1:ℕ) m, (1:ℝ)/(k:ℝ))
      = ∑ j ∈ Finset.range m, (1:ℝ)/((j:ℝ)+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, Finset.sum_range_succ]
    push_cast
    ring

/-- Lower bound `k log 2 + 2(N-2^k)/(N+2^k) ≤ log N` when `2^k ≤ N < 2^{k+1}`. -/
lemma log_nat_ge (N k : ℕ) (hk : 2^k ≤ N) (hk2 : N < 2^(k+1)) :
    (k:ℝ)*lo2 + 2*((N:ℝ) - 2^k)/((N:ℝ) + 2^k) ≤ Real.log (N:ℝ) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h2kpos : (0:ℝ) < (2:ℝ)^k := pow_pos (by norm_num) k
  have hx : (1:ℝ) ≤ (N:ℝ)/(2:ℝ)^k := by
    rw [le_div_iff₀ h2kpos, one_mul]
    have h2k : (2:ℝ)^k = (2^k:ℝ) := by push_cast; ring
    rw [h2k]; exact_mod_cast hk
  have key := log_ge_two_mul_div hx
  have h2lo : lo2 ≤ Real.log 2 := by simp only [lo2]; linarith [Real.log_two_gt_d9]
  have hsplit : Real.log (N:ℝ) = (k:ℝ)*Real.log 2 + Real.log ((N:ℝ)/(2:ℝ)^k) := by
    rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt h2kpos), Real.log_pow]; ring
  have heq : 2*((N:ℝ)/(2:ℝ)^k - 1)/((N:ℝ)/(2:ℝ)^k + 1)
      = 2*((N:ℝ) - 2^k)/((N:ℝ) + 2^k) := by
    have h2k : (2:ℝ)^k = (2^k:ℝ) := by push_cast; ring
    rw [h2k]
    have hd : (0:ℝ) < (2^k : ℝ) := by positivity
    field_simp
  have hkk : (k:ℝ)*lo2 ≤ (k:ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_left h2lo (Nat.cast_nonneg k)
  rw [heq] at key
  rw [hsplit]
  linarith [key, hkk]

/-- Assembly step: AM-GM bound together with monotonicity in `a` and `b`. -/
lemma bound_step (N : ℕ) (hN : 2 ≤ N) (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (A B Ahi Blo ell : ℝ) (hA0 : 0 ≤ A) (hB : 0 < B) (hA : A ≤ Ahi)
    (hBlo0 : 0 < Blo) (hBB : Blo ≤ B)
    (hchk : Ahi*((N:ℝ)-2)/(N:ℝ) + Ahi^2/((N:ℝ)^2*Blo) ≤ ell) :
    A * w - B * w^N ≤ ell := by
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hN2le : (0:ℝ) ≤ (N:ℝ) - 2 := by
    have : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have h1 := amgm_pow_le N hN A B w hA0 hB hw0 hw1
  have hN2pos : (0:ℝ) < (N:ℝ)^2 := by positivity
  have h2 : A^2/((N:ℝ)^2*B) ≤ Ahi^2/((N:ℝ)^2*Blo) := by
    apply div_le_div₀
    · positivity
    · exact pow_le_pow_left₀ hA0 hA 2
    · positivity
    · exact mul_le_mul_of_nonneg_left hBB (le_of_lt hN2pos)
  have h3 : A*((N:ℝ)-2)/(N:ℝ) ≤ Ahi*((N:ℝ)-2)/(N:ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
    exact mul_le_mul_of_nonneg_right hA hN2le
  calc A*w - B*w^N ≤ A*((N:ℝ)-2)/(N:ℝ) + A^2/((N:ℝ)^2*B) := h1
    _ ≤ Ahi*((N:ℝ)-2)/(N:ℝ) + Ahi^2/((N:ℝ)^2*Blo) := add_le_add h3 h2
    _ ≤ ell := hchk

/-- Finite-case reduction: with a rational upper bound `HK` for the harmonic sum
and a rational lower bound `elbK` for `log N`, the verified arithmetic inequality
`hchk` yields the claim. -/
lemma small_branch (N : ℕ) (hN : 2 ≤ N) (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (HK elbK : ℝ)
    (hW : (∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ)) = HK)
    (hlog : elbK ≤ Real.log (N:ℝ)) (helb0 : 0 ≤ elbK) (hHK1 : 1 ≤ HK)
    (hchk : (hi2 + 1 + (HK-1)/2)*((N:ℝ)-2)/(N:ℝ)
        + (hi2+1+(HK-1)/2)^2/((N:ℝ)^2 * (2*(elbK+1)/((N:ℝ)+1))) ≤ elbK) :
    ((Real.log 2 + 1) + ((∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ)) - 1)/2) * w
      - (Real.log (N:ℝ)+1)*(2/((N:ℝ)+1))*w^N ≤ Real.log (N:ℝ) := by
  rw [hW]
  have hA0 : 0 ≤ Real.log 2 + 1 + (HK - 1)/2 := by
    linarith [Real.log_two_gt_d9, hHK1]
  have hB : 0 < (Real.log (N:ℝ) + 1) * (2/((N:ℝ)+1)) := by
    have hp : (0:ℝ) < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have : (0:ℝ) < 2/((N:ℝ)+1) := by positivity
    positivity
  have hA : Real.log 2 + 1 + (HK - 1)/2 ≤ hi2 + 1 + (HK - 1)/2 := by
    have h2 : Real.log 2 ≤ hi2 := by simp only [hi2]; linarith [Real.log_two_lt_d9]
    linarith
  have hBlo0 : 0 < 2*(elbK + 1)/((N:ℝ)+1) := by
    apply div_pos _ (by positivity)
    linarith
  have hBB : 2*(elbK + 1)/((N:ℝ)+1) ≤ (Real.log (N:ℝ) + 1) * (2/((N:ℝ)+1)) := by
    have hb2 : (Real.log (N:ℝ) + 1) * (2/((N:ℝ)+1)) = 2*(Real.log (N:ℝ)+1)/((N:ℝ)+1) := by ring
    rw [hb2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h := bound_step N hN w hw0 hw1
      (Real.log 2 + 1 + (HK - 1)/2)
      ((Real.log (N:ℝ) + 1) * (2/((N:ℝ)+1)))
      (hi2 + 1 + (HK - 1)/2)
      (2*(elbK + 1)/((N:ℝ)+1))
      elbK
      hA0 hB hA hBlo0 hBB hchk
  exact h.trans hlog

/-- The requested inequality. -/
lemma tgG_le (N : ℕ) (hN : 2 ≤ N) (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : ((Real.log 2 + 1) + ((∑ k ∈ Finset.Icc 1 (N-1), (1:ℝ)/(k:ℝ)) - 1)/2) * w - (Real.log (N:ℝ) + 1) * (2/((N:ℝ)+1)) * w^N ≤ Real.log (N:ℝ) := by
  by_cases h20 : N ≤ 20
  · interval_cases N
    · exact small_branch 2 (by norm_num) w hw0 hw1 ((1:ℝ)) ((1:ℝ)*lo2) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 2 1 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 3 (by norm_num) w hw0 hw1 ((3:ℝ)/2) ((1:ℝ)*lo2 + (2:ℝ)/5) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 3 1 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 4 (by norm_num) w hw0 hw1 ((11:ℝ)/6) ((2:ℝ)*lo2) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 4 2 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 5 (by norm_num) w hw0 hw1 ((25:ℝ)/12) ((2:ℝ)*lo2 + (2:ℝ)/9) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 5 2 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 6 (by norm_num) w hw0 hw1 ((137:ℝ)/60) ((2:ℝ)*lo2 + (2:ℝ)/5) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 6 2 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 7 (by norm_num) w hw0 hw1 ((49:ℝ)/20) ((2:ℝ)*lo2 + (6:ℝ)/11) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 7 2 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 8 (by norm_num) w hw0 hw1 ((363:ℝ)/140) ((3:ℝ)*lo2) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 8 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 9 (by norm_num) w hw0 hw1 ((761:ℝ)/280) ((3:ℝ)*lo2 + (2:ℝ)/17) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 9 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 10 (by norm_num) w hw0 hw1 ((7129:ℝ)/2520) ((3:ℝ)*lo2 + (2:ℝ)/9) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 10 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 11 (by norm_num) w hw0 hw1 ((7381:ℝ)/2520) ((3:ℝ)*lo2 + (6:ℝ)/19) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 11 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 12 (by norm_num) w hw0 hw1 ((83711:ℝ)/27720) ((3:ℝ)*lo2 + (2:ℝ)/5) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 12 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 13 (by norm_num) w hw0 hw1 ((86021:ℝ)/27720) ((3:ℝ)*lo2 + (10:ℝ)/21) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 13 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 14 (by norm_num) w hw0 hw1 ((1145993:ℝ)/360360) ((3:ℝ)*lo2 + (6:ℝ)/11) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 14 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 15 (by norm_num) w hw0 hw1 ((1171733:ℝ)/360360) ((3:ℝ)*lo2 + (14:ℝ)/23) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 15 3 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 16 (by norm_num) w hw0 hw1 ((1195757:ℝ)/360360) ((4:ℝ)*lo2) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 16 4 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 17 (by norm_num) w hw0 hw1 ((2436559:ℝ)/720720) ((4:ℝ)*lo2 + (2:ℝ)/33) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 17 4 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 18 (by norm_num) w hw0 hw1 ((42142223:ℝ)/12252240) ((4:ℝ)*lo2 + (2:ℝ)/17) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 18 4 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 19 (by norm_num) w hw0 hw1 ((14274301:ℝ)/4084080) ((4:ℝ)*lo2 + (6:ℝ)/35) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 19 4 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
    · exact small_branch 20 (by norm_num) w hw0 hw1 ((275295799:ℝ)/77597520) ((4:ℝ)*lo2 + (2:ℝ)/9) (by rw [sum_Icc_inv_eq]; norm_num) (by have h := log_nat_ge 20 4 (by norm_num) (by norm_num); norm_num at h ⊢; exact h) (by norm_num [lo2]) (by norm_num) (by norm_num [lo2, hi2])
  · -- large case: 21 ≤ N
    have h21 : 21 ≤ N := by omega
    have hNpos : (0:ℝ) < (N:ℝ) := by
      have : 0 < N := by omega
      exact_mod_cast this
    have hexp3 : Real.exp 3 < 21 := by
      have he : Real.exp 3 = (Real.exp 1)^3 := by
        simpa using Real.exp_nat_mul (1:ℝ) 3
      rw [he]
      have h1 := Real.exp_one_lt_d9
      have hpos : (0:ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
      calc (Real.exp 1)^3 < (2.7182818286:ℝ)^3 := by
            exact pow_lt_pow_left₀ h1 hpos (by norm_num)
        _ < 21 := by norm_num
    have hL21 : Real.log (21:ℝ) ≤ Real.log (N:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h21)
    have hL3 : (3:ℝ) ≤ Real.log (N:ℝ) := by
      have h3 : (3:ℝ) < Real.log (21:ℝ) :=
        (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 21)).2 hexp3
      linarith
    have hW : (∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ)) - 1
        ≤ Real.log ((2*(N:ℝ)-1)/3) := harmonic_le_log N hN
    have hlog32 : (2:ℝ)/5 ≤ Real.log (3/2) := by
      have h := log_ge_two_mul_div (x := (3:ℝ)/2) (by norm_num)
      norm_num at h
      linarith
    have hb : Real.log ((2*(N:ℝ)-1)/3) ≤ Real.log (N:ℝ) - Real.log (3/2) := by
      have harg : (0:ℝ) < (2*(N:ℝ)-1)/3 := by
        have hN21r : (21:ℝ) ≤ (N:ℝ) := by exact_mod_cast h21
        apply div_pos _ (by norm_num)
        linarith
      have h1 : (2*(N:ℝ)-1)/3 ≤ (2:ℝ)/3 * (N:ℝ) := by linarith
      have h3 : Real.log ((2:ℝ)/3 * (N:ℝ)) = Real.log (N:ℝ) - Real.log (3/2) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
        have : Real.log ((2:ℝ)/3) = - Real.log (3/2) := by
          rw [show (2:ℝ)/3 = ((3:ℝ)/2)⁻¹ by norm_num, Real.log_inv]
        linarith [this]
      calc Real.log ((2*(N:ℝ)-1)/3) ≤ Real.log ((2:ℝ)/3 * (N:ℝ)) :=
            Real.log_le_log harg h1
        _ = Real.log (N:ℝ) - Real.log (3/2) := h3
    have hA : Real.log 2 + 1 + ((∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ)) - 1)/2
        ≤ Real.log (N:ℝ) := by
      have h2 : Real.log 2 ≤ (6931471808:ℝ)/10000000000 := by
        have := Real.log_two_lt_d9; linarith
      nlinarith [hW, hb, h2, hlog32, hL3]
    have hA0 : 0 ≤ Real.log 2 + 1 + ((∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ)) - 1)/2 := by
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hW1 : 1 ≤ ∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ) := by
        have hmem : 1 ∈ Finset.Icc (1:ℕ) (N-1) := by simp only [Finset.mem_Icc]; omega
        have hnn : ∀ k ∈ Finset.Icc (1:ℕ) (N-1), (0:ℝ) ≤ (1:ℝ)/(k:ℝ) := by
          intro k hk
          have hk0 : (0:ℝ) < (k:ℝ) := by
            simp only [Finset.mem_Icc] at hk
            exact_mod_cast (by omega : 0 < k)
          positivity
        simpa using Finset.single_le_sum hnn hmem
      linarith
    have hBnn : 0 ≤ (Real.log (N:ℝ) + 1) * (2/((N:ℝ)+1)) * w^N := by
      have hp : 0 ≤ Real.log (N:ℝ) := le_of_lt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
      have h1 : 0 ≤ Real.log (N:ℝ) + 1 := by linarith
      have h2 : 0 ≤ 2/((N:ℝ)+1) := by positivity
      have h3 : 0 ≤ w^N := pow_nonneg hw0 N
      exact mul_nonneg (mul_nonneg h1 h2) h3
    have hAw : ((Real.log 2 + 1) + ((∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ)) - 1)/2) * w
        ≤ Real.log 2 + 1 + ((∑ k ∈ Finset.Icc (1:ℕ) (N-1), (1:ℝ)/(k:ℝ)) - 1)/2 :=
      mul_le_of_le_one_right hA0 hw1
    linarith [hAw, hBnn, hA]

end

end Work.LinnikAreas.Density4
