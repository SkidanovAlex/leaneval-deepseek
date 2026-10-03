import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.peelBigEpsDefs
import Submission.Work.FIArea7.normQuadEigenLe
import Submission.Work.FIArea7.sum_tau_Icc_le_two_mul_log
import Submission.Work.FIArea7.sum_inv_sq_filter_le
import Submission.Work.FIArea7.t2psi_defs

set_option maxHeartbeats 2000000

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Sum over the multiples of `m` in `[1,M]`, reindexed by `k = n/m`. -/
private lemma sum_multiples_eq (F : ℕ → ℝ) {m M : ℕ} (hm : 1 ≤ m) :
    (∑ n ∈ (Finset.Icc 1 M).filter (fun n => m ∣ n), F n)
      = ∑ k ∈ Finset.Icc 1 (M / m), F (m * k) := by
  refine Finset.sum_bij (fun n _ => n / m) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnIcc, hdvd⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_Icc] at hnIcc ⊢
    refine ⟨?_, Nat.div_le_div_right hnIcc.2⟩
    rcases Nat.eq_zero_or_pos (n / m) with h | h
    · exfalso
      have hn0 : n ≠ 0 := by omega
      apply hn0
      rw [← Nat.mul_div_cancel' hdvd, h, mul_zero]
    · exact h
  · intro a ha b hb hab
    obtain ⟨_, hadvd⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hbdvd⟩ := Finset.mem_filter.mp hb
    rw [← Nat.mul_div_cancel' hadvd, ← Nat.mul_div_cancel' hbdvd, hab]
  · intro kk hk
    rw [Finset.mem_Icc] at hk
    refine ⟨m * kk, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right m kk⟩
      · have := Nat.mul_le_mul hm hk.1; simpa using this
      · have h2 : kk * m ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp hk.2
        calc m * kk = kk * m := Nat.mul_comm m kk
          _ ≤ M := h2
    · exact Nat.mul_div_cancel_left kk (by omega : 0 < m)
  · intro n hn
    obtain ⟨_, hdvd⟩ := Finset.mem_filter.mp hn
    rw [Nat.mul_div_cancel' hdvd]

/-- The `m`-th inner diagonal sum (with `m` prime `> z`) is bounded by
`12 τ(c) ∑_{k ≤ u/m²} τ(k)`. -/
private lemma diagInner_le (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ)
    (c u z : ℕ) (P : ℝ → ℝ) (hchi : ∀ z', ‖chi z'‖ ≤ 1) (hPabs : ∀ t, |P t| ≤ 1)
    {m : ℕ} (hmp : m.Prime) (hzm : z < m) :
    (∑ n ∈ (Finset.Icc 1 (peelBigM u z)).filter (fun n => m ∣ n),
        ‖peelT Pa chi k c u z P m n‖)
      ≤ 12 * (((c.divisors.card : ℕ) : ℝ))
          * (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ))) := by
  have hψ : ∀ w, ‖Work.FIArea7.grossenChar chi k w‖ ≤ 1 :=
    fun w => Work.FIArea7.t2psi_norm_grossenChar chi hchi k w
  have hm1 : 1 ≤ m := hmp.one_le
  have hstep : ∀ n : ℕ, ‖peelT Pa chi k c u z P m n‖
      ≤ (if m * n ≤ u then 4 * (((c * (m * n)).divisors.card : ℕ) : ℝ) else 0) := by
    intro n
    have hA : peelA Pa c z m
        = (ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m
            * (if Nat.Coprime c m then (1 : ℂ) else 0) := by
      unfold peelA; rw [if_pos ⟨hmp, hzm⟩]
    have hb1 : ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m
          * (if Nat.Coprime c m then (1 : ℂ) else 0)‖ ≤ 1 := by
      have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := norm_moebius_cast_le m
      have h2 : ‖Work.FIArea7.nspInd Pa m‖ ≤ 1 := Work.FIArea7.norm_nspInd_le_one Pa m
      have h3 : ‖(if Nat.Coprime c m then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp
      calc ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m
            * (if Nat.Coprime c m then (1 : ℂ) else 0)‖
          = ‖(ArithmeticFunction.moebius m : ℂ)‖ * ‖Work.FIArea7.nspInd Pa m‖
              * ‖(if Nat.Coprime c m then (1 : ℂ) else 0)‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * 1 := by gcongr
        _ ≤ 1 := by norm_num
    have hb2 : ‖peelB Pa c u z n‖ ≤ 1 := norm_peelB_le Pa c u z n
    have hb3 : ‖((P ((c : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hPabs _
    have hb4 : ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (m * n))‖
        ≤ 4 * (((c * (m * n)).divisors.card : ℕ) : ℝ) :=
      Work.FIArea7.normQuadEigenLe _ hψ _
    unfold peelT
    by_cases hmn : m * n ≤ u
    · rw [if_pos hmn, if_pos hmn, hA]
      calc ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m
              * (if Nat.Coprime c m then (1 : ℂ) else 0) * peelB Pa c u z n
              * ((P ((c : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (m * n))‖
          = ‖(ArithmeticFunction.moebius m : ℂ) * Work.FIArea7.nspInd Pa m
              * (if Nat.Coprime c m then (1 : ℂ) else 0)‖ * ‖peelB Pa c u z n‖
              * ‖((P ((c : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)‖
              * ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (m * n))‖ := by
            rw [norm_mul, norm_mul, norm_mul]
        _ ≤ 1 * 1 * 1 * (4 * (((c * (m * n)).divisors.card : ℕ) : ℝ)) := by
            gcongr
        _ = 4 * (((c * (m * n)).divisors.card : ℕ) : ℝ) := by ring
    · rw [if_neg hmn, if_neg hmn]; simp
  have hτm2 : (m ^ 2).divisors.card = 3 := by
    rw [Nat.divisors_prime_pow hmp 2]; simp
  have hτle : ∀ kk : ℕ,
      (c * (m * (m * kk))).divisors.card ≤ 3 * c.divisors.card * kk.divisors.card := by
    intro kk
    have heq : m * (m * kk) = m ^ 2 * kk := by ring
    calc (c * (m * (m * kk))).divisors.card
        ≤ c.divisors.card * (m * (m * kk)).divisors.card :=
          Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le c (m * (m * kk))
      _ = c.divisors.card * (m ^ 2 * kk).divisors.card := by rw [heq]
      _ ≤ c.divisors.card * ((m ^ 2).divisors.card * kk.divisors.card) :=
          Nat.mul_le_mul_left _ (Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le (m ^ 2) kk)
      _ = c.divisors.card * (m ^ 2).divisors.card * kk.divisors.card := by ring
      _ = 3 * c.divisors.card * kk.divisors.card := by rw [hτm2]; ring
  calc (∑ n ∈ (Finset.Icc 1 (peelBigM u z)).filter (fun n => m ∣ n), ‖peelT Pa chi k c u z P m n‖)
      ≤ ∑ n ∈ (Finset.Icc 1 (peelBigM u z)).filter (fun n => m ∣ n),
          (if m * n ≤ u then 4 * (((c * (m * n)).divisors.card : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum (fun n _ => hstep n)
    _ = ∑ kk ∈ Finset.Icc 1 (peelBigM u z / m),
          (if m * (m * kk) ≤ u then 4 * (((c * (m * (m * kk))).divisors.card : ℕ) : ℝ) else 0) :=
        sum_multiples_eq (fun n => (if m * n ≤ u then 4 * (((c * (m * n)).divisors.card : ℕ) : ℝ) else 0)) hm1
    _ ≤ ∑ kk ∈ Finset.Icc 1 (peelBigM u z / m),
          (if m * (m * kk) ≤ u then 12 * (((c.divisors.card : ℕ) : ℝ)) * (((kk.divisors.card : ℕ) : ℝ)) else 0) := by
        apply Finset.sum_le_sum; intro kk _
        by_cases h : m * (m * kk) ≤ u
        · rw [if_pos h, if_pos h]
          have hc2 : (((c * (m * (m * kk))).divisors.card : ℕ) : ℝ)
              ≤ 3 * ((c.divisors.card : ℕ) : ℝ) * ((kk.divisors.card : ℕ) : ℝ) := by
            exact_mod_cast hτle kk
          nlinarith [hc2, (by positivity : (0:ℝ) ≤ ((c.divisors.card:ℕ):ℝ)),
                     (by positivity : (0:ℝ) ≤ ((kk.divisors.card:ℕ):ℝ))]
        · rw [if_neg h, if_neg h]
    _ = 12 * (((c.divisors.card : ℕ) : ℝ))
          * (∑ kk ∈ (Finset.Icc 1 (peelBigM u z / m)).filter (fun kk => m * (m * kk) ≤ u),
              (((kk.divisors.card : ℕ) : ℝ))) := by
        rw [Finset.mul_sum, Finset.sum_filter]
    _ ≤ 12 * (((c.divisors.card : ℕ) : ℝ))
          * (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro kk hk
          obtain ⟨hkIcc, hkP⟩ := Finset.mem_filter.mp hk
          rw [Finset.mem_Icc] at hkIcc ⊢
          refine ⟨hkIcc.1, ?_⟩
          have hk2 : kk * m ^ 2 ≤ u := by
            rw [show kk * m ^ 2 = m * (m * kk) by ring]; exact hkP
          exact (Nat.le_div_iff_mul_le (pow_pos hmp.pos 2)).mpr hk2
        · intro kk _ _; exact Nat.cast_nonneg _

/-- **The diagonal correction is bounded by `100 τ(c) u log(u+2)/z`.** -/
theorem peelDiagSumBound
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c u z : ℕ) (P : ℝ → ℝ)
    (hchi : ∀ z', ‖chi z'‖ ≤ 1) (hPabs : ∀ t, |P t| ≤ 1) (hz : 1 ≤ z) :
    ‖peelDiagSum Pa chi k c u z P‖
      ≤ 100 * (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ) := by
  set M := peelBigM u z with hM
  have hA : ‖peelDiagSum Pa chi k c u z P‖
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m ∣ n),
          ‖peelT Pa chi k c u z P m n‖ := by
    rw [peelDiagSum, hM]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun m _ => norm_sum_le _ _))
  have hB : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m ∣ n),
          ‖peelT Pa chi k c u z P m n‖)
      = ∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
          ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m ∣ n), ‖peelT Pa chi k c u z P m n‖ := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro m hm hmn
    refine Finset.sum_eq_zero (fun n _ => ?_)
    rw [norm_eq_zero]
    have hp0 : peelA Pa c z m = 0 := by
      unfold peelA; rw [if_neg]; exact fun hh => hmn (Finset.mem_filter.mpr ⟨hm, hh⟩)
    unfold peelT
    by_cases hmn' : m * n ≤ u
    · rw [if_pos hmn', hp0]; ring
    · rw [if_neg hmn']
  have hC : (∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
          ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m ∣ n), ‖peelT Pa chi k c u z P m n‖)
      ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
          12 * (((c.divisors.card : ℕ) : ℝ))
            * (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ))) := by
    apply Finset.sum_le_sum
    intro m hm
    obtain ⟨_, hmp, hzm⟩ := Finset.mem_filter.mp hm
    exact diagInner_le Pa chi k c u z P hchi hPabs hmp hzm
  have htail : (∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
          (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ))))
      ≤ 4 * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ) := by
    have h1 : ∀ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
        (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ)))
          ≤ 2 * ((u : ℝ) / (m : ℝ) ^ 2) * Real.log ((u : ℝ) + 2) := by
      intro m _
      have hsz := Work.FIArea7.sum_tau_Icc_le_two_mul_log (u / m ^ 2)
      refine le_trans hsz ?_
      have hdiv : ((u / m ^ 2 : ℕ) : ℝ) ≤ (u : ℝ) / (m : ℝ) ^ 2 := by
        have := Nat.cast_div_le (α := ℝ) (m := u) (n := m ^ 2)
        simpa [Nat.cast_pow] using this
      have hlog : Real.log (((u / m ^ 2 : ℕ) : ℝ) + 2) ≤ Real.log ((u : ℝ) + 2) := by
        apply Real.log_le_log (by positivity)
        have : ((u / m ^ 2 : ℕ) : ℝ) ≤ (u : ℝ) := by
          exact_mod_cast Nat.div_le_self u (m ^ 2)
        linarith
      have hbnn : (0:ℝ) ≤ 2 * ((u : ℝ) / (m : ℝ) ^ 2) :=
        mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg u) (sq_nonneg _))
      have hlog1' : (1:ℝ) ≤ ((u / m ^ 2 : ℕ) : ℝ) + 2 := by
        have h : (0:ℝ) ≤ ((u / m ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      exact mul_le_mul (by linarith) hlog (Real.log_nonneg hlog1') hbnn
    calc (∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
            (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ))))
        ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
            2 * ((u : ℝ) / (m : ℝ) ^ 2) * Real.log ((u : ℝ) + 2) :=
          Finset.sum_le_sum h1
      _ = 2 * Real.log ((u : ℝ) + 2) * (u : ℝ)
            * (∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m), 1 / (m : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro m _; ring
      _ ≤ 2 * Real.log ((u : ℝ) + 2) * (u : ℝ) * (2 / (z : ℝ)) := by
          have hnn : (0:ℝ) ≤ 2 * Real.log ((u : ℝ) + 2) * (u : ℝ) :=
            mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by have h : (0:ℝ) ≤ (u:ℝ) := Nat.cast_nonneg u; linarith))) (Nat.cast_nonneg u)
          apply mul_le_mul_of_nonneg_left _ hnn
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
            (Work.FIArea7.sum_inv_sq_filter_le M (z : ℝ) (by exact_mod_cast (show 0 < z by omega)))
          · intro m hm
            obtain ⟨hmIcc, _, hzm⟩ := Finset.mem_filter.mp hm
            exact Finset.mem_filter.mpr ⟨hmIcc, by exact_mod_cast hzm⟩
          · intro i _ _; positivity
      _ = 4 * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ) := by ring
  have hτ0 : (0:ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have huz0 : (0:ℝ) ≤ (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg u) (Real.log_nonneg (by have h : (0:ℝ) ≤ (u:ℝ) := Nat.cast_nonneg u; linarith))) (Nat.cast_nonneg z)
  calc ‖peelDiagSum Pa chi k c u z P‖
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m ∣ n),
          ‖peelT Pa chi k c u z P m n‖ := hA
    _ = ∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
          ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m ∣ n), ‖peelT Pa chi k c u z P m n‖ := hB
    _ ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
          12 * (((c.divisors.card : ℕ) : ℝ))
            * (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ))) := hC
    _ = 12 * (((c.divisors.card : ℕ) : ℝ))
          * (∑ m ∈ (Finset.Icc 1 M).filter (fun m => m.Prime ∧ z < m),
              (∑ kk ∈ Finset.Icc 1 (u / m ^ 2), (((kk.divisors.card : ℕ) : ℝ)))) := by
          rw [Finset.mul_sum]
    _ ≤ 12 * (((c.divisors.card : ℕ) : ℝ)) * (4 * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ 100 * (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ) := by
          have hX : (0:ℝ) ≤ (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ) :=
            div_nonneg (mul_nonneg (mul_nonneg hτ0 (Nat.cast_nonneg u))
              (Real.log_nonneg (by have h : (0:ℝ) ≤ (u:ℝ) := Nat.cast_nonneg u; linarith))) (Nat.cast_nonneg z)
          have he : (12:ℝ) * (((c.divisors.card : ℕ) : ℝ))
              * (4 * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ))
              = 48 * ((((c.divisors.card : ℕ) : ℝ)) * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ)) := by ring
          have he2 : (100:ℝ) * (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ)
              = 100 * ((((c.divisors.card : ℕ) : ℝ)) * (u : ℝ) * Real.log ((u : ℝ) + 2) / (z : ℝ)) := by ring
          rw [he, he2]
          exact mul_le_mul_of_nonneg_right (by norm_num : (48:ℝ) ≤ 100) hX

end

end Work.FIArea7.smallCInner2EpsAux
