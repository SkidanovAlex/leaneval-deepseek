import Mathlib
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.GeomMinIncPart
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.GeomMinDecPart

/-!
# The min-geometric `rpow` sum bound

We bound, uniformly in the number of terms, sums of the shape
`∑_{j<n} min N (C·a^j) · a^{-jθ}` for `a > 1` and `0 < θ < 1`.
Splitting at the (unique) crossing index `k` where `C·a^k` overtakes `N`, the sum
is a sum of an increasing geometric series (ratio `a^{1-θ} > 1`) up to `k` and of a
decreasing one (ratio `a^{-θ} < 1`) from `k` on; the two geometric tails are
controlled by the two auxiliary lemmas `GeomMinIncPart` and `GeomMinDecPart`.

Instantiating `a = 2^s`, `θ = m/s` yields the statement of the paper's bound.
-/

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

open Finset

/-- Abstract min-geometric sum bound: for `a > 1` and `0 < θ < 1` there is a
constant `K` with
`∑_{j<n} min N (C·a^j) · a^{-jθ} ≤ K · C^θ · N^{1-θ}` for all `N, C ≥ 0` and `n`. -/
theorem geom_min_sum_rpow {a θ : ℝ} (ha : 1 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N C : ℝ) (n : ℕ), 0 ≤ N → 0 ≤ C →
      (∑ j ∈ Finset.range (n+1), min N (C * a^j) * a^(-(j:ℝ)*θ))
      ≤ K * C^θ * N^(1-θ) := by
  classical
  have ha0 : 0 < a := lt_trans one_pos ha
  have h1θ : 0 < 1 - θ := by linarith
  have hq1 : 1 < a^(1-θ) := Real.one_lt_rpow ha h1θ
  have hqpos : 0 < a^(1-θ) := lt_trans one_pos hq1
  have hqnn : 0 ≤ a^(1-θ)/(a^(1-θ)-1) := div_nonneg hqpos.le (by linarith)
  have hr1 : a^(-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith)
  have hrpos : 0 < a^(-θ) := Real.rpow_pos_of_pos ha0 _
  have hrnn : 0 ≤ 1/(1-a^(-θ)) := div_nonneg one_pos.le (by linarith)
  have hrw : ∀ j : ℕ, a^(-(j:ℝ)*θ) = (a^j)^(-θ) := fun j => by
    rw [← Real.rpow_natCast a j, ← Real.rpow_mul ha0.le (j:ℝ) (-θ)]
    congr 1; ring
  refine ⟨a^(1-θ)/(a^(1-θ)-1) + 1/(1-a^(-θ)) + 1, ?_, ?_⟩
  · have hq : 0 < a^(1-θ)/(a^(1-θ)-1) := div_pos hqpos (by linarith)
    have hr : 0 < 1/(1-a^(-θ)) := div_pos one_pos (by linarith)
    linarith
  · intro N C n hN hC
    have hCθnn : 0 ≤ C^θ := Real.rpow_nonneg hC θ
    have hNθnn : 0 ≤ N^(1-θ) := Real.rpow_nonneg hN (1-θ)
    have hV : 0 ≤ C^θ * N^(1-θ) := mul_nonneg hCθnn hNθnn
    by_cases hC0 : C = 0
    · subst hC0
      have hL : (∑ j ∈ Finset.range (n+1), min N (0 * a^j) * a^(-(j:ℝ)*θ)) = 0 := by
        apply Finset.sum_eq_zero; intro j _
        rw [zero_mul, min_eq_right hN, zero_mul]
      rw [hL, Real.zero_rpow (ne_of_gt hθ0)]
      simp
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
      by_cases hN0 : N = 0
      · subst hN0
        have hL : (∑ j ∈ Finset.range (n+1), min 0 (C * a^j) * a^(-(j:ℝ)*θ)) = 0 := by
          apply Finset.sum_eq_zero; intro j _
          rw [min_eq_left (mul_nonneg hC (pow_nonneg ha0.le j)), zero_mul]
        rw [hL, Real.zero_rpow (ne_of_gt h1θ)]
        simp
      · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
        have hex : ∃ j, N < C * a^j := by
          obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (N / C) ha
          refine ⟨j, ?_⟩
          have h2 := mul_lt_mul_of_pos_right hj hCpos
          rwa [div_mul_cancel₀ N (ne_of_gt hCpos), mul_comm] at h2
        set k := Nat.find hex
        have hkspec : N < C * a^k := Nat.find_spec hex
        have hkmin : ∀ j < k, C * a^j ≤ N := fun j hj => not_lt.mp (Nat.find_min hex hj)
        have hcrossA : 1 ≤ k → a ^ (k-1) ≤ N / C := fun hk1 => by
          have h := hkmin (k-1) (Nat.sub_lt hk1 (by norm_num))
          rw [le_div_iff₀ hCpos, mul_comm]
          exact h
        have hcrossB : N / C ≤ a^k := by
          rw [div_le_iff₀ hCpos, mul_comm]
          exact le_of_lt hkspec
        have hterm : ∀ j : ℕ, min N (C * a^j) * a^(-(j:ℝ)*θ)
            = (if j < k then C * (a^j)^(1-θ) else 0)
              + (if k ≤ j then N * (a^j)^(-θ) else 0) := by
          intro j
          rw [hrw j]
          rcases lt_or_ge j k with hjk | hjk
          · rw [if_pos hjk, if_neg (not_le.mpr hjk), add_zero,
                min_eq_right (hkmin j hjk),
                show (a^j)^(1-θ) = a^j * (a^j)^(-θ) by
                  rw [show (1:ℝ)-θ = 1 + (-θ) by ring,
                      Real.rpow_add (pow_pos ha0 j), Real.rpow_one]]
            ring
          · rw [if_neg (not_lt.mpr hjk), if_pos hjk, zero_add, min_eq_left]
            exact le_of_lt (lt_of_lt_of_le hkspec
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_of_lt ha) hjk) hCpos.le))
        have hsplit : (∑ j ∈ Finset.range (n+1), min N (C * a^j) * a^(-(j:ℝ)*θ))
            = (∑ j ∈ Finset.range (n+1), (if j < k then C * (a^j)^(1-θ) else 0))
              + (∑ j ∈ Finset.range (n+1), (if k ≤ j then N * (a^j)^(-θ) else 0)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => hterm j)
        have hAb : (∑ j ∈ Finset.range (n+1), (if j < k then C * (a^j)^(1-θ) else 0))
            ≤ a^(1-θ)/(a^(1-θ)-1) * C^θ * N^(1-θ) := by
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · rw [hk0]
            have hzero : (∑ j ∈ Finset.range (n+1),
                (if j < (0:ℕ) then C * (a^j)^(1-θ) else 0)) = 0 := by
              apply Finset.sum_eq_zero; intro j _; simp
            rw [hzero]
            exact mul_nonneg (mul_nonneg hqnn hCθnn) hNθnn
          · exact GeomMinIncPart ha hθ0 hθ1 hNpos hCpos (Nat.succ_le_of_lt hkpos)
              (hcrossA (Nat.succ_le_of_lt hkpos))
        have hBb := GeomMinDecPart ha hθ0 hθ1 hNpos hCpos (k := k) (n := n) hcrossB
        calc (∑ j ∈ Finset.range (n+1), min N (C * a^j) * a^(-(j:ℝ)*θ))
            = _ := hsplit
          _ ≤ a^(1-θ)/(a^(1-θ)-1) * C^θ * N^(1-θ)
                + 1/(1-a^(-θ)) * C^θ * N^(1-θ) := add_le_add hAb hBb
          _ = (a^(1-θ)/(a^(1-θ)-1) + 1/(1-a^(-θ))) * (C^θ * N^(1-θ)) := by ring
          _ ≤ (a^(1-θ)/(a^(1-θ)-1) + 1/(1-a^(-θ)) + 1) * C^θ * N^(1-θ) := by
              calc (a^(1-θ)/(a^(1-θ)-1) + 1/(1-a^(-θ))) * (C^θ * N^(1-θ))
                  ≤ (a^(1-θ)/(a^(1-θ)-1) + 1/(1-a^(-θ)) + 1) * (C^θ * N^(1-θ)) :=
                    mul_le_mul_of_nonneg_right (by linarith) hV
                _ = (a^(1-θ)/(a^(1-θ)-1) + 1/(1-a^(-θ)) + 1) * C^θ * N^(1-θ) := by ring

/-- The requested bound: with `a = 2^s` and `θ = m/s`, the min-geometric sum over
the dyadic shells `2^{js}` is bounded by `K1 · C^{m/s} · N^{1-m/s}`. -/
theorem MinGeomRpowSumAux {m s : ℝ} (hm : 0 < m) (hms : m < s) :
    ∃ K1 : ℝ, 0 < K1 ∧ ∀ (N C : ℝ) (Knum : ℕ), 0 ≤ N → 0 ≤ C →
      (∑ j ∈ Finset.range (Knum + 1),
        min N (C * (2:ℝ)^((j:ℝ)*s)) * (2:ℝ)^(-(j:ℝ)*m))
      ≤ K1 * C ^ (m / s) * N ^ (1 - m / s) := by
  have hs0 : 0 < s := lt_trans hm hms
  have hθ0 : 0 < m / s := div_pos hm hs0
  have hθ1 : m / s < 1 := (div_lt_one hs0).mpr hms
  obtain ⟨K, hKpos, hK⟩ := geom_min_sum_rpow (a := (2:ℝ)^s) (θ := m / s)
    (Real.one_lt_rpow (by norm_num) hs0) hθ0 hθ1
  refine ⟨K, hKpos, ?_⟩
  intro N C Knum hN hC
  have hsum : (∑ j ∈ Finset.range (Knum + 1),
        min N (C * (2:ℝ)^((j:ℝ)*s)) * (2:ℝ)^(-(j:ℝ)*m))
      = (∑ j ∈ Finset.range (Knum + 1),
        min N (C * ((2:ℝ)^s)^j) * ((2:ℝ)^s)^(-(j:ℝ)*(m/s))) := by
    apply Finset.sum_congr rfl
    intro j _
    have h1 : (2:ℝ)^((j:ℝ)*s) = ((2:ℝ)^s)^j := by
      rw [← Real.rpow_natCast ((2:ℝ)^s) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; ring
    have h2 : ((2:ℝ)^s)^(-(j:ℝ)*(m/s)) = (2:ℝ)^(-(j:ℝ)*m) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      rw [show s * (-(j:ℝ) * (m/s)) = -(j:ℝ) * (s * (m/s)) by ring,
          mul_comm s (m/s), div_mul_cancel₀ m (ne_of_gt hs0)]
    rw [h1, ← h2]
  rw [hsum]
  exact hK N C Knum hN hC

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
