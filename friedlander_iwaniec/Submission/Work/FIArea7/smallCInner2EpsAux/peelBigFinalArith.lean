import Mathlib

set_option maxHeartbeats 1000000

namespace Work.FIArea7.smallCInner2EpsAux

/-- **Final numeric bookkeeping of the peeled bilinear estimate (weighted form).**  Combines the
hyperbola term (with the loss factor `(u+c+2)^ε` and range `⌊u/(z+1)⌋`) and the diagonal term
(`≪ u log(u+2)/z`) into a single bound `C·u·z^{-1/12}·(u+c+2)^ε·log(u+2)^A`, valid for `1 ≤ z`. -/
theorem peelBigFinalArith (C1 C2 A1 A2 eps : ℝ)
    (h1 : 0 < C1) (h2 : 0 < C2) (h4 : 0 < A1) (h5 : 0 < A2) (h3 : 0 < eps) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ u z c : ℕ, 1 ≤ z →
      C1 * (2 * ((u / (z + 1) : ℕ) : ℝ)) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12)
          * (((u : ℝ) + (c : ℝ) + 2) ^ eps) * (Real.log ((u : ℝ) + 2)) ^ A1
        + C2 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) ^ A2 / (z : ℝ)
      ≤ C * (u : ℝ) * ((z : ℝ) ^ (-(1 : ℝ) / 12)) * (((u : ℝ) + (c : ℝ) + 2) ^ eps)
          * (Real.log ((u : ℝ) + 2)) ^ A := by
  refine ⟨C1 * 2 ^ ((1:ℝ)/12) + C2, max (max A1 A2) 0 + 1, ?_, ?_, ?_⟩
  · have h2p : (0:ℝ) < 2 := by norm_num
    nlinarith [Real.rpow_pos_of_pos h2p ((1:ℝ)/12), h1, h2]
  · have := le_max_right (max A1 A2) (0:ℝ); linarith
  · intro u z c hz
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · simp [Real.zero_rpow]
    · have hu1 : 1 ≤ u := hu
      have hU1 : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu1
      have hUpos : 0 < (u:ℝ) := lt_of_lt_of_le one_pos hU1
      have hZ1 : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
      have hZpos : 0 < (z:ℝ) := by linarith
      have hLX : 1 ≤ Real.log ((u:ℝ)+2) := by
        have hh : (1:ℝ) < Real.log ((u:ℝ)+2) := by
          rw [Real.lt_log_iff_exp_lt (by positivity)]
          linarith [Real.exp_one_lt_three, hU1]
        exact le_of_lt hh
      have hLnn : 0 ≤ Real.log ((u:ℝ)+2) := le_trans zero_le_one hLX
      have hP1 : (1:ℝ) ≤ ((u:ℝ)+(c:ℝ)+2)^eps := by
        apply Real.one_le_rpow _ (le_of_lt h3)
        have hc : (0:ℝ) ≤ (c:ℝ) := by positivity
        linarith
      have hA : (2 * ((u / (z + 1) : ℕ) : ℝ))^((1:ℝ)/12) * (u:ℝ)^((11:ℝ)/12)
              ≤ 2^((1:ℝ)/12) * (u:ℝ) * (z:ℝ)^(-(1:ℝ)/12) := by
        have hdiv1 : ((u / (z + 1) : ℕ) : ℝ) ≤ (u:ℝ)/((z:ℝ)+1) := by
          simpa [Nat.cast_add, Nat.cast_one] using (Nat.cast_div_le (α := ℝ) (m := u) (n := z + 1))
        have hdiv2 : (u:ℝ)/((z:ℝ)+1) ≤ (u:ℝ)/(z:ℝ) := by
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg u) hZpos (by linarith)
        have hdiv : ((u / (z + 1) : ℕ) : ℝ) ≤ (u:ℝ)/(z:ℝ) := le_trans hdiv1 hdiv2
        have hle : (2 * ((u / (z + 1) : ℕ) : ℝ)) ≤ (2 * ((u:ℝ)/(z:ℝ))) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
        have hstep : (2 * ((u / (z + 1) : ℕ) : ℝ))^((1:ℝ)/12) ≤ (2 * ((u:ℝ)/(z:ℝ)))^((1:ℝ)/12) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
        calc (2 * ((u / (z + 1) : ℕ) : ℝ))^((1:ℝ)/12) * (u:ℝ)^((11:ℝ)/12)
            ≤ (2 * ((u:ℝ)/(z:ℝ)))^((1:ℝ)/12) * (u:ℝ)^((11:ℝ)/12) :=
              mul_le_mul_of_nonneg_right hstep (by positivity)
          _ = 2^((1:ℝ)/12) * (u:ℝ) * (z:ℝ)^(-(1:ℝ)/12) := by
              have hrew : (u:ℝ) ^ ((1:ℝ)/12) * (u:ℝ) ^ ((11:ℝ)/12) = (u:ℝ) := by
                rw [← Real.rpow_add hUpos ((1:ℝ)/12) ((11:ℝ)/12)]
                norm_num
              rw [show -(1:ℝ)/12 = -((1:ℝ)/12) by ring]
              rw [div_eq_mul_inv]
              rw [show (2 * ((u:ℝ) * (z:ℝ)⁻¹)) = (2 * (u:ℝ)) * (z:ℝ)⁻¹ by ring]
              rw [Real.mul_rpow (by positivity) (by positivity)]
              rw [Real.mul_rpow (by norm_num) (le_of_lt hUpos)]
              rw [Real.inv_rpow (le_of_lt hZpos), Real.rpow_neg (le_of_lt hZpos) ((1:ℝ)/12)]
              rw [show 2 ^ ((1:ℝ)/12) * (u:ℝ) ^ ((1:ℝ)/12) * ((z:ℝ) ^ ((1:ℝ)/12))⁻¹ * (u:ℝ) ^ ((11:ℝ)/12)
                    = 2 ^ ((1:ℝ)/12) * ((u:ℝ) ^ ((1:ℝ)/12) * (u:ℝ) ^ ((11:ℝ)/12)) * ((z:ℝ) ^ ((1:ℝ)/12))⁻¹ by ring]
              rw [hrew]
      have hLA1 : (Real.log ((u:ℝ)+2))^A1 ≤ (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hLX
        have ha := le_max_left A1 A2
        have hb := le_max_left (max A1 A2) (0:ℝ)
        linarith
      have hLA2 : (Real.log ((u:ℝ)+2))^A2 ≤ (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hLX
        have ha := le_max_right A1 A2
        have hb := le_max_left (max A1 A2) (0:ℝ)
        linarith
      have hZinv : ((z:ℝ) ^ (-(1:ℝ))) ≤ (z:ℝ) ^ (-(1:ℝ)/12) :=
        Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
      have ht1 : C1 * (2 * ((u / (z + 1) : ℕ) : ℝ))^((1:ℝ)/12) * (u:ℝ)^((11:ℝ)/12)
                   * ((u:ℝ)+(c:ℝ)+2)^eps * (Real.log ((u:ℝ)+2))^A1
               ≤ C1 * (2^((1:ℝ)/12) * (u:ℝ) * (z:ℝ)^(-(1:ℝ)/12))
                   * ((u:ℝ)+(c:ℝ)+2)^eps * (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1) := by
        rw [show C1 * (2 * ((u / (z + 1) : ℕ) : ℝ))^((1:ℝ)/12) * (u:ℝ)^((11:ℝ)/12)
              = C1 * ((2 * ((u / (z + 1) : ℕ) : ℝ))^((1:ℝ)/12) * (u:ℝ)^((11:ℝ)/12)) by ring]
        gcongr
      have ht2 : C2 * (u:ℝ) * (Real.log ((u:ℝ)+2))^A2 / (z:ℝ)
               ≤ C2 * (u:ℝ) * (z:ℝ)^(-(1:ℝ)/12) * (((u:ℝ)+(c:ℝ)+2)^eps
                   * (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1)) := by
        calc C2 * (u:ℝ) * (Real.log ((u:ℝ)+2))^A2 / (z:ℝ)
            = C2 * (u:ℝ) * (Real.log ((u:ℝ)+2))^A2 * (z:ℝ)^(-(1:ℝ)) := by
              rw [div_eq_mul_inv, Real.rpow_neg_one]
          _ ≤ C2 * (u:ℝ) * (Real.log ((u:ℝ)+2))^A2 * (z:ℝ)^(-(1:ℝ)/12) := by
              apply mul_le_mul_of_nonneg_left hZinv
              positivity
          _ ≤ C2 * (u:ℝ) * (Real.log ((u:ℝ)+2))^A2 * (z:ℝ)^(-(1:ℝ)/12) * ((u:ℝ)+(c:ℝ)+2)^eps := by
              refine le_mul_of_one_le_right (by positivity) hP1
          _ ≤ C2 * (u:ℝ) * (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1) * (z:ℝ)^(-(1:ℝ)/12)
                * ((u:ℝ)+(c:ℝ)+2)^eps := by
              gcongr
          _ = C2 * (u:ℝ) * (z:ℝ)^(-(1:ℝ)/12) * (((u:ℝ)+(c:ℝ)+2)^eps
                * (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1)) := by ring
      calc C1 * (2 * ((u / (z + 1) : ℕ) : ℝ)) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12)
            * (((u : ℝ) + (c : ℝ) + 2) ^ eps) * (Real.log ((u : ℝ) + 2)) ^ A1
        + C2 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) ^ A2 / (z : ℝ)
          ≤ C1 * (2^((1:ℝ)/12) * (u:ℝ) * (z:ℝ)^(-(1:ℝ)/12)) * ((u:ℝ)+(c:ℝ)+2)^eps
              * (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1)
            + C2 * (u:ℝ) * (z:ℝ)^(-(1:ℝ)/12) * (((u:ℝ)+(c:ℝ)+2)^eps
              * (Real.log ((u:ℝ)+2))^(max (max A1 A2) 0 + 1)) := add_le_add ht1 ht2
        _ = (C1 * 2 ^ ((1:ℝ)/12) + C2) * (u : ℝ) * ((z : ℝ) ^ (-(1 : ℝ) / 12))
              * (((u : ℝ) + (c : ℝ) + 2) ^ eps) * (Real.log ((u : ℝ) + 2)) ^ (max (max A1 A2) 0 + 1) := by
              ring

end Work.FIArea7.smallCInner2EpsAux
