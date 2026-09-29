import Mathlib
import Submission.Work.Cert.ThetaDefs
import Submission.Work.Cert.aLoop_aux

namespace Work.Cert

open Complex Finset

noncomputable section

/-- One-step expansion of the `B` rounding budget. -/
lemma Bd2_succ (k : ℕ) : Bd2 (k+1) = Bd2 k + ((16 * (k+1)^2 + 1 : ℕ) : ℝ) := by
  rw [Bd2, Finset.sum_range_succ, Bd2]

/-- One-step expansion of the `B` mean-value budget. -/
lemma BdM2_succ (m rq : ℤ) (k : ℕ) :
    BdM2 m rq (k+1) = BdM2 m rq k +
      (2 * ((((k+1)^2 : ℕ)) : ℝ) * (mub m)^((k+1)^2 - 1) * (rq:ℝ)) := by
  rw [BdM2, Finset.sum_range_succ, BdM2]

theorem bstep_num (rq m : ℤ) (k : ℕ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : mub m ≤ 79/100)
    {s : BS}
    (h3 : (mub m)^(k*k) ≤ (s.ms : ℝ)/(S:ℝ))
    (h4 : (mub m)^(2*k+1) ≤ (s.mo : ℝ)/(S:ℝ))
    (h5 : Bd2 k + BdM2 m rq k ≤ (s.dB : ℝ)) :
    (mub m)^((k+1)*(k+1)) ≤ (((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(S:ℝ) ∧
    (mub m)^(2*(k+1)+1) ≤ (((mu s.mo (mu m m + 1) + 1 : ℤ)) : ℝ)/(S:ℝ) ∧
    Bd2 (k+1) + BdM2 m rq (k+1) ≤
      (((s.dB + 2 * mu (Int.ofNat (k+1) * Int.ofNat (k+1) * dvu (mu s.ms s.mo + 1) m) rq
        + 16 * Int.ofNat (k+1) * Int.ofNat (k+1) + 1 : ℤ)) : ℝ) := by
  have hS : (0:ℝ) < (S:ℝ) := thS_pos
  have hμ0 : 0 ≤ mub m := mub_nonneg (by omega)
  have hμpos : 0 < mub m := mub_pos hm
  have hmpos : (0:ℤ) < m := lt_of_lt_of_le Int.zero_lt_one hm
  have hrqr : 0 ≤ (rq:ℝ) := by exact_mod_cast hrq
  have hstep1 : (mub m)^((k+1)*(k+1)) ≤ (((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(S:ℝ) := by
    have hprod : (mub m)^(k*k) * (mub m)^(2*k+1)
        ≤ ((s.ms:ℝ)/(S:ℝ)) * ((s.mo:ℝ)/(S:ℝ)) :=
      mul_le_mul h3 h4 (pow_nonneg hμ0 _) (le_trans (pow_nonneg hμ0 _) h3)
    have key : (mub m)^(k*k) * (mub m)^(2*k+1) = (mub m)^((k+1)*(k+1)) := by
      have h : (k+1)*(k+1) = k*k + (2*k+1) := by ring
      rw [h, ← pow_add]
    calc (mub m)^((k+1)*(k+1))
        = (mub m)^(k*k) * (mub m)^(2*k+1) := key.symm
      _ ≤ ((s.ms:ℝ)/(S:ℝ)) * ((s.mo:ℝ)/(S:ℝ)) := hprod
      _ ≤ ((mu s.ms s.mo : ℤ) : ℝ)/(S:ℝ) := thmu_ge _ _
      _ ≤ (((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(S:ℝ) := by
            push_cast
            exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hS)
  refine ⟨hstep1, ?_, ?_⟩
  · have hmm2 : (mub m)^2 ≤ (((mu m m + 1 : ℤ)) : ℝ)/(S:ℝ) := by
      have hm2 : ((m:ℝ)/(S:ℝ)) * ((m:ℝ)/(S:ℝ)) = (mub m)^2 := by rw [mub]; ring
      calc (mub m)^2 = ((m:ℝ)/(S:ℝ)) * ((m:ℝ)/(S:ℝ)) := hm2.symm
        _ ≤ ((mu m m : ℤ) : ℝ)/(S:ℝ) := thmu_ge m m
        _ ≤ (((mu m m + 1 : ℤ)) : ℝ)/(S:ℝ) := by
              push_cast
              exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hS)
    have hprod : (mub m)^(2*k+1) * (mub m)^2
        ≤ ((s.mo:ℝ)/(S:ℝ)) * ((((mu m m + 1 : ℤ)) : ℝ)/(S:ℝ)) :=
      mul_le_mul h4 hmm2 (pow_nonneg hμ0 2) (le_trans (pow_nonneg hμ0 _) h4)
    have key : (mub m)^(2*k+1) * (mub m)^2 = (mub m)^(2*(k+1)+1) := by
      have h : 2*(k+1)+1 = 2*k+1 + 2 := by ring
      rw [h, ← pow_add]
    calc (mub m)^(2*(k+1)+1)
        = (mub m)^(2*k+1) * (mub m)^2 := key.symm
      _ ≤ ((s.mo:ℝ)/(S:ℝ)) * ((((mu m m + 1 : ℤ)) : ℝ)/(S:ℝ)) := hprod
      _ ≤ ((mu s.mo (mu m m + 1) : ℤ) : ℝ)/(S:ℝ) := thmu_ge _ _
      _ ≤ (((mu s.mo (mu m m + 1) + 1 : ℤ)) : ℝ)/(S:ℝ) := by
            push_cast
            exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hS)
  · set nn : ℤ := Int.ofNat (k+1) with hnn
    have hnnR : (nn:ℝ) = ((k+1 : ℕ) : ℝ) := by rw [hnn]; exact Int.cast_natCast (k+1)
    have hnn0 : (0:ℝ) ≤ (nn:ℝ) := by rw [hnnR]; positivity
    have hnn2 : ((((k+1)^2 : ℕ)) : ℝ) = (nn:ℝ) * (nn:ℝ) := by
      rw [hnnR]; push_cast; ring
    have hT1 : (((16 * (k+1)^2 + 1 : ℕ)) : ℝ) = 16 * ((nn:ℝ) * (nn:ℝ)) + 1 := by
      rw [hnnR]; push_cast; ring
    have hcast : (((s.dB + 2 * mu (nn * nn * dvu (mu s.ms s.mo + 1) m) rq
          + 16 * nn * nn + 1 : ℤ)) : ℝ)
        = (s.dB:ℝ) + 2 * ((mu (nn * nn * dvu (mu s.ms s.mo + 1) m) rq : ℤ) : ℝ)
          + 16 * ((nn:ℝ) * (nn:ℝ)) + 1 := by
      push_cast; ring
    have hE1 : 1 ≤ (k+1)^2 := by
      rw [pow_two]
      have hk1 : (1:ℕ) ≤ (k+1) := by omega
      calc (1:ℕ) = 1 * 1 := by ring
        _ ≤ (k+1) * (k+1) := Nat.mul_le_mul hk1 hk1
    have hB_S : (mub m)^((k+1)^2) ≤ (((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(S:ℝ) := by
      simpa only [pow_two] using hstep1
    have hBm : (mub m)^((k+1)^2 - 1) ≤ (((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(m:ℝ) := by
      have h1 : (mub m)^((k+1)^2) / (mub m)
          ≤ ((((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(S:ℝ)) / (mub m) :=
        div_le_div_of_nonneg_right hB_S (le_of_lt hμpos)
      have hpow : (mub m)^((k+1)^2) = (mub m)^((k+1)^2 - 1) * (mub m) := by
        rw [← pow_succ, Nat.sub_add_cancel hE1]
      have h2 : (mub m)^((k+1)^2) / (mub m) = (mub m)^((k+1)^2 - 1) := by
        rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hμpos)]
      have h3 : ((((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(S:ℝ)) / (mub m)
          = (((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(m:ℝ) := by
        rw [mub]
        exact div_div_div_cancel_right₀ thS_ne _ _
      rwa [h2, h3] at h1
    have hdvu : (((mu s.ms s.mo + 1 : ℤ)) : ℝ)/(m:ℝ)
        ≤ ((dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ)/(S:ℝ) := thdvu_ge _ _ hmpos
    have hcrux1 : (mub m)^((k+1)^2 - 1) * (rq:ℝ)
        ≤ ((dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ)/(S:ℝ) * (rq:ℝ) :=
      mul_le_mul_of_nonneg_right (le_trans hBm hdvu) hrqr
    have hcrux2 : (nn:ℝ) * (nn:ℝ) * (mub m)^((k+1)^2 - 1) * (rq:ℝ)
        ≤ ((mu (nn * nn * dvu (mu s.ms s.mo + 1) m) rq : ℤ) : ℝ) := by
      have h1 : (nn:ℝ) * (nn:ℝ) * ((mub m)^((k+1)^2 - 1) * (rq:ℝ))
          ≤ (nn:ℝ) * (nn:ℝ)
            * (((dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ)/(S:ℝ) * (rq:ℝ)) :=
        mul_le_mul_of_nonneg_left hcrux1 (mul_nonneg hnn0 hnn0)
      have h2 : (nn:ℝ) * (nn:ℝ)
            * (((dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ)/(S:ℝ) * (rq:ℝ))
          = ((nn * nn * dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ) * (rq:ℝ)/(S:ℝ) := by
        push_cast; ring
      have h3 : ((nn * nn * dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ) * (rq:ℝ)/(S:ℝ)
          ≤ ((mu (nn * nn * dvu (mu s.ms s.mo + 1) m) rq : ℤ) : ℝ) := mu_ge' _ _
      calc (nn:ℝ) * (nn:ℝ) * (mub m)^((k+1)^2 - 1) * (rq:ℝ)
          = (nn:ℝ) * (nn:ℝ) * ((mub m)^((k+1)^2 - 1) * (rq:ℝ)) := by ring
        _ ≤ (nn:ℝ) * (nn:ℝ)
              * (((dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ)/(S:ℝ) * (rq:ℝ)) := h1
        _ = ((nn * nn * dvu (mu s.ms s.mo + 1) m : ℤ) : ℝ) * (rq:ℝ)/(S:ℝ) := h2
        _ ≤ ((mu (nn * nn * dvu (mu s.ms s.mo + 1) m) rq : ℤ) : ℝ) := h3
    have hcrux : 2 * ((((k+1)^2 : ℕ)) : ℝ) * (mub m)^((k+1)^2 - 1) * (rq:ℝ)
        ≤ 2 * ((mu (nn * nn * dvu (mu s.ms s.mo + 1) m) rq : ℤ) : ℝ) := by
      rw [hnn2]
      linarith [hcrux2]
    rw [Bd2_succ, BdM2_succ, hcast, hT1]
    linarith [h5, hcrux]

end

end Work.Cert
