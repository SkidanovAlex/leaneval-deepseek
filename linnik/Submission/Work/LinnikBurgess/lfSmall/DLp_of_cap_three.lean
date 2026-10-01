import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.DLp_of_cap

open Polynomial

namespace Work.LinnikBurgess.lfSmall

theorem DLp_of_cap_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : suppPred 3 e a b y) (hbt : SuppTransfer 3 e a b)
    (hcap : capLevel 3 e ≤ nval 3 e a b y) :
    DLp 3 (capLevel 3 e) a b := by
  obtain ⟨hunit, _hsupp⟩ := hy
  obtain ⟨hbval, hNdvd⟩ := hbt y ⟨hunit, _hsupp⟩
  refine ⟨y, hunit, ?_, ?_⟩
  · -- `3^T ∣ N(y)`: the transfer gives `3^(m + b_y) ∣ N(y)` with `b_y = min (nval y) T = T`.
    have hb : bval 3 e a b y = capLevel 3 e := by
      rw [hbval, min_eq_right hcap]
    have hmT : capLevel 3 e ≤ cubeLevel 3 e + capLevel 3 e := Nat.le_add_left _ _
    refine dvd_trans ?_ hNdvd
    rw [hb]
    exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow 3 hmT)
  · -- `3^T ∣ N'(y)`: either `N'(y) = 0`, or `T ≤ v_3(N'(y)) = nval y`.
    by_cases hz : (derivative (critN a b)).eval (y : ℤ) = 0
    · rw [hz]; exact dvd_zero _
    · have hnval : nval 3 e a b y
          = padicValNat 3 ((derivative (critN a b)).eval (y : ℤ)).natAbs := by
        unfold nval
        rw [if_neg hz]
      have hle : capLevel 3 e ≤
          padicValNat 3 ((derivative (critN a b)).eval (y : ℤ)).natAbs := by
        rw [← hnval]; exact hcap
      have hdvd : 3 ^ capLevel 3 e
          ∣ ((derivative (critN a b)).eval (y : ℤ)).natAbs :=
        (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hz)).mpr hle
      exact Int.natCast_dvd.mpr hdvd

end Work.LinnikBurgess.lfSmall
