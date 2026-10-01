import Mathlib
import Submission.Work.LinnikBurgess.lf_defs

namespace Work.LinnikBurgess

open Polynomial

/-- A support point `y` of Lemma A with `T ≤ nval y` witnesses `DLp p T a b`
(`T = capLevel p e`).

Hints: `SuppTransfer` gives `b_y = min (nval y) T = T` and `p^(m+T) ∣ N(y)`, hence `p^T ∣ N(y)`
(`T ≤ m+T`); and `T ≤ nval y` gives `p^T ∣ N'(y)`.  The witness is `y` itself, a unit at `p`. -/
theorem DLp_of_cap {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) {y : ℕ} (hy : suppPred p e a b y) (hbt : SuppTransfer p e a b)
    (hcap : capLevel p e ≤ nval p e a b y) :
    DLp p (capLevel p e) a b := by
  obtain ⟨hunit, _hsupp⟩ := hy
  obtain ⟨hbval, hNdvd⟩ := hbt y ⟨hunit, _hsupp⟩
  refine ⟨y, hunit, ?_, ?_⟩
  · -- `p^T ∣ N(y)`: the transfer gives `p^(m + b_y) ∣ N(y)` with `b_y = min (nval y) T = T`.
    have hb : bval p e a b y = capLevel p e := by
      rw [hbval, min_eq_right hcap]
    have hmT : capLevel p e ≤ cubeLevel p e + capLevel p e := Nat.le_add_left _ _
    refine dvd_trans ?_ hNdvd
    rw [hb]
    exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hmT)
  · -- `p^T ∣ N'(y)`: either `N'(y) = 0`, or `T ≤ v_p(N'(y)) = nval y`.
    by_cases hz : (derivative (critN a b)).eval (y : ℤ) = 0
    · rw [hz]; exact dvd_zero _
    · have hnval : nval p e a b y
          = padicValNat p ((derivative (critN a b)).eval (y : ℤ)).natAbs := by
        unfold nval
        rw [if_neg hz]
      have hle : capLevel p e ≤
          padicValNat p ((derivative (critN a b)).eval (y : ℤ)).natAbs := by
        rw [← hnval]; exact hcap
      have hdvd : p ^ capLevel p e ∣ ((derivative (critN a b)).eval (y : ℤ)).natAbs :=
        (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hz)).mpr hle
      exact Int.natCast_dvd.mpr hdvd

end Work.LinnikBurgess
