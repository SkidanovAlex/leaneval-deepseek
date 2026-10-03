import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The `ℓ¹`/`ℓ^{2t}` power-mean inequality

`(Σ_{x∈[-N,N]} ‖f x‖)^{2t} ≤ (2N+1)^{2t-1} Σ_{x∈[-N,N]}‖f x‖^{2t}`: the Hölder/power-mean
inequality that converts the `a = 0` lower bound for `linFamAvg` (an `ℓ^{2t}` mass) into the `ℓ¹`
mass which the trivial bound on `ΛMD` controls.  See `NOTES_petChapter5_session13.md` §B.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

theorem l1_pow_lower (f : ℤ → ℂ) (N t : ℕ) (hN : 0 < N) (ht : 1 ≤ t) :
    (∑ x ∈ symIcc N, ‖f x‖) ^ (2 * t)
      ≤ (((2 * N + 1 : ℕ) : ℝ) ^ (2 * t - 1)) * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) := by
  classical
  have hcard : (symIcc N).card = 2 * N + 1 := by
    rw [symIcc, Int.card_Icc]
    omega
  have hp1 : (1 : ℝ) ≤ ((2 * t : ℕ) : ℝ) := by
    have : 1 ≤ 2 * t := by omega
    exact_mod_cast this
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := symIcc N)
    (f := fun x => ‖f x‖) (p := ((2 * t : ℕ) : ℝ)) hp1 (fun i _ => norm_nonneg _)
  have hL : (∑ x ∈ symIcc N, ‖f x‖) ^ (((2 * t : ℕ) : ℝ))
      = (∑ x ∈ symIcc N, ‖f x‖) ^ (2 * t) := Real.rpow_natCast _ _
  have hR2 : (∑ x ∈ symIcc N, ‖f x‖ ^ (((2 * t : ℕ) : ℝ)))
      = ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) :=
    Finset.sum_congr rfl (fun x _ => Real.rpow_natCast _ _)
  have h3 : ((symIcc N).card : ℝ) ^ (((2 * t : ℕ) : ℝ) - 1)
      = (((2 * N + 1 : ℕ) : ℝ)) ^ (2 * t - 1) := by
    rw [hcard]
    have he : ((2 * t : ℕ) : ℝ) - 1 = ((2 * t - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub (show 1 ≤ 2 * t by omega)]
    rw [he, Real.rpow_natCast]
  rw [hL, hR2, h3] at h
  exact h

end Work.Peluse.UControl
