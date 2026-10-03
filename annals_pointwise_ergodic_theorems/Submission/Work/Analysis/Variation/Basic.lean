/-
# Elementary API for the truncated variation seminorm

The main content here is that for a sequence anchored at `0` the supremum term of the full
variational norm is already dominated by the variation, so that `VrFull r K a ≤ 2 * Vr r K a`.
This is what lets every estimate proved for the seminorm `Vr` (in particular the Rademacher--
Menshov inequalities and Corollary `rm-bil`) be used for the full variational norm
`𝕍^r = sup + V^r` of Krause--Mirek--Tao.
-/
import Submission.Work.Analysis.Variation.Dyadic

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- The truncated variation seminorm is monotone in the truncation parameter. -/
theorem Vr_mono (r : ℝ) {K K' : ℕ} (h : K ≤ K') (a : ℕ → ℂ) : Vr r K a ≤ Vr r K' a := by
  unfold Vr
  apply iSup_le; intro J
  apply iSup_le; intro u
  apply iSup_le; intro hmono
  apply iSup_le; intro h0
  apply iSup_le; intro hu
  exact le_iSup_of_le J (le_iSup_of_le u (le_iSup_of_le hmono (le_iSup_of_le h0
    (le_iSup_of_le (fun i => le_trans (hu i) h) le_rfl))))

/-- For a sequence anchored at `0`, the supremum term of the variational norm is dominated by the
variation: `VrFull r K a ≤ 2 * Vr r K a` for `r ≥ 1`. -/
theorem VrFull_le_two_mul_Vr {r : ℝ} (hr : 1 ≤ r) {K : ℕ} {a : ℕ → ℂ} (h0 : a 0 = 0) :
    VrFull r K a ≤ 2 * Vr r K a := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hsup : (⨆ k : Fin (K + 1), ‖a k‖ₑ) ≤ Vr r K a := by
    refine iSup_le (fun k => ?_)
    have hklt : (k : ℕ) < K + 1 := k.isLt
    have hkK : (k : ℕ) ≤ K := by omega
    rcases eq_or_lt_of_le (Nat.zero_le (k : ℕ)) with hk | hk
    · have hk0 : a (k : ℕ) = 0 := by rw [hk.symm]; exact h0
      rw [hk0, enorm_zero]
      exact bot_le
    · set n : ℕ := (k : ℕ) with hn
      have hnpos : 0 < n := hk
      have hnle : n ≤ K := by rw [hn]; exact hkK
      let u : Fin 2 → ℕ := ![0, n]
      have hu0 : u 0 = 0 := rfl
      have humono : Monotone u := by
        rw [Fin.monotone_iff_le_succ]
        intro i
        fin_cases i
        simp [u]
      have hule : ∀ i, u i ≤ K := by
        intro i
        fin_cases i
        · simp [u]
        · simp [u]
          omega
      have hsum : (∑ j : Fin 1, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ r)
          = ‖a n - a 0‖ₑ ^ r := by
        rw [Fin.sum_univ_one]
        have h1 : u (0 : Fin 1).succ = n := by simp [u]
        have h2 : u (0 : Fin 1).castSucc = 0 := by simp [u]
        rw [h1, h2]
      have hpow : (‖a n‖ₑ ^ r) ^ (1 / r) = ‖a n‖ₑ := by
        rw [one_div]
        exact ENNReal.rpow_rpow_inv (ne_of_gt hr0) _
      calc ‖a k‖ₑ = ‖a n‖ₑ := by rw [hn]
        _ = (‖a n‖ₑ ^ r) ^ (1 / r) := hpow.symm
        _ = (∑ j : Fin 1, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ r) ^ (1 / r) := by
              rw [hsum, h0, sub_zero]
        _ ≤ Vr r K a :=
              le_iSup_of_le 1 (le_iSup_of_le u (le_iSup_of_le humono (le_iSup_of_le hu0
                (le_iSup_of_le hule le_rfl))))
  rw [VrFull]
  calc (⨆ k : Fin (K + 1), ‖a k‖ₑ) + Vr r K a ≤ Vr r K a + Vr r K a := add_le_add hsup le_rfl
    _ = 2 * Vr r K a := by ring

end Work.Analysis.Variation
