import Mathlib
import Submission.Work.ZeroDensity.Jutila.JutilaDefs
import Submission.Work.ZeroDensity.Jutila.riemannZeta_eq_ofReal_zetaZ
import Submission.Work.ZeroDensity.Jutila.deriv_riemannZeta_eq_neg_ofReal_zetaW
import Submission.Work.ZeroDensity.Jutila.summable_zetaW
import Submission.Work.ZeroDensity.Jutila.tail_rpow_le

namespace Work.ZeroDensity.Jutila

/-!
# An explicit upper bound for `-Re (ζ'/ζ)` on the real axis

The main content of this file is the elementary inequality

    `zetaW σ ≤ zetaZ σ / (σ - 1)`   (`σ > 1`),

where `zetaW σ = ∑ n^{-σ} log n = -ζ'(σ)` and `zetaZ σ = ∑ n^{-σ} = ζ(σ)`
(see `JutilaDefs.lean`).  Dividing by `zetaZ σ > 0` gives
`-ζ'/ζ(σ) = zetaW σ / zetaZ σ ≤ 1/(σ-1)`, hence the stated bound with the extra `+ 1`.

The proof of `zetaW σ ≤ zetaZ σ/(σ-1)` rewrites `log n = ∑_{i<n} (log(i+1) - log i)`,
interchanges the two (triangular) finite sums with `Finset.sum_Ico_Ico_comm'`, and
uses the two elementary bounds `log(i+1) - log i ≤ 1/i` and
`∑_{n>i} n^{-σ} ≤ i^{1-σ}/(σ-1)` (`tail_rpow_le`).
-/

open Finset

/-- Telescoping: `log n = ∑_{1 ≤ i < n} (log (i+1) - log i)` for `n ≥ 1`. -/
lemma log_eq_sum_Ico (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n : ℝ) = ∑ i ∈ Finset.Ico 1 n, (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) := by
  have heq : (∑ i ∈ Finset.Ico 1 n, (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)))
      = ∑ i ∈ Finset.Ico 1 n, (Real.log ((i + 1 : ℕ) : ℝ) - Real.log ((i : ℕ) : ℝ)) :=
    Finset.sum_congr rfl (fun i _ => by push_cast; ring_nf)
  rw [heq, Finset.sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hn]
  simp

/-- `log (1 + 1/i) ≤ 1/i`, i.e. `log (i+1) - log i ≤ 1/i` for `i ≥ 1`. -/
lemma log_succ_sub_log_le_inv (i : ℕ) (hi : 1 ≤ i) :
    Real.log ((i : ℝ) + 1) - Real.log (i : ℝ) ≤ 1 / (i : ℝ) := by
  have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have h1 : Real.log ((i : ℝ) + 1) - Real.log (i : ℝ) = Real.log (((i : ℝ) + 1) / (i : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity)]
  rw [h1]
  have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((i : ℝ) + 1) / (i : ℝ) by positivity)
  have h2 : ((i : ℝ) + 1) / (i : ℝ) - 1 = 1 / (i : ℝ) := by field_simp; ring
  linarith

/-- The finite partial sums of `zetaW` are bounded by `zetaZ σ/(σ-1)` for `σ > 1`. -/
lemma partial_sum_log_le (σ : ℝ) (hσ : 1 < σ) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) * (n : ℝ) ^ (-σ) ≤ zetaZ σ / (σ - 1) := by
  have hstep : (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) * (n : ℝ) ^ (-σ))
      = ∑ n ∈ Finset.Ico 1 N, ∑ i ∈ Finset.Ico 1 n,
          (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) * (n : ℝ) ^ (-σ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [log_eq_sum_Ico n (Finset.mem_Ico.mp hn).1, Finset.sum_mul]
  rw [hstep]
  rw [← Finset.sum_Ico_Ico_comm' 1 N
    (fun i j => (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) * (j : ℝ) ^ (-σ))]
  simp_rw [← Finset.mul_sum]
  have hsum_le : ∑ i ∈ Finset.Ico 1 N, (i : ℝ) ^ (-σ) ≤ zetaZ σ := by
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      have h := (Real.summable_one_div_nat_rpow (p := σ)).mpr hσ
      exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n), one_div])
    have := Summable.sum_le_tsum (Finset.Ico 1 N) (fun i _ => by positivity) hsum
    simpa [zetaZ] using this
  calc ∑ i ∈ Finset.Ico 1 N, (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) *
          (∑ n ∈ Finset.Ico (i + 1) N, (n : ℝ) ^ (-σ))
      ≤ ∑ i ∈ Finset.Ico 1 N, (i : ℝ) ^ (-σ) / (σ - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have hc : Real.log ((i : ℝ) + 1) - Real.log (i : ℝ) ≤ 1 / (i : ℝ) :=
          log_succ_sub_log_le_inv i hi1
        have hnn : 0 ≤ ∑ n ∈ Finset.Ico (i + 1) N, (n : ℝ) ^ (-σ) :=
          Finset.sum_nonneg (fun n _ => by positivity)
        have hA : (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) *
              (∑ n ∈ Finset.Ico (i + 1) N, (n : ℝ) ^ (-σ))
            ≤ (1 / (i : ℝ)) * (∑ n ∈ Finset.Ico (i + 1) N, (n : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_right hc hnn
        have hB : (1 / (i : ℝ)) * (∑ n ∈ Finset.Ico (i + 1) N, (n : ℝ) ^ (-σ))
            ≤ (1 / (i : ℝ)) * ((i : ℝ) ^ (1 - σ) / (σ - 1)) :=
          mul_le_mul_of_nonneg_left (tail_rpow_le σ hσ i N hi1) (by positivity)
        have hi0 : (0 : ℝ) < (i : ℝ) := by positivity
        have hC : (1 / (i : ℝ)) * ((i : ℝ) ^ (1 - σ) / (σ - 1)) = (i : ℝ) ^ (-σ) / (σ - 1) := by
          have hexp : (-1 : ℝ) + (1 - σ) = -σ := by ring
          rw [← mul_div_assoc, one_div, ← Real.rpow_neg_one, ← Real.rpow_add hi0, hexp]
        rw [hC] at hB
        linarith [hA, hB]
    _ = (∑ i ∈ Finset.Ico 1 N, (i : ℝ) ^ (-σ)) / (σ - 1) := (Finset.sum_div _ _ _).symm
    _ ≤ zetaZ σ / (σ - 1) := div_le_div_of_nonneg_right hsum_le (by linarith)

/-- The key elementary estimate: for `σ > 1`, `∑ n^{-σ} log n ≤ (∑ n^{-σ})/(σ-1)`. -/
lemma zetaW_le_zetaZ_div (σ : ℝ) (hσ : 1 < σ) : zetaW σ ≤ zetaZ σ / (σ - 1) := by
  have hps : ∀ N : ℕ,
      ∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) * (n : ℝ) ^ (-σ) ≤ zetaZ σ / (σ - 1) :=
    fun N => partial_sum_log_le σ hσ N
  have hsum : Summable (fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ (-σ)) := summable_zetaW σ hσ
  have hlim : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds (zetaW σ)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, Real.log (i : ℝ) * (i : ℝ) ^ (-σ))
        Filter.atTop (nhds (zetaW σ)) := hsum.hasSum.tendsto_sum_nat
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hf0 : Real.log ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by simp
    rw [show N = (N - 1) + 1 from (Nat.succ_pred_eq_of_pos hN).symm, Finset.sum_range_succ',
      Finset.sum_Ico_eq_sum_range]
    simp only [hf0, add_zero, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm 1 k]
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hps)

/-- Explicit upper bound for the real part of `-ζ'/ζ` on the real axis segment `1 < σ ≤ 3`:
`-Re (ζ'/ζ)(σ) ≤ 1/(σ-1) + 1`.

Numerically the true value is `1/(σ-1) - γ + O(σ-1)` near `σ = 1` and drops to `0.216` at `σ = 3`,
so the inequality is true with a lot of room.

Recommended route (the coefficient of `1/(σ-1)` must be exactly `1`):
* `deriv riemannZeta (σ:ℂ) = -Σ_n (log n) n^{-σ}` and `riemannZeta (σ:ℂ) = Σ_n n^{-σ}` (both as
  complex `tsum`s, e.g. from `LSeries_deriv` + `LSeries_one_eq_riemannZeta` + `Complex.ofReal_tsum`
  + `Filter.EventuallyEq.deriv_eq`, then take real parts);
* so `-ζ'/ζ(σ) = W / Z` with `W = Σ_n (Real.log n) n^{-σ}` and `Z = Σ_n n^{-σ} > 0`;
* the key input is the sharp bound `W ≤ Z / (σ-1)`, which follows from
  `log n = Σ_{i<n} (log (i+1) - log i)` telescoping, `log (1 + 1/i) ≤ 1/i`, and
  `Σ_{n>i} n^{-σ} ≤ i^{1-σ}/(σ-1)` (for which `AntitoneOn.sum_le_integral_Ico` in
  `Mathlib.Analysis.SumIntegralComparisons` plus `integral_rpow` is convenient):
  `W ≤ Σ_i (1/i) · i^{1-σ}/(σ-1) = (1/(σ-1)) Σ_i i^{-σ} = Z/(σ-1)`;
* finish with `W/Z ≤ 1/(σ-1) ≤ 1/(σ-1) + 1`.

An alternative for the last input is `ζ(σ) ≥ 1/(σ-1)` (also elementary) together with
`Σ_{n≥2}(log n)n^{-σ} ≤ φ(2) + φ(3) + 3^{1-σ}(log 3/(σ-1) + 1/(σ-1)²)` where
`φ(t) = (log t) t^{-σ}` is antitone on `[3,∞)`; here one additionally needs the sharper
`ζ(σ) ≥ 1 + 2^{1-σ}/(σ-1)`, and the final arithmetic closes with room. -/
theorem neg_zeta_logDeriv_re_le (σ : ℝ) (hσ1 : 1 < σ) (hσ3 : σ ≤ 3) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  have hz : riemannZeta (σ : ℂ) = (zetaZ σ : ℂ) := riemannZeta_eq_ofReal_zetaZ σ hσ1
  have hd : deriv riemannZeta (σ : ℂ) = -(zetaW σ : ℂ) :=
    deriv_riemannZeta_eq_neg_ofReal_zetaW σ hσ1
  have hkey : zetaW σ ≤ zetaZ σ / (σ - 1) := zetaW_le_zetaZ_div σ hσ1
  have hzp : 0 < zetaZ σ := by
    have h := riemannZeta_re_pos_of_one_lt hσ1
    rw [hz] at h
    simpa using h
  have hratio : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      = zetaW σ / zetaZ σ := by
    rw [hd, hz, neg_neg, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hratio]
  have h2 : zetaW σ / zetaZ σ ≤ 1 / (σ - 1) := by
    calc zetaW σ / zetaZ σ
        ≤ (zetaZ σ / (σ - 1)) / zetaZ σ := div_le_div_of_nonneg_right hkey (le_of_lt hzp)
      _ = 1 / (σ - 1) := by field_simp
  linarith [h2, one_div_pos.mpr (sub_pos.mpr hσ1)]

end Work.ZeroDensity.Jutila
