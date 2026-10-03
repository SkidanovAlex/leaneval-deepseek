import Mathlib
import Submission.Work.FIArea6Road.HeartZcDefs
import Submission.Work.FIArea6Road.DivisorWindowDefs
import Submission.Work.FIArea6Road.tau_sq_le_d4
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 400000

/-!
## The divisor-square Dirichlet-series bound

We bound `∑_n τ(n)² n^{-σ} ≤ (1 + 1/(σ-1))⁴` for real `σ > 1`, where `τ(n) = #(n.divisors)`.

The route is the standard one: `τ(n)² ≤ d₄(n)` pointwise (`tau_sq_le_d4`), the Dirichlet series of
`d₄ = τ * τ` is `ζ(s)⁴`, and `ζ(σ) ≤ 1 + 1/(σ-1)` for real `σ > 1`.  The middle step is carried out
through `LSeries.convolution` (the `τ = 1 * 1` and `d₄ = τ * τ` identities), reproducing
`Submission.Work.FIArea6Road.ZsfunRightEdgeL1Bound`'s private development at the level of the
`d₄` series alone.
-/

/-- The divisor function `τ`, as a complex-valued sequence. -/
private def ftau : ℕ → ℂ := fun n => ((tauR n : ℝ) : ℂ)

/-- The four-fold divisor function `d₄ = τ * τ` as a complex-valued sequence. -/
private def fd4 : ℕ → ℂ := fun n => ((d4 n : ℝ) : ℂ)

private lemma conv_one_one_eq (n : ℕ) :
    (LSeries.convolution (1 : ℕ → ℂ) (1 : ℕ → ℂ)) n = ftau n := by
  rw [LSeries.convolution, ArithmeticFunction.mul_apply]
  have hmul : ∀ x ∈ n.divisorsAntidiagonal,
      (toArithmeticFunction (1 : ℕ → ℂ) x.1) * (toArithmeticFunction (1 : ℕ → ℂ) x.2)
        = (1 : ℂ) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hx1, hxn⟩ := hx
    have h1 : x.1 ≠ 0 := fun h => by rw [h, zero_mul] at hx1; exact hxn hx1.symm
    have h2 : x.2 ≠ 0 := fun h => by rw [h, mul_zero] at hx1; exact hxn hx1.symm
    simp [toArithmeticFunction, h1, h2]
  rw [Finset.sum_congr rfl hmul, Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℂ))]
  simp [ftau, tauR]

private lemma toAF_ftau_apply (m : ℕ) : (toArithmeticFunction ftau) m = ftau m := by
  rw [toArithmeticFunction]
  by_cases h : m = 0
  · subst h
    simp [ftau, tauR, Nat.divisors_zero]
  · simp [h]

private lemma conv_tau_tau_eq (n : ℕ) :
    (LSeries.convolution ftau ftau) n = fd4 n := by
  rw [LSeries.convolution, ArithmeticFunction.mul_apply]
  simp only [toAF_ftau_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal, ftau x.1 * ftau x.2)
        = ∑ x ∈ n.divisorsAntidiagonal, (((tauR x.1 * tauR x.2 : ℝ)) : ℂ) from
      Finset.sum_congr rfl (fun x _ => by simp [ftau, Complex.ofReal_mul])]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (((tauR a * tauR b : ℝ)) : ℂ))]
  simp only [fd4]
  rw [d4, Complex.ofReal_sum]

private lemma fd4_zero : fd4 0 = 0 := by
  simp [fd4, d4, Nat.divisors_zero]

private lemma fd4_LSeriesSummable {σ : ℝ} (hσ : 1 < σ) :
    LSeriesSummable fd4 ((σ : ℝ) : ℂ) := by
  have hσC : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  have hS1 : LSeriesSummable (1 : ℕ → ℂ) ((σ : ℝ) : ℂ) := LSeriesSummable_one_iff.mpr hσC
  have h11 : LSeriesSummable (LSeries.convolution (1 : ℕ → ℂ) (1 : ℕ → ℂ)) ((σ : ℝ) : ℂ) :=
    hS1.convolution hS1
  have hT : LSeriesSummable ftau ((σ : ℝ) : ℂ) :=
    (LSeriesSummable_congr ((σ : ℝ) : ℂ) (fun {n} _ => conv_one_one_eq n)).mp h11
  have hTT : LSeriesSummable (LSeries.convolution ftau ftau) ((σ : ℝ) : ℂ) :=
    hT.convolution hT
  exact (LSeriesSummable_congr ((σ : ℝ) : ℂ) (fun {n} _ => conv_tau_tau_eq n)).mp hTT

private lemma fd4_LSeries_eq {σ : ℝ} (hσ : 1 < σ) :
    LSeries fd4 ((σ : ℝ) : ℂ) = (riemannZeta ((σ : ℝ) : ℂ)) ^ (4 : ℕ) := by
  have hσC : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  have hS1 : LSeriesSummable (1 : ℕ → ℂ) ((σ : ℝ) : ℂ) := LSeriesSummable_one_iff.mpr hσC
  have h11 : LSeriesSummable (LSeries.convolution (1 : ℕ → ℂ) (1 : ℕ → ℂ)) ((σ : ℝ) : ℂ) :=
    hS1.convolution hS1
  have hT : LSeriesSummable ftau ((σ : ℝ) : ℂ) :=
    (LSeriesSummable_congr ((σ : ℝ) : ℂ) (fun {n} _ => conv_one_one_eq n)).mp h11
  have e1 : LSeries fd4 ((σ : ℝ) : ℂ)
      = LSeries (LSeries.convolution ftau ftau) ((σ : ℝ) : ℂ) :=
    LSeries_congr (fun {n} _ => (conv_tau_tau_eq n).symm) _
  have htau : LSeries ftau ((σ : ℝ) : ℂ) = (riemannZeta ((σ : ℝ) : ℂ)) ^ (2 : ℕ) := by
    have e2 : LSeries ftau ((σ : ℝ) : ℂ)
        = LSeries (LSeries.convolution (1 : ℕ → ℂ) (1 : ℕ → ℂ)) ((σ : ℝ) : ℂ) :=
      LSeries_congr (fun {n} _ => (conv_one_one_eq n).symm) _
    rw [e2, LSeries_convolution' hS1 hS1, LSeries_one_eq_riemannZeta hσC]
    ring
  rw [e1, LSeries_convolution' hT hT, htau]
  ring

private lemma fd4_term_eq (σ : ℝ) (n : ℕ) :
    LSeries.term fd4 ((σ : ℝ) : ℂ) n = (((d4 n * (n : ℝ) ^ (-σ) : ℝ)) : ℂ) := by
  rw [LSeries.term_def₀ fd4_zero]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [fd4, d4, Nat.divisors_zero]
  · have hpow : ((n : ℂ)) ^ (-((σ : ℝ) : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_neg σ,
        Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)]
    simp only [fd4]
    rw [hpow, Complex.ofReal_mul]

private lemma fd4_LSeries_eq_ofReal {σ : ℝ} :
    LSeries fd4 ((σ : ℝ) : ℂ) = (((∑' n : ℕ, d4 n * (n : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
  rw [LSeries]
  rw [show (∑' n : ℕ, LSeries.term fd4 ((σ : ℝ) : ℂ) n)
        = ∑' n : ℕ, (((d4 n * (n : ℝ) ^ (-σ) : ℝ)) : ℂ) from
      tsum_congr (fun n => fd4_term_eq σ n)]
  exact (Complex.ofReal_tsum _).symm

private lemma d4_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => d4 n * (n : ℝ) ^ (-σ)) := by
  have hsumm : Summable (LSeries.term fd4 ((σ : ℝ) : ℂ)) := fd4_LSeriesSummable hσ
  have h2 : Summable (fun n : ℕ => (((d4 n * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)) :=
    hsumm.congr (fun n => fd4_term_eq σ n)
  exact (Complex.summable_ofReal (f := fun n : ℕ => d4 n * (n : ℝ) ^ (-σ))).mp h2

private lemma d4_tsum_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, d4 n * (n : ℝ) ^ (-σ)) ≤ (1 + 1 / (σ - 1)) ^ (4 : ℕ) := by
  have hEq : (((∑' n : ℕ, d4 n * (n : ℝ) ^ (-σ)) : ℝ) : ℂ)
      = (riemannZeta ((σ : ℝ) : ℂ)) ^ (4 : ℕ) := by
    rw [← fd4_LSeries_eq_ofReal (σ := σ), fd4_LSeries_eq hσ]
  have hbound : ‖riemannZeta ((σ : ℝ) : ℂ)‖ ≤ 1 + 1 / (σ - 1) :=
    Commons.NumberTheory.LSeries.riemannZeta_norm_le_one_add_inv_sub_one σ hσ
  calc (∑' n : ℕ, d4 n * (n : ℝ) ^ (-σ))
      = Complex.re ((((∑' n : ℕ, d4 n * (n : ℝ) ^ (-σ)) : ℝ) : ℂ)) :=
        (Complex.ofReal_re _).symm
    _ = Complex.re ((riemannZeta ((σ : ℝ) : ℂ)) ^ (4 : ℕ)) := by rw [hEq]
    _ ≤ ‖(riemannZeta ((σ : ℝ) : ℂ)) ^ (4 : ℕ)‖ := Complex.re_le_norm _
    _ = ‖riemannZeta ((σ : ℝ) : ℂ)‖ ^ (4 : ℕ) := by rw [norm_pow]
    _ ≤ (1 + 1 / (σ - 1)) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 4

/-- **The divisor-square series bound.**  For real `σ > 1`,
`∑_n τ(n)² n^{-σ} ≤ (1 + 1/(σ-1))⁴`. -/
theorem ZsfunWitnessL1Key {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ))
      ≤ (1 + 1 / (σ - 1)) ^ (4 : ℕ) := by
  have hsumm2 : Summable (fun n : ℕ => d4 n * (n : ℝ) ^ (-σ)) := d4_summable hσ
  have hle : ∀ n : ℕ, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)
      ≤ d4 n * (n : ℝ) ^ (-σ) := by
    intro n
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    simpa only [tauR] using tau_sq_le_d4 n
  have hsumm1 : Summable (fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      hle hsumm2
  calc (∑' n : ℕ, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ))
      ≤ ∑' n : ℕ, d4 n * (n : ℝ) ^ (-σ) := hsumm1.tsum_le_tsum hle hsumm2
    _ ≤ (1 + 1 / (σ - 1)) ^ (4 : ℕ) := d4_tsum_le hσ

end

end Work.FIArea6Road
