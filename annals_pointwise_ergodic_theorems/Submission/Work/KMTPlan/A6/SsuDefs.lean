/-
# Shared vocabulary for the single-scale estimate `ssu` of the low case of A6

This module fixes the objects appearing in the *proof* of the paper's Lemma `ssu`
(`Work.KMTPlan.A6.ssuBtwistExBdd`, the bounded-symbol variant of `ssuBtwistEx`):

* the twisted bilinear multiplier `BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF d u)` applied to the two
  exact-height modulated pieces `Tm ρ l₁ φ f`, `Tm ρ l₂ ψ g`;
* its comparison with the halved average `Ã_N` (`AhalfR TZ N X P`), which the paper effects by
  `mod-approx`; in this formalisation the comparison is done *directly* at the level of the
  frequency bands of `Tm` (the window `η_{≤-2u}` collapses each band to a single arithmetic
  frequency), and the arithmetic content is the mean of the character `n ↦ e(nα + β P(n))` over
  the window `{N/2+1, …, N}`.

The definitions below are pure notation: `ssuCoeff` (the band coefficient of the halved average),
`ssuPc` (the `ℓ¹` mass of the coefficients of `P`, used to bound `P` on `[0,N]`), and `ssuErr`
(the explicit error of the band realisation of `Ã_N`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BandDecomp
import Submission.Work.KMTPlan.A6.BtwistEx_eq_sum_bandPiece
import Submission.Work.KMTPlan.A6.MaeCollapse
import Submission.Work.KMTPlan.A6.ShiftModulation
import Submission.Work.KMTPlan.A6.periodic_window_deviation
import Submission.Work.KMTPlan.A6.mZ_period_eq
import Submission.Work.KMTPlan.A6.iwArithFreqs_separated
import Submission.Work.KMTPlan.A6.supportedInArc_periodize_of_support
import Submission.Work.KMTPlan.A6.exists_bound_BtwistEx_crude

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- The frequency circle `ℝ/ℤ` of the Ionescu--Wainger analysis. -/
abbrev SsuC : Type := Work.Analysis.IonescuWainger.Circle

/-- **The band coefficient of the halved average.**  The mean of the arithmetic character
`n ↦ e(nα + β P(n))` over the window `{N/2+1, …, N}`; it is the coefficient of the band piece
`A_α B_β` in the exact expansion of `Ã_N(A,B)`. -/
def ssuCoeff (P : Polynomial ℤ) (N : ℕ) (α β : SsuC) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
    fourier (T := 1) (n : ℤ) α * fourier (T := 1) (P.eval (n : ℤ)) β

theorem ssuCoeff_def (P : Polynomial ℤ) (N : ℕ) (α β : SsuC) :
    ssuCoeff P N α β
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          fourier (T := 1) (n : ℤ) α * fourier (T := 1) (P.eval (n : ℤ)) β := rfl

/-- The `ℓ¹` mass of the coefficients of `P`, used to bound `|P n|` on `[0,N]` by
`ssuPc P * N ^ P.natDegree`. -/
def ssuPc (P : Polynomial ℤ) : ℝ := ∑ i ∈ P.support, |((P.coeff i : ℤ) : ℝ)|

theorem ssuPc_nonneg (P : Polynomial ℤ) : 0 ≤ ssuPc P :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

theorem ssu_two_zpow_nonneg (m : ℤ) : (0 : ℝ) ≤ (2 : ℝ) ^ m :=
  zpow_nonneg (by norm_num) m

/-- The explicit error of the band realisation of the halved average `Ã_N`:
`2π(2^{-3u} N + (2^{-3du} N^d) · ‖P‖_{ℓ¹})`. -/
def ssuErr (P : Polynomial ℤ) (u N : ℕ) : ℝ :=
  2 * Real.pi * ((N : ℝ) * (2 : ℝ) ^ (-(3 * (u : ℤ)))
    + ssuPc P * ((N : ℝ) ^ P.natDegree) * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))

theorem ssuErr_nonneg (P : Polynomial ℤ) (u N : ℕ) : 0 ≤ ssuErr P u N := by
  have h1 : (0 : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ (-(3 * (u : ℤ))) :=
    mul_nonneg (Nat.cast_nonneg _) (ssu_two_zpow_nonneg _)
  have h2 : (0 : ℝ) ≤ ssuPc P * ((N : ℝ) ^ P.natDegree)
      * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))) :=
    mul_nonneg (mul_nonneg (ssuPc_nonneg P) (pow_nonneg (Nat.cast_nonneg N) _))
      (ssu_two_zpow_nonneg _)
  have h3 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  exact mul_nonneg h3 (add_nonneg h1 h2)

/-- **The evaluation bound for `ssuPc`.**  For `n ≤ N` with `N ≥ 1` one has
`|P n| ≤ ssuPc P · N^{deg P}`. -/
theorem ssuPc_eval_bound (P : Polynomial ℤ) (N n : ℕ) (hN : 1 ≤ N) (hn : n ≤ N) :
    |(((P.eval (n : ℤ) : ℤ)) : ℝ)| ≤ ssuPc P * (N : ℝ) ^ P.natDegree := by
  have hcast : (((P.eval (n : ℤ) : ℤ)) : ℝ)
      = ∑ i ∈ P.support, (((P.coeff i : ℤ)) : ℝ) * (n : ℝ) ^ i := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    push_cast
    rfl
  rw [hcast]
  calc |∑ i ∈ P.support, (((P.coeff i : ℤ)) : ℝ) * (n : ℝ) ^ i|
      ≤ ∑ i ∈ P.support, |(((P.coeff i : ℤ)) : ℝ) * (n : ℝ) ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ P.support, |(((P.coeff i : ℤ)) : ℝ)| * (n : ℝ) ^ i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hnn : (0 : ℝ) ≤ (n : ℝ) ^ i := pow_nonneg (Nat.cast_nonneg n) i
        rw [abs_mul]
        exact congrArg (fun z => |(((P.coeff i : ℤ)) : ℝ)| * z) (abs_of_nonneg hnn)
    _ ≤ ∑ i ∈ P.support, |(((P.coeff i : ℤ)) : ℝ)| * (N : ℝ) ^ P.natDegree := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hle : i ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp i hi
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc (n : ℝ) ^ i ≤ (N : ℝ) ^ i := by
              exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn) i
          _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ (by exact_mod_cast hN) hle
    _ = ssuPc P * (N : ℝ) ^ P.natDegree := by
        rw [ssuPc, Finset.sum_mul]

/-- On a probability space, `L^∞` is contained in `L²`. -/
theorem memLp_two_of_memLp_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {Φ : α → ℂ} (h : MemLp Φ ⊤ μ) : MemLp Φ 2 μ :=
  h.mono_exponent (by norm_num)

/-- **The halved average of the band comparison, in integer-shift form.**
`ssuAvg P N h k x = N⁻¹ ∑_{N/2 < n ≤ N} h (x - n) k (x - P(n))`.  This is the object compared
with `BtwistEx` (it is `Submission.PointwiseErgodicTheorems.AhalfR TZ N X P h k`, see
`Work.KMTPlan.A6.ssuAvg_eq_AhalfR`), written without the measurable-equivalence machinery so that
it can be used in the statements of the delegated band estimates. -/
def ssuAvg (P : Polynomial ℤ) (N : ℕ) (h k : ℤ → ℂ) : ℤ → ℂ :=
  fun x => (((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc (N / 2) N,
    h (x - (n : ℤ)) * k (x - P.eval (n : ℤ))

theorem ssuAvg_def (P : Polynomial ℤ) (N : ℕ) (h k : ℤ → ℂ) :
    ssuAvg P N h k
      = fun x => (((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc (N / 2) N,
          h (x - (n : ℤ)) * k (x - P.eval (n : ℤ)) := rfl

end

end Work.KMTPlan.A6
