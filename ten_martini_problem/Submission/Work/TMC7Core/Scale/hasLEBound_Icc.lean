import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Scale.frob_tmC_le

/-!
# `HasLEBound` on a symmetric interval `Icc (-R) R`

The finite-scale exponent `u_N(x) = (1/N) log ‖A_N(x)‖_F` is bounded uniformly in `x`, in
`α`, in `N` and in the energy `E ∈ Icc (-R) R` by the single constant

`max 1 (log (sqrt ((R + 2|lam|)^2 + 2)))`.

The reason is that every transfer matrix `tmC lam E y = !![E - 2λcos 2πy, -1; 1, 0]` has
Frobenius norm at most `sqrt ((R + 2|lam|)^2 + 2)` when `|E| ≤ R` (its squared Frobenius norm
is `|E - 2λcos|^2 + 2`), and the Frobenius norm is submultiplicative, so the `N`-fold product
is bounded by the `N`-th power of that constant for `N ≥ 1`; taking logarithms and dividing
by `N` gives the claim.  The `max 1` handles the junk value `u_0 = 0`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

/-- `‖(r : ℂ)‖ = |r|`. -/
private lemma norm_cast_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- A single transfer matrix has Frobenius norm at most `sqrt ((R + 2|lam|)^2 + 2)` whenever
the (real) energy satisfies `|E| ≤ R`. -/
private lemma frob_tmC_le_sqrt (lam R E : ℝ) (hE : |E| ≤ R) (y : ℝ) :
    frob (tmC lam (E : ℂ) y) ≤ Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) := by
  have h1 : frob (tmC lam (E : ℂ) y) ≤ Real.sqrt ((‖(E : ℂ)‖ + 2 * |lam|) ^ 2 + 2) :=
    Work.TMC7Core.Scale.frob_tmC_le lam (E : ℂ) y
  rw [norm_cast_real] at h1
  refine le_trans h1 (Real.sqrt_le_sqrt ?_)
  have h2 : |E| + 2 * |lam| ≤ R + 2 * |lam| := by linarith
  have h3 : (0 : ℝ) ≤ |E| + 2 * |lam| := by positivity
  have h4 := pow_le_pow_left₀ h3 h2 2
  linarith [h4]

/-- For `N ≥ 1` the `N`-fold iterate of the transfer cocycle has Frobenius norm at most
`M^N`, where `M = sqrt ((R + 2|lam|)^2 + 2)` and `|E| ≤ R`. -/
private lemma frob_iterC_le_pow (lam R E : ℝ) (hE : |E| ≤ R) (α : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (x : ℝ) :
    frob (iterC α lam (E : ℂ) N x) ≤ (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) ^ N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  clear hN
  induction k with
  | zero =>
    have h1 : iterC α lam (E : ℂ) (1 + 0) x = tmC lam (E : ℂ) x := by
      rw [iterC_succ, iterC_zero, mul_one]
      norm_num
    rw [h1]
    simpa using frob_tmC_le_sqrt lam R E hE x
  | succ k ih =>
    have hsucc : iterC α lam (E : ℂ) (1 + (k + 1)) x
        = tmC lam (E : ℂ) (x + ((1 + k : ℕ) : ℝ) * α)
          * iterC α lam (E : ℂ) (1 + k) x := by
      have := iterC_succ α lam (E : ℂ) (1 + k) x
      simpa [Nat.add_assoc] using this
    rw [hsucc]
    calc frob (tmC lam (E : ℂ) (x + ((1 + k : ℕ) : ℝ) * α)
          * iterC α lam (E : ℂ) (1 + k) x)
        ≤ frob (tmC lam (E : ℂ) (x + ((1 + k : ℕ) : ℝ) * α))
            * frob (iterC α lam (E : ℂ) (1 + k) x) :=
          Cocycle.frob_mul_le _ _
      _ ≤ Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)
            * (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) ^ (1 + k) :=
          mul_le_mul (frob_tmC_le_sqrt lam R E hE _) ih (frob_nonneg _) (Real.sqrt_nonneg _)
      _ = (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) ^ (1 + (k + 1)) := by
          rw [show 1 + (k + 1) = (1 + k) + 1 by omega, pow_succ]
          ring

set_option linter.unusedVariables false in
theorem hasLEBound_Icc (lam R : ℝ) (hR : 0 ≤ R) :
    HasLEBound lam (Set.Icc (-R) R)
      (max 1 (Real.log (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)))) := by
  refine ⟨lt_of_lt_of_le (by linarith [hR]) (le_max_left _ _), ?_⟩
  intro E hE α N x
  obtain ⟨hER1, hER2⟩ := hE
  have hEabs : |E| ≤ R := abs_le.mpr ⟨hER1, hER2⟩
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp only [uAvg, Nat.cast_zero, div_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h
    have hfrob : frob (iterC α lam (E : ℂ) N x)
        ≤ (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) ^ N :=
      frob_iterC_le_pow lam R E hEabs α N h x
    have hfrobpos : (0 : ℝ) < frob (iterC α lam (E : ℂ) N x) :=
      lt_of_lt_of_le (by norm_num)
        (Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam (E : ℂ) N x))
    have hlog : Real.log (frob (iterC α lam (E : ℂ) N x))
        ≤ (N : ℝ) * Real.log (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) := by
      calc Real.log (frob (iterC α lam (E : ℂ) N x))
          ≤ Real.log ((Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) ^ N) :=
            Real.log_le_log hfrobpos hfrob
        _ = (N : ℝ) * Real.log (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) := Real.log_pow _ _
    rw [uAvg, div_le_iff₀ hNpos]
    calc Real.log (frob (iterC α lam (E : ℂ) N x))
        ≤ (N : ℝ) * Real.log (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)) := hlog
      _ ≤ (max 1 (Real.log (Real.sqrt ((R + 2 * |lam|) ^ 2 + 2)))) * (N : ℝ) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hNpos.le

end Work.TMC7Core.Scale
