import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory
open scoped Real BigOperators

/-- The squared `L²`-norm of the total excited part `Σ_k Q_k ψ` over the centred
box is dominated by `N²` times the squared `L²`-norm of `ψ`.

This is the elementary Cauchy–Schwarz step
`(Σ_k Q_k ψ)² ≤ N · Σ_k (Q_k ψ)²` integrated over `abox N s`, together with the
projection contraction `∫(Q_k ψ)² ≤ ∫ψ²` (`Q0Sector`/`CentredSector`:
`∫ψ² = ∫(P_kψ)² + ∫(Q_kψ)²` with `∫(P_kψ)² ≥ 0`). -/
lemma aQsum_sq_integral_le {N : ℕ} {s : ℝ} (hs : 0 < s) {ψ : Submission.BoseGases.X N → ℝ} (hψc : Continuous ψ) :
    ∫ x in Submission.BoseGases.abox N s, (∑ k : Fin N, Submission.BoseGases.aQ s k ψ x) ^ 2
      ≤ (N : ℝ) ^ 2 * ∫ x in Submission.BoseGases.abox N s, (ψ x) ^ 2 := by
  have hcont : ∀ k : Fin N, Continuous (Submission.BoseGases.aQ s k ψ) :=
    fun k => Submission.BoseGases.aQ_continuous hs k hψc
  -- integrand on the left
  have hLc : Continuous (fun x : Submission.BoseGases.X N =>
      (∑ k : Fin N, Submission.BoseGases.aQ s k ψ x) ^ 2) :=
    (continuous_finsetSum (Finset.univ : Finset (Fin N)) (fun k _ => hcont k)).pow 2
  -- integrand on the right of the first (Cauchy–Schwarz) step
  have hRc : Continuous (fun x : Submission.BoseGases.X N =>
      (N : ℝ) * ∑ k : Fin N, (Submission.BoseGases.aQ s k ψ x) ^ 2) :=
    continuous_const.mul (continuous_finsetSum (Finset.univ : Finset (Fin N))
      (fun k _ => (hcont k).pow 2))
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ x : Submission.BoseGases.X N,
      (∑ k : Fin N, Submission.BoseGases.aQ s k ψ x) ^ 2
        ≤ (N : ℝ) * ∑ k : Fin N, (Submission.BoseGases.aQ s k ψ x) ^ 2 := by
    intro x
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun k => Submission.BoseGases.aQ s k ψ x)
    simpa using h
  have hLint : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (∑ k : Fin N, Submission.BoseGases.aQ s k ψ x) ^ 2) (Submission.BoseGases.abox N s) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hs hLc
  have hRint : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (N : ℝ) * ∑ k : Fin N, (Submission.BoseGases.aQ s k ψ x) ^ 2) (Submission.BoseGases.abox N s) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hs hRc
  have hstep1 := integral_mono hLint hRint hpt
  -- pull the constant and the sum out of the integral
  have hstep2 : ∫ x in Submission.BoseGases.abox N s,
        (N : ℝ) * ∑ k : Fin N, (Submission.BoseGases.aQ s k ψ x) ^ 2
      = (N : ℝ) * ∑ k : Fin N, ∫ x in Submission.BoseGases.abox N s,
          (Submission.BoseGases.aQ s k ψ x) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum (Finset.univ)
      (fun k _ => Submission.BoseGases.integrableOn_sq_aQ hs k hψc)
  -- projection contraction for each slot
  have hQk : ∀ k : Fin N, ∫ x in Submission.BoseGases.abox N s, (Submission.BoseGases.aQ s k ψ x) ^ 2
      ≤ ∫ x in Submission.BoseGases.abox N s, (ψ x) ^ 2 := by
    intro k
    have hdec := Submission.BoseGases.sq_norm_decomp hs k hψc
    have hPnn : 0 ≤ ∫ x in Submission.BoseGases.abox N s, (Submission.BoseGases.aP s k ψ x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    linarith
  have hstep3 : (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N s, (Submission.BoseGases.aQ s k ψ x) ^ 2)
      ≤ ∑ k : Fin N, ∫ x in Submission.BoseGases.abox N s, (ψ x) ^ 2 :=
    Finset.sum_le_sum (fun k _ => hQk k)
  have hstep4 : (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N s, (ψ x) ^ 2)
      = (N : ℝ) * ∫ x in Submission.BoseGases.abox N s, (ψ x) ^ 2 := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  calc
    ∫ x in Submission.BoseGases.abox N s, (∑ k : Fin N, Submission.BoseGases.aQ s k ψ x) ^ 2
        ≤ ∫ x in Submission.BoseGases.abox N s,
            (N : ℝ) * ∑ k : Fin N, (Submission.BoseGases.aQ s k ψ x) ^ 2 := hstep1
    _ = (N : ℝ) * ∑ k : Fin N, ∫ x in Submission.BoseGases.abox N s,
          (Submission.BoseGases.aQ s k ψ x) ^ 2 := hstep2
    _ ≤ (N : ℝ) * ((N : ℝ) * ∫ x in Submission.BoseGases.abox N s, (ψ x) ^ 2) :=
        mul_le_mul_of_nonneg_left (le_trans hstep3 (le_of_eq hstep4)) (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ 2 * ∫ x in Submission.BoseGases.abox N s, (ψ x) ^ 2 := by ring

end Work.SmallBoxA0
