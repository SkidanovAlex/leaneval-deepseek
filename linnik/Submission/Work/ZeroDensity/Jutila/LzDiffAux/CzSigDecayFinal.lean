import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux
import Submission.Work.ZeroDensity.Jutila.MsqAux.CzRIISumBounds

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

/-!
# The `σ_{-1/2}`-weighted decay sum against the de la Vallée Poussin envelope

For `c > 0` there is `C > 0` with, for every `b > 0` and `R ≥ 1`,

  `Σ_{r ≤ R} σ_{-1/2}(r)·exp(−c√(log(b·r))) ≤ C·(1/b + R·exp(−c√(log(b·R))))`,

where `σ_{-1/2}(r) = czSig r = Σ_{d ∣ r} d^{-1/2}` and `czEps c x = exp(−c√(log x))`.

The proof is a reduction to the (already available, unconditional) divisor-sum estimate
`Work.ZeroDensity.Jutila.MsqAux.czRII_czSigEpsR_sum_le`: expanding `σ_{-1/2}` over the divisors
and instantiating its shape parameters `w = 4b`, `y = 1` turns its envelope argument
`w·r/(4y)` into exactly `b·r`.  Its input `hE` is the enveloped sum bound
`Σ_{m ≤ M} czEps c (a·m) ≤ Ke·M·czEps c (a·M)`, valid for every `a > 0`, supplied by
`Work.ZeroDensity.Jutila.MsqAux.czRII_eps_sum_le`.  The right-hand side `R·czEps c (b·R)` is
then absorbed into `1/b + R·czEps c (b·R)` because `1/b > 0` and `czEps ≥ 0`.
-/

/-- **`σ_{-1/2}`-weighted envelope decay, uniform in the shift `b > 0`.** -/
theorem CzSigDecayFinal (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ) (R : ℕ), 0 < b → 1 ≤ R →
      (∑ r ∈ Finset.Icc 1 R, Work.ZeroDensity.Jutila.BzCross.czSig r * Work.ZeroDensity.Jutila.BzCross.czEps c (b * (r : ℝ)))
      ≤ C * (1 / b + (R : ℝ) * Work.ZeroDensity.Jutila.BzCross.czEps c (b * (R : ℝ))) := by
  obtain ⟨Ke, hKe, hE⟩ := Work.ZeroDensity.Jutila.MsqAux.czRII_eps_sum_le c hc.le
  refine ⟨3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)), by positivity, ?_⟩
  intro b R hb hR
  have hw : 0 < 4 * b := by linarith
  have hkey := Work.ZeroDensity.Jutila.MsqAux.czRII_czSigEpsR_sum_le c hc.le Ke hKe hE
    (w := 4 * b) (y := 1) hw (by norm_num) R
  -- identifying the two envelope arguments: `(4b)·r/(4·1) = b·r`
  have hconv : ∀ r : ℕ, czSig r * czEps c (b * (r : ℝ))
      = (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR c ((4 * b) * (r : ℝ) / (4 * 1)) := by
    intro r
    have harg : b * (r : ℝ) = (4 * b) * (r : ℝ) / (4 * 1) := by ring
    rw [czSig, harg]
    rfl
  have hargR : (4 * b) * (R : ℝ) / (4 * 1) = b * (R : ℝ) := by ring
  have hmain : (∑ r ∈ Finset.Icc 1 R, czSig r * czEps c (b * (r : ℝ)))
      ≤ 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (R : ℝ) * czEps c (b * (R : ℝ)) := by
    calc (∑ r ∈ Finset.Icc 1 R, czSig r * czEps c (b * (r : ℝ)))
        = ∑ r ∈ Finset.Icc 1 R,
            (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR c ((4 * b) * (r : ℝ) / (4 * 1)) :=
          Finset.sum_congr rfl (fun r _ => hconv r)
      _ ≤ 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (R : ℝ)
            * czEpsR c ((4 * b) * (R : ℝ) / (4 * 1)) := hkey
      _ = 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (R : ℝ) * czEps c (b * (R : ℝ)) := by
          rw [hargR]
          rfl
  refine hmain.trans ?_
  have hC : (0 : ℝ) ≤ 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) := by positivity
  have hφ : (0 : ℝ) ≤ czEps c (b * (R : ℝ)) := (czEps_pos c _).le
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have h1b : (0 : ℝ) < 1 / b := by
    rw [one_div_pos]
    exact hb
  have hle : (R : ℝ) * czEps c (b * (R : ℝ)) ≤ 1 / b + (R : ℝ) * czEps c (b * (R : ℝ)) := by
    linarith
  calc 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (R : ℝ) * czEps c (b * (R : ℝ))
      = (3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)))
          * ((R : ℝ) * czEps c (b * (R : ℝ))) := by ring
    _ ≤ (3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)))
          * (1 / b + (R : ℝ) * czEps c (b * (R : ℝ))) := mul_le_mul_of_nonneg_left hle hC

end

end Work.ZeroDensity.Jutila.LzDiffAux
