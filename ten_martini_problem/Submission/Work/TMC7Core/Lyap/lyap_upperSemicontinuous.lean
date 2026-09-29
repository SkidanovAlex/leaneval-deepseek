import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Lyap.continuous_lyapAvg_energy

/-!
# Upper semicontinuity of the Lyapunov exponent in the energy

The Lyapunov exponent is *defined* (AJ (2.2)--(2.5), `Work.TMC7Core.lyap`) as the infimum

`lyap α lam E = ⨅ n, (1/(n+1)) ∫₀¹ log ‖A_{n+1}(x; E)‖_F dx`

of the continuous functions `f_n(E) = (1/(n+1)) ∫₀¹ log ‖A_{n+1}(x; E)‖_F dx`, which are
continuous in the energy by `continuous_lyapAvg_energy`.

An arbitrary infimum of continuous real-valued functions is upper semicontinuous, and here
the family is bounded below (each transfer iterate has determinant one, hence Frobenius norm
at least `√2 > 1`, so each `log` is nonnegative).  Concretely, for `ε > 0` pick `n` with
`f_n(E₀) < lyap E₀ + ε` — such an `n` exists because `⨅ ≤ f_n` for all `n` and `⨅ < ⨅ + ε`
— and then, by continuity of `f_n` at `E₀`, `f_n(E) < lyap E₀ + ε` for `E` near `E₀`, whence
`lyap E ≤ f_n(E) < lyap E₀ + ε`.

Nothing about `α, λ` or `E₀` is assumed: upper semicontinuity holds unconditionally.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMC7Core.Lyap

open Work.TMC7Core

/-- Every finite-scale Lyapunov average is nonnegative: transfer iterates have determinant
one, hence Frobenius norm at least `√2 > 1`, hence their logarithm is nonnegative.  In
particular the family whose infimum defines `lyap` is bounded below by `0`. -/
theorem lyapAvg_seq_bddBelow (α lam : ℝ) (E : ℂ) :
    BddBelow (Set.range fun n : ℕ =>
      (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  refine div_nonneg ?_ (by positivity)
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro u _
  refine Real.log_nonneg ?_
  have hle : Real.sqrt 2 ≤ frob (iterC α lam E (n + 1) u) :=
    Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam E (n + 1) u)
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  linarith

theorem lyap_upperSemicontinuous (α lam : ℝ) (E₀ : ℂ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ E in nhds E₀, lyap α lam E < lyap α lam E₀ + ε := by
  intro ε hε
  -- Step 1: choose a scale `n` at which the finite average is already within `ε` of `lyap E₀`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E₀ (n + 1) x))) / ((n : ℝ) + 1)
        < lyap α lam E₀ + ε := by
    have hlt : (⨅ n : ℕ,
        (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E₀ (n + 1) x))) / ((n : ℝ) + 1))
          < lyap α lam E₀ + ε := by
      rw [lyap]
      linarith
    exact exists_lt_of_ciInf_lt hlt
  -- Step 2: that fixed finite average is continuous in the energy, so it is `< lyap E₀ + ε`
  -- on a neighbourhood of `E₀`; on that neighbourhood `lyap` — being the infimum — is below it.
  have hcont := continuous_lyapAvg_energy α lam n
  filter_upwards [hcont.continuousAt.eventually (eventually_lt_nhds hn)] with E hE
  exact lt_of_le_of_lt (ciInf_le (lyapAvg_seq_bddBelow α lam E) n) hE

end Work.TMC7Core.Lyap

end
