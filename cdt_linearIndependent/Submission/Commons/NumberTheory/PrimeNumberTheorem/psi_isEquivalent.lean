import Mathlib
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real

open Filter Asymptotics
open scoped Topology

namespace Commons.NumberTheory.PrimeNumberTheorem

/-- The prime-number asymptotic in the Chebyshev `ψ` form: `ψ(x) = Σ_{p^k ≤ x} log p`
is asymptotic to `x`.  (Neither this asymptotic nor the version in arithmetic
progressions is available in this Mathlib snapshot; the Chebyshev functions `ψ`, `θ`
live in `Mathlib.NumberTheory.Chebyshev`, and `riemannZeta_ne_zero_of_one_le_re`,
the Euler product and the analytic continuation of `ζ` are available.)

Suggested route: the Dirichlet series `-ζ'/ζ(s) = Σ Λ n / n^s` for `Re s > 1`, the
non-vanishing of `ζ` on `Re s ≥ 1`, and a Tauberian result (Ikehara/Newman: for a
Dirichlet series `Σ a n / n^s` with `a n ≥ 0` extending meromorphically slightly
beyond `Re s ≥ 1` with only a simple pole at `s = 1` of residue `1`, one gets
`Σ_{n ≤ x} a n ~ x`), followed by Abel summation. -/
theorem psi_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop (fun x : ℝ => Chebyshev.psi x) (fun x : ℝ => x) := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  -- Prime number theorem with a power-of-log error term, in `ψ` form.
  obtain ⟨x₀, hx₀⟩ := Commons.NumberTheory.Zeta.psi_sub_id_powLog_real 1 zero_lt_one
  -- Eventually `log x ≥ 1 / c`.
  have hlog : ∀ᶠ x : ℝ in atTop, (1 : ℝ) / c ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 / c))
  filter_upwards [eventually_ge_atTop (max x₀ 3), hlog] with x hx hlogx
  have hx₀x : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : 1 ≤ c * Real.log x := by
    have := (div_le_iff₀ hc).mp hlogx
    simpa [mul_comm] using this
  have hbound : |Chebyshev.psi x - x| ≤ x / Real.log x := by
    simpa [Real.rpow_one] using hx₀ x hx₀x
  have hmain : |Chebyshev.psi x - x| ≤ c * x := by
    refine hbound.trans ?_
    rw [div_le_iff₀ hlogpos]
    nlinarith [h1, hlogpos, hxpos]
  simpa [Real.norm_eq_abs, abs_of_pos hxpos] using hmain

end Commons.NumberTheory.PrimeNumberTheorem
