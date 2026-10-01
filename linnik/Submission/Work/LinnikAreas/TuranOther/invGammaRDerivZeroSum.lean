import Mathlib
import Submission.Work.LinnikAreas.TuranOther.PFZeroSumDefs
import Submission.Work.LinnikAreas.TuranOther.invGammaRZeroSum
import Submission.Work.LinnikAreas.TuranOther.gammaRInvDeriv

namespace Work.LinnikAreas.TuranOther

/-!
# The zero-sum expansion of the derivatives of `logDeriv (Γ_ℝ(· + a))⁻¹`

For `k ≥ 1`, `a : ℕ` and `1 < t.re` we prove the Hadamard ("partial fraction") description of the
`k`-th derivative of the logarithmic derivative of the reciprocal archimedean factor

`f_a z = (Γ_ℝ (z + a))⁻¹`:

`(logDeriv f_a)^{(k)}(t) = (-1)^k k! · Σ_u ord_u(f_a) · (t - u)^{-(k+1)}`

(the right-hand side is `zeroSumK f_a t k`), together with the summability of the multiplicity
weighted kernel `u ↦ ord_u(f_a) · (t - u)^{-(k+1)}` over `u : ℂ`.

`f_a` is entire with simple zeros exactly at the trivial zeros `u = -(a + 2n)`, `n ≥ 0`; hence the
sum over `u : ℂ` collapses to the series `Σ_{n ≥ 0} (t + a + 2n)^{-(k+1)}`, which converges since
`k + 1 ≥ 2`.

The statement is assembled from the two halves of this computation, each proved separately:

* `invGammaR_zeroSum_eq` — the zero-set/multiplicity half: the multiplicity-weighted sum over
  `u : ℂ` is summable and equals the trivial-zero series
  `Σ_n (t + a + 2n)^{-(k+1)}`;
* `gammaRInvDeriv` — the analytic half: the `k`-th derivative of `logDeriv f_a` at `t` equals
  `(-1)^k k!` times the same series (obtained from
  `gammaRDerivSeries` for `logDeriv Γ_ℝ` and the Hurwitz-type series `digammaDerivSeries`
  for the derivatives of `ψ = logDeriv Γ`).
-/

theorem invGammaRDerivZeroSum (a : ℕ) (ha : a = 0 ∨ a = 1) (k : ℕ) (hk : 1 ≤ k)
    {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)) ∧
      iteratedDeriv k (logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)) t =
        (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * Work.LinnikAreas.TuranOther.zeroSumK (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) t k := by
  -- the zero sum is summable and is the trivial-zero series `Σ_n (t + a + 2n)^{-(k+1)}`
  obtain ⟨hsum, hzeroSum⟩ := invGammaR_zeroSum_eq a k hk ht
  refine ⟨hsum, ?_⟩
  -- the `k`-th derivative is `(-1)^k k!` times that same series
  rw [gammaRInvDeriv a ha k hk ht, hzeroSum]

end Work.LinnikAreas.TuranOther
