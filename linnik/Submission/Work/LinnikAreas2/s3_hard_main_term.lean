import Mathlib
import Submission.Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3GAuxDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3RouteAccumB
import Submission.Work.LinnikAreas2.S3Hard2.ModelEval

namespace Work.LinnikAreas2

/-- **Main term `Σ_A` of the `S₃` computation of `Σ_{n≤N}B_z(n)²`** (Graham 1978; An, arXiv:2206.10104, §5, case `w y > x`, specialised to `k = ℚ`, `w = y = z`).

For `2 ≤ z ≤ N < z²`, the triple sum over `q ≤ N/z`, `r, t ≤ N/(qz)` of the Möbius multiplier
`[r ⟂ t]·μ(r)·μ(t)` times `s3c(rt)·⌊N/(qrt)⌋·((log(⌊N/(qrt)⌋·t/z) − 1)·(log(⌊N/(qrt)⌋·r/z) − 1) + 1)`
equals `N·log(N/z) + O(N)`, with `s3c(rt) = ζ(2)^{-1}∏_{p|rt}p/(p+1)` written out explicitly in the statement.

Numerically checked (z = 10, N = 99: sum = 157.890 vs N·log(N/z) = 226.961, diff ≈ −0.70·N; z = 100, N = 1000: 1590.791 vs 2302.585; z = 50, N = 2499: 7978.5 vs 9775.1).

ROUTE.  Write `log(⌊N/(qrt)⌋·t/z) = log(N/(qrt)) − log(z/t) + O(qrt/N)` and expand
`(L_t − 1)(L_r − 1) + 1`; the leading `q`-dependence is `⌊N/(qrt)⌋ ≈ N/(qrt)` and
`Σ_{q ≤ Q}1/q = log Q + O(1)`.  Then
* expand the coprimality indicator `[r ⟂ t]` by Möbius inversion over common divisors (or use
  `Work.LinnikAreas.Density4.mobius_kappa_sum` / `mobius_kappa_log_sum` after checking `#print axioms`);
* the `t`-sum is evaluated by the PROVED, sorry-free, axiom-clean sharp Mertens input
  `Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one`:
  `Σ_{t ≤ T} μ(t)(log(T/t) − 1)/t = 1 + O((log T)^{-2})`; this produces the normalisation `N·log(N/z)`;
* further inputs: `s3c ≥ 0`, `s3c ≤ 1` (`Work.LinnikAreas.Density4.BzS3.s3c_nonneg`, `s3c_le_one`)
  and the elementary `⌊x⌋ = x + O(1)` replacement.  A large absolute constant `C` is fine. -/
theorem s3_hard_main_term : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
    |(∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
        ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (if r.Coprime t then
            (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
          ((Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1))
            * (((N / (q * r * t) : ℕ) : ℝ))
            * ((Real.log ((((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ)) - 1)
                * (Real.log ((((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ)) - 1) + 1)))
      - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))| ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Work.LinnikAreas.JutilaPieces.S3RouteAccumB
  obtain ⟨C₂, hC₂, h₂⟩ := Work.LinnikAreas2.S3Hard2.s3cont_model
  refine ⟨C₁ + C₂, by linarith, fun z N hz hzN hNz => ?_⟩
  change |Work.ZeroDensity.Jutila.s3exact z N
      - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))| ≤ (C₁ + C₂) * (N : ℝ)
  have hF := h₁ z N hz hzN hNz
  have hM := h₂ z N hz hzN hNz
  have hsplit : Work.ZeroDensity.Jutila.s3exact z N
        - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))
      = (Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N)
        + (Work.ZeroDensity.Jutila.s3cont z N
            - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))) := by ring
  rw [hsplit]
  calc |(Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N)
          + (Work.ZeroDensity.Jutila.s3cont z N
              - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ)))|
      ≤ |Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N|
        + |Work.ZeroDensity.Jutila.s3cont z N
            - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))| := abs_add_le _ _
    _ ≤ C₁ * (N : ℝ) + C₂ * (N : ℝ) := add_le_add hF hM
    _ = (C₁ + C₂) * (N : ℝ) := by ring

end Work.LinnikAreas2
