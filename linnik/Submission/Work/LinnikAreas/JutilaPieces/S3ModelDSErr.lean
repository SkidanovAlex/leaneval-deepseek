import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

namespace Work.LinnikAreas.JutilaPieces

/-- **Per-`q` error of the continuous model.**  With `s3DSabs` and `RS1`/`RS0`/`wm` from
`S3ModelDefs` (`wm n = μ(n)/κ(n)`), and the Mertens-type input `h : KappaMertensInput`, for every
cut-off `Q : ℝ` and integer `B` with `2 ≤ B ≤ Q`,

  `s3DSabs Q B = ζ(2)·Σ_{t ≤ B}(μ(t)/t)(log(Q/t) − 1) + O((log Q + 2)^4·exp(−c√log B))`.

Route: for squarefree `t` the two conjuncts of `h` (with `R = B`, `Y = Q`) give
`RS1 Q t B = ζ(2)κ(t)/t + log(Q/B)·RS0 t B + δ`, `|δ| ≤ C σ_{-1/2}(t) e^{−c√log B}`,
`|RS0 t B| ≤ C σ_{-1/2}(t) e^{−c√log B}`, `σ_{-1/2}(t) = Σ_{d ∣ t} d^{-1/2}`; for other `t` both
sides of the pointwise identity vanish since `μ(t) = 0`.  Then `wm t·(κ(t)/t) = μ(t)/t`,
`|log(Q/t) − 1| ≤ log Q + 1`, `log(Q/B) ≤ log Q`, `|wm t| = |μ t|/κ(t) ≤ 1/κ(t) ≤ 1/t` for
squarefree `t`, and `Σ_{t≤B}σ_{-1/2}(t)/t ≤ (1 + log(2+B))²`; finally
`(log Q + 1)(1 + log(2+B))² ≤ (log Q + 2)^4` for `2 ≤ B ≤ Q`.  NB:
`Work.ZeroDensity.Jutila.BzSqSigma` does not compile in this snapshot, so
`Σ_{t≤T}σ_{-1/2}(t)/t ≤ (1+log(2+T))²` must be proved locally from `σ_{-1/2}(t) ≤ τ(t)` and
`Σ_{t≤T}τ(t)/t = Σ_{d m ≤ T} 1/(dm) ≤ (Σ_{t≤T}1/t)²`. -/
theorem S3ModelDSErr (h : Work.ZeroDensity.Jutila.KappaMertensInput) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (Q : ℝ) (B : ℕ), 2 ≤ B → (B : ℝ) ≤ Q →
        |Work.LinnikAreas.JutilaPieces.s3DSabs Q B
            - (Real.pi ^ 2 / 6) * (∑ t ∈ Finset.Icc 1 B,
                (ArithmeticFunction.moebius t : ℝ) / (t : ℝ) *
                  (Real.log (Q / (t : ℝ)) - 1))|
          ≤ K * (Real.log Q + 2) ^ 4 *
              Real.exp (-(c * Real.sqrt (Real.log (B : ℝ)))) := by sorry

end Work.LinnikAreas.JutilaPieces
