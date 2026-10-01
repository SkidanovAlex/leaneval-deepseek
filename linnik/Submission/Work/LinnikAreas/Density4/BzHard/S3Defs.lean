/-
# The `S₃` set-up (An arXiv:2206.10104 §5, `k = ℚ`, `w = y = z`) for the correction term `B_z`

Namespace `Work.LinnikAreas.Density4.BzHard`.

For `2 ≤ z ≤ N < z²` the second moment of the correction term
`B_z(n) = Λ_z(n) − Λ(n) = Σ_{z < d ∣ n} μ(d)·log(d/z)` is re-indexed as a quadruple sum over
`(q,r,t,m)` and evaluated by two Abel summations of the squarefree-coprime count.  This file
collects the numerical objects:

* `kap n = n·∏_{p ∣ n}(1 + 1/p)` (the paper's `κ`);
* `s3C c = ζ(2)^{-1}·∏_{p ∣ c}(1 + 1/p)^{-1}`, the density of squarefree integers coprime to `c`;
* `s3M z N q r t = ⌊N/(qrt)⌋` and `s3Mp z r t = max (⌊z/t⌋) (⌊z/r⌋)`, the two cut-offs;
* `s3G c α β X = Σ_{m ≤ X, (m,c)=1, m squarefree} (log m − α)(log m − β)` and its main term
  `s3MainG`, whose difference is `O(X^{1/2+ε} σ_{-1/3}(c))` uniformly in `α, β`.

Nothing here is proved; the lemmas live in the sibling files.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs

namespace Work.LinnikAreas.Density4.BzHard

open Finset

noncomputable section

/-- `κ(n) = n·∏_{p ∣ n} (1 + 1/p)` (An arXiv:2206.10104, §2). -/
def kap (n : ℕ) : ℝ :=
  (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ))

/-- `ζ(2)` as a real number. -/
def zeta2R : ℝ := (riemannZeta (2 : ℂ)).re

/-- The density of the squarefree integers coprime to `c`:
`C_c = ζ(2)^{-1}·∏_{p ∣ c}(1 + 1/p)^{-1}`. -/
def s3C (c : ℕ) : ℝ :=
  zeta2R⁻¹ * (∏ p ∈ c.primeFactors, (1 + (1 : ℝ) / (p : ℝ)))⁻¹

/-- The cut-off `M = ⌊N/(q·r·t)⌋` of the innermost `m`-sum. -/
def s3M (N q r t : ℕ) : ℕ := N / (q * r * t)

/-- The cut-off `M' = max(⌊z/t⌋, ⌊z/r⌋)` below which the `m`-summands are discarded. -/
def s3Mp (z r t : ℕ) : ℕ := max (z / t) (z / r)

/-- `G(c,α,β,X) = Σ_{m ≤ X, (m,c)=1, m squarefree} (log m − α)·(log m − β)`. -/
def s3G (c : ℕ) (α β : ℝ) (X : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m c ∧ Squarefree m),
    (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)

/-- The main term `C_c·X·((log X − α − 1)(log X − β − 1) + 1)` of `s3G`. -/
def s3MainG (c : ℕ) (α β : ℝ) (X : ℕ) : ℝ :=
  s3C c * (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)

/-- The exact quadruple sum the second moment of `B_z` is re-indexed into, with the `m`-sum in
the `(M'+1, M]` range. -/
def s3Quad (z N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
    ∑ t ∈ Finset.Icc 1 (N / (q * z)),
      (if Nat.Coprime r t then
          (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
        * (s3G (r * t) (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ)))
              (s3M N q r t)
            - s3G (r * t) (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ)))
              (s3Mp z r t))

end

end Work.LinnikAreas.Density4.BzHard
