/-
# `phiASeriesDefs` — the explicit power-series form of `𝒜φ = VocabO.phiA α`

`phiA α z = α z² φ''(z) + (5+α) z φ'(z)` with `φ(z) = 2z/(1+z)²`, so in terms of
`u = 1/(1+z) = (1+z)^{-1}` it is a polynomial of degree `4` in `u`:

`phiA α z = (2α-10)u + (30-14α)u² + (24α-20)u³ − 12α u⁴`.

Since `(d/dz)^k (1+z)^m = (∏_{i<k}(m-i))·(1+z)^{m-k}`, every `z`-derivative of `phiA α`
is an explicit finite sum — this is what makes the bound `BddDeriv 22 (phiA α) K` cheap.

The two objects below are *definitions only* (no proofs), so that the lemmas about them can
be proved in parallel.
-/
import Mathlib
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Finset

namespace Work.FTS.PhiStar.Series.Deleg

/-- The coefficient of `(1+z)^{-(n+1)}` in the expansion of `𝒜φ = VocabO.phiA α`:
`2α-10`, `30-14α`, `24α-20`, `-12α` for `n = 0,1,2,3`. -/
def phiAcoef (α : ℝ) : ℕ → ℝ
  | 0 => 2 * α - 10
  | 1 => 30 - 14 * α
  | 2 => 24 * α - 20
  | _ => -12 * α

/-- `𝒜φ` written in powers of `u = 1/(1+z)`, together with its formal `k`-th derivative:
`(d/dz)^k (1+z)^m = (∏_{i<k}(m-i))·(1+z)^{m-k}`, so `phiAseries α k` is the closed form of
`iteratedDeriv k (phiA α)` on `z > 0`. -/
def phiAseries (α : ℝ) (k : ℕ) : ℝ → ℝ := fun z =>
  ∑ n ∈ Finset.range 4, phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
    * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))

end Work.FTS.PhiStar.Series.Deleg
