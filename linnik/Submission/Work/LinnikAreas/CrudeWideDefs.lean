import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

/-!
# Definitions for the *single-input* far-zero bound (crude, wide range)

This module holds the one new definition of the file
`Submission/Work/LinnikAreas/FarBoundOfJutilaCrudeWide.lean`: the **two-branch cell bound**
`cellBoundJMcw`, which replaces the three-branch `cellBoundJMsh` by using the *wide-range crude
log-free* estimate `FamilyZeroDensityJutilaCrudeWide`
(`Σ_{χ ≠ 1} N(σ,T,χ) ≤ C·(qT)^{(24/5+ε)(1-σ)}` on `σ ≥ 1 - 1021/5000`) on the **whole** low-`λ`
region `(m+1) ≤ (1021/5000)·L`, and the σ-blind count above it.

Since `24/5 + 1/1000 = 4.801 < 49/10 = 4.9`, the `m`-sums still converge geometrically, and since
`(24/5 + 1/1000)·(1021/5000) = 0.98036… ≤ 11/10`, the dyadic `k`-sum `CellLayerKsum` applies with
its `R^{-9/10}` decay.  See `Submission/Work/LinnikAreas/NOTE_area2_principal_character.md` §7/§9.
-/

namespace Work.LinnikAreas

noncomputable section

/-- **The two-branch cell bound.**  `cellBoundJMcw q CJ c0 L m k` bounds the multiplicity sum
over the cell `λ ∈ [m,m+1)`, `|Im ρ|·L ≤ 2^k`:

* `(m+1) ≤ (1021/5000)·L` (i.e. `σ = 1 - (m+1)/L ≥ 1 - 1021/5000 = 0.7958`): the wide-range
  crude log-free non-principal family estimate, exponent coefficient `24/5 + 1/1000 = 4.801`;
* `(m+1) > (1021/5000)·L`: the σ-blind uniform ball count at the *scaled* height `2^k/L`
  (legitimate because the zeros of the cell satisfy `|Im ρ|·L ≤ 2^k`).

The middle branch `(L/5, (1021/5000)L]` of `cellBoundJMsh` has disappeared: it is covered by the
first branch, which is why a *single* input suffices. -/
def cellBoundJMcw (q : ℕ) (CJ c0 L : ℝ) (m k : ℕ) : ℝ :=
  if ((m:ℝ) + 1) ≤ (1021/5000)*L then
    CJ * ((q:ℝ) * (2:ℝ)^k) ^ (((24:ℝ)/5 + 1/1000) * (((m:ℝ) + 1)/L))
  else
    (q:ℝ) * c0 * (4 + (2:ℝ)^k / L) * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2)

end

end Work.LinnikAreas
