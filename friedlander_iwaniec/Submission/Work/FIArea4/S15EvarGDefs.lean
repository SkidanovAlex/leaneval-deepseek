import Mathlib
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.p14_uncond
import Submission.Work.FIArea4.S15prim_defs

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# FI §15: reduction of the signed-box variance `EvarG` to the positive-box variance `Evar`

`EvarG R m u = Σ_a |Σ_{z ∈ cls_a} u z · (Re z | oddPart m)|²` is the variance of the *signed* box
`gBox R` with the Jacobi weight built in.  Writing `v = u · jwG m` it is the (unweighted) signed-box
variance `S15red.EvG R m v`, and `S15red.EvG_le_Evar` splits `EvG` into four copies of the
positive-box variance `Work.FIPlan.Evar` on the four quadrants.

This module packages the *array* of that reduction: `quadArrE R u σ` (`r,s ≥ 1`,
`z = (σ₁ r, σ₂ s)`), which is *independent of `m`* — the point being that the `m`-dependent Jacobi
factor is exactly `Evar`'s built-in weight up to a unimodular constant, which does not change
`Evar`.  It also fixes the dyadic bracket sum `dyadicSum`.
-/



/-- `EvarG` is nonnegative (a sum of `Complex.normSq`). -/
lemma EvarG_nonneg (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) : 0 ≤ EvarG R m u := by
  unfold EvarG
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

/-- The quadrant array of `u` for the sign combination `σ`: the values `u ⟨σ₁ r, σ₂ s⟩` on the
positive box `1 ≤ r, s ≤ R` (and `0` outside).  This is the array to which `Work.FIPlan.Evar`
is applied for the quadrant `Re = σ₁ r`, `Im = σ₂ s`. -/
def quadArrE (R : ℕ) (u : GaussianInt → ℂ) (σ₁ σ₂ : ℤ) : ℕ → ℕ → ℂ :=
  fun r s =>
    if (r : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ) ∧ (s : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)
      then u ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ else 0

/-- The dyadic sum of the Proposition 14.1 brackets over the moduli `2 ^ k ≤ 4 M` (the factor `4`
being the modulus normalisation `m = 4 (d/e)` of the §15 stratification). -/
def dyadicSum (M R S : ℕ) (ε : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Nat.log 2 (4 * M) + 1), p14Bracket (2 ^ k) R S ε

/-- The `(d/e)`-range of the §15 stratum `e`: `⌈N/(X 2^j)⌉ + 1` divided by `e`, i.e.
`S15Y Pa X j / e`. -/
def stratumY (Pa : Work.FITop.Params) (X j e : ℕ) : ℕ := S15Y Pa X j / e

end

end Work.FIArea4
