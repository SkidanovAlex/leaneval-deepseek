import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.Mono2
import Submission.Pc
import Submission.Minimals
import Submission.Qpos
import Submission.Dual
import Submission.MT

/-!
# Core estimate (FKNP)

`core_estimate` states that for an increasing family `𝓕` with `2 ≤ l 𝓕`, at
`p = CoreK·q_f(𝓕)·log(l 𝓕)` the Bernoulli measure of `𝓕` is at least `3/4`.

It is obtained by combining Talagrand's LP-duality (`talagrand_dual`:
`q_f(𝓕) ≤ q` yields a `2q`-spread probability measure `ν` on the minimal
elements of `𝓕`) with the spread-hitting theorem (`spread_hit`, i.e. FKNP's
"Theorem MT": such a spread `ν` forces `μ_p(𝓕) ≥ 3/4` at `p = MTK·q·log(l 𝓕)`).
-/

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]

/-- The universal constant of Theorem 1.1 (equals `MTK`). -/
noncomputable def CoreK : ℝ := MTK

/-- FKNP core: at `p = CoreK·q·log l`, an increasing family is very likely. -/
theorem core_estimate {X : Type u} [Fintype X] (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕)
    (hl : 2 ≤ l 𝓕) {pstar : I}
    (hpval : (pstar : ℝ) = CoreK * (q_f 𝓕 : ℝ) * Real.log (l 𝓕))
    (hple : (pstar : ℝ) ≤ 1) :
    (3 / 4 : ℝ) ≤ mu pstar 𝓕 := by
  classical
  let q : ℝ := (q_f 𝓕 : ℝ)
  have hq0 : 0 < q := by
    simpa [q] using (q_f_pos (𝓕 := 𝓕) h𝓕 hl)
  rcases talagrand_dual (X := X) h𝓕 hl q hq0 (by simpa [q] using le_rfl) with
    ⟨ν, hν0, hν1, hνFmin, hspread⟩
  have hνF : ∀ S : Set X, ν S ≠ 0 → S ∈ 𝓕 := by
    intro S hS
    exact (hνFmin S hS).1
  have hνℓ : ∀ S : Set X, ν S ≠ 0 → S.ncard ≤ l 𝓕 := by
    intro S hS
    exact ncard_le_l_of_minimal_elem (hνFmin S hS)
  have hspread' : WeightSpread (2 * q) ν := hspread
  have hMT := spread_hit (X := X) 𝓕 h𝓕 hl q hq0 ν hν0 hν1 hνF hνℓ hspread'
    (pstar := pstar) hple (by
      -- pstar = CoreK · q_f · log l ; q = q_f ; CoreK = MTK
      simpa [q, CoreK] using hpval)
  exact hMT

end FET
end Submission
