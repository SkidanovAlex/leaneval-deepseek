import Mathlib
import Submission.Vinogradov.ChallengeDeps
import Submission.Vinogradov.Core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the Ford extraction (`vk_exp_sum_ford`)

Ford, *Vinogradov's integral and bounds for the Riemann zeta function*, Proc. LMS 85 (2002),
565--633, §5.  The target of the surrounding file is Theorem 2 of that paper:

    `S(N,t) = max_{0<u≤1} max_{N<R≤2N} |Σ_{N<n≤R} (n+u)^{-it}| ≤ 9.463 N^{1-1/(133.66 λ²)}`
    for integers `N ≤ t` and `λ = log t / log N`.

The route fixed here is Ford's Lemma 5.1 (the "Vinogradov extraction"), which reduces the partial
sum to *Vinogradov integral* type counts:

* `J r k X` (`LeanEval.NumberTheory.VinogradovMeanValue.J`) — the complete system (degrees `1..k`);
* `Jincom s k h B` — the **incomplete** system on a set `B`, i.e. the power sums agree only for
  `h ≤ j ≤ k`;
* `fordW r s t N M₁ M₂ j` — Ford's `W_j`, the number of integers `|d| < sM₂^j-1` with
  `‖d γ_j‖ < 1/(2rM₁^j)`, where `γ_j ≍ t/N^j` (this is where the *oscillation* of the phase
  `t log n` is converted into a saving).
-/

namespace Work.BMF

/-- Alias for the complete-system count `J` of the Vinogradov mean value theorem
(`LeanEval.NumberTheory.VinogradovMeanValue.J`), so that delegated lemmas can import just this
file. -/
abbrev vJ (s k X : ℕ) : ℝ := LeanEval.NumberTheory.VinogradovMeanValue.J s k X


open Finset

/-- **Ford's incomplete-system count.**  For `B : Finset ℕ` and `h ≤ k`, `Jincom s k h B` is the
number of pairs of `s`-tuples with entries in `B` whose `j`-th power sums agree for every
`h ≤ j ≤ k`.  (The complete system `J s k X` of the Vinogradov mean value theorem is the case
`h = 1`, `B = Finset.Icc 1 X`.) -/
noncomputable def Jincom (s k h : ℕ) (B : Finset ℕ) : ℝ :=
  ((Finset.univ.filter (fun xy : (Fin s → B) × (Fin s → B) =>
      ∀ j : ℕ, h ≤ j → j ≤ k →
        (∑ i, (xy.1 i : ℕ) ^ j) = (∑ i, (xy.2 i : ℕ) ^ j))).card : ℝ)

/-- **Ford's `W_j`** (Lemma 5.1 of the reference): an upper bound for the number of integers `d`
with `|d| < s M₂^j - 1` whose `γ_j`-multiple `d γ_j` lies within `1/(2rM₁^j)` of an integer, where
`γ_j ≍ t/N^j`.  This is Ford's display following (5.6), with `K = sM₂^j-1`, `γ = |γ_j|` and
`δ = 1/(2rM₁^j)`; here `γ_j` is *upper bounded* by `t/(2π j N^j)` and *lower bounded* in the two
regimes, which is what the three middle terms express. -/
noncomputable def fordW (r s t N M₁ M₂ : ℝ) (j : ℕ) : ℝ :=
  min (2 * s * M₂ ^ j)
    (2 * s * M₂ ^ j / (r * M₁ ^ j) + s * t * M₂ ^ j / (Real.pi * j * N ^ j)
      + 4 * Real.pi * j * (2 * N) ^ j / (r * t * M₁ ^ j) + 2)

end Work.BMF

namespace Work.BMF

open Finset

/-! ## The two Vinogradov-integral inputs of the extraction

The Ford extraction consumes two bounds on the counts above:

* the **complete** system bound (`BMF/vkford_stechkin`): Stechkin's theorem
  `J_{s,k}(X) ≤ exp(C min(⌊s/k⌋,k) k² log k) · X^{2s - k(k+1)/2 + (k²/2)(1-1/k)^{⌊s/k⌋}}`
  for `2 ≤ k ≤ s`;
* the **incomplete** system bound (Ford (1.9)): for `B ⊆ [1,P]`,
  `Jincom s k h B ≤ s^{h-1} P^{h(h-1)/2} J_{s,k}(P)` — the "trivial" estimate which relaxes the
  equations of degree `< h`; this is what converts the `Jincom` term of Ford's Lemma 5.1 into a
  *complete* count (together with `vkford_Wproduct` it makes the `M₂`-powers cancel exactly, which
  is the "gives nothing better than replacing `J_{s,g,h}` by `J_{s,g}`" remark of the source).

-/
