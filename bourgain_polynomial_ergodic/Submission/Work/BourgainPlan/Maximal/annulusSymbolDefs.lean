import Mathlib

/-!
# Condition (c) of `WINDOW_WEAK_TYPE_STATUS_S10.md` §8.2: annulus symbol smoothness

Piece (i) of MST's `(eq:51)` at `p ≠ 2` is the vector-valued kernel estimate for the *localised*
family `Σ_n |U_n S_{j+n} f|²`.  The two failed drafts of that estimate (§7, §7.1 and §8.1 of the
status note) show that the finiteness cannot come from properties of a single kernel — the fine
dyadic scales saturate — and that it must instead come from the `S_{j+n}` localisation, i.e. from
the frequency support of the symbols, exactly as the bounded-overlap half of `anisoAnnulus_facts`
supplies it.  The ingredient both drafts were missing in different ways is that the smoothness must
sit on the *symbols* and not on the inverse transform of an arbitrary symbol (§8.2).

`AnnulusSymbolSmooth b` is that condition, in the corpus's one-frequency-variable notation
(`ξ ∈ ℝ`, cf. `polyProfile_eq_polyModel`): the family `b` is supported in the dyadic annuli at level
`m` — `2⁻¹ < |2^m ξ| < 2`, the same annuli as `anisoAnnulusDefs` in one dimension — and its `k`-th
derivatives obey the *scale* bound `‖(d/dξ)^k b_m(ξ)‖ ≤ C_k · 2^{m k}`, which is what a symbol
localised at frequency scale `2^{-m}` does.  This is precisely the smooth-cutoff behaviour that
`WINDOW_WEAK_TYPE_STATUS_S7.md` insists the `ℓ^p` assembly must use (and that the sharp Farey
indicator fails), one fact rather than two.

The canonical instance — a fixed Schwartz bump dilated to each annulus — is the delegated lemma
`annulusSymbolSmooth_of_dilate`.

**Why the `ContDiff` conjunct is there (found by the gate, and it matters).**  A pure derivative
*bound* is not a smoothness hypothesis: Mathlib's `iteratedDeriv` is `0` wherever the function is not
differentiable, so the *indicator* of the annulus `1_{2⁻¹ < |2^m ξ| < 2}` satisfies the bounds
vacuously while its inverse Fourier transform decays only like `1/z` — at every fine scale — so the
scale sum `(Σ_n |K_{j+n}(z−y) − K_{j+n}(z)|²)^{1/2}` diverges (numerically `≈ 0.06·M` for the
partial sum over `m ∈ [−M, M]`).  That is the same failure as §8.1, in a different guise.  `b m` being `C^∞` is what lets integration by parts move
derivatives onto the exponential and produce the `2^m/|z|²` decay that makes the scale sum converge.
That smoothness is therefore carried as an **explicit hypothesis of the estimate**
(`annulusLocalizedKernelHormander`) rather than by this predicate, so that the predicate keeps the
already-proved canonical instance (`annulusSymbolSmooth_of_dilate`) — a bounded-derivative bump
satisfies `AnnulusSymbolSmooth`, and adding `ContDiff ℂ` to the predicate would not have helped
there either.
-/

open scoped BigOperators

namespace Work.BourgainPlan.Maximal

/-- **Condition (c)**: an annulus-supported symbol family whose `k`-th derivatives are bounded by
`C_k · 2^{m k}` (frequency scale `2^{-m}`). -/
def AnnulusSymbolSmooth (b : ℤ → ℝ → ℂ) : Prop :=
  (∀ m ξ, b m ξ ≠ 0 → (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| < 2) ∧
    (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ m ξ, ‖iteratedDeriv k (b m) ξ‖ ≤ C * (2 : ℝ) ^ (m * k))

end Work.BourgainPlan.Maximal
