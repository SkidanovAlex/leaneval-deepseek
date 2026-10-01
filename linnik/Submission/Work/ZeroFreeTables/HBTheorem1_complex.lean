/-
# ZeroFreeTables — HBTheorem1_complex

**HB Lemma 9.5** (D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions,
and the least prime in an arithmetic progression*, PLMS (3) **64** (1992), 265–338,
p. 59), in the *contrapositive* form needed by HB Theorem 1:

> Suppose that either `χ₁` or `ρ₁` is complex, or both, and let `χ₁` have order `h`.
> Then for `q` sufficiently large, `λ₁ ≥ 0.518 (h=2), ≥ 0.389 (h=3), ≥ 0.348 (h=4),
> ≥ 0.397 (h=5), ≥ 0.364 (h≥6)`.

Taking the weakest of these values, every complex case has `λ₁ ≥ 0.348`, i.e.

  `IsMin1WideAt 10 χ₁ ρ₁ → (χ₁^2 ≠ 1 ∨ ρ₁.im ≠ 0) → 348/1000 ≤ lamOf q ρ₁`.

This is the *realness* half of HB Theorem 1: combined with `HBTheorem1_second`
(simplicity and uniqueness in the real case) it gives `HBProps.HBTheorem1`
(`HBTheorem1_proof.lean`), and hence clause `(Z1)` of the contract.

## The proof, and the case split

`IsMin1WideAt 10 χ₁ ρ₁` entails `IsMin1 χ₁ ρ₁`, hence `IsZ χ₁ ρ₁`, hence `χ₁ ≠ 1`.
So for `χ₁² ≠ 1` the order `h = orderOf χ₁` of `χ₁` satisfies `h ≥ 3`
(`h ≠ 1` since `χ₁ ≠ 1`, `h ≠ 2` since `h = 2` would give `χ₁² = 1`).  The two
disjuncts of the hypothesis are therefore covered by

* `χ₁² = 1`, `ρ₁.im ≠ 0`: `h = 2` — HB's `P₃`/Chebyshev engine with `a = 3.4`,
  available as the *sharp* `Work.ZeroFreeTables.XY.Lam1Lower` (`λ₁ ≥ 0.518`, proved by the
  fleet in `XY/`), weakened to `0.348`;
* `χ₁² ≠ 1`: `h ≥ 3`, split further into `h = 3` (`a = 2.6`),
  `h = 4` (`a = 2.3`, the binding case) and `h ≥ 5` (the `§7` optimal test
  functions of HB Lemma 7.1/7.5) — `HBTheorem1_complex_h3`, `_h4`, `_h5plus`.

The assembly is the case split on `orderOf χ₁` (`3 ≤ orderOf χ₁`, then
`= 3`, `= 4` or `≥ 5`).

**Status of the four cases** (the three `∃ q₀` statements are combined by `max`):

* `h = 2`: `Work.ZeroFreeTables.XY.Lam1Lower` — *proved* by the fleet's `XY/` chapter
  (the `P₃`/Chebyshev engine of HB §9 with `a = 17/5`, `φ = 1/4`), giving the sharp
  `λ₁ ≥ 518/1000`, weakened here to `348/1000`;
* `h = 4`: `Work.ZeroFreeTables.HBTheorem1_complex_h4` — *proved* (the binding case,
  root `0.348384…`);
* `h ≥ 5`: `Work.ZeroFreeTables.HBTheorem1_complex_h5plus` — *proved* (HB's §9
  `F`-method for `h ≥ 5` with the second-minimum input of HB Lemma 6.2);
* `h = 3`: `Work.ZeroFreeTables.HBTheorem1_complex_h3` — *proved*; it consumes the
  analytic engine `Work.ZeroFreeTables.HB95_h3_engine` (HB (9.16) with the `P₃`
  polynomial, `a = 2.6`, `N₃ = 40630`, `φ/2 = 1/8`, proved from
  `HB95SigmaEngine`/`HB95PrincipalEngine`/`HB95NearZeros`) together with the numerical
  step `Work.ZeroFreeTables.h3_arith` ((★) `⟹ λ₁ ≥ 348/1000`).  The companion
  `T₃`-drop (`Re T₃ ≤ 0` under (9.17)) and the end-to-end form
  (with-`T₃` inequality `⟹ λ₁ ≥ 348/1000`) are the proved
  `Work.ZeroFreeTables.T3re_nonpos` / `h3_reduce` of `HB95Arith.lean`.

## The numerical content

The order `2, 3, 4` cases reduce to the single inequality (HB p. 59, from (9.16)
with the polynomial `P₃` of (8.4) and the side condition (9.17))

  `0 ≤ 14379·P₃((a+λ₁)/a) − 24480·P₃(1) + N_h·(a+λ₁)·(1/8 + ε)`,

whose roots at `ε = 0` are `0.518683 (h=2)`, `0.389034 (h=3)`, `0.348384 (h=4)` —
matching HB's stated thresholds.  The purely numerical step (that inequality
forces `λ₁ ≥ 348/1000`) is proved in `ZeroFreeTables.HB95Arith`
(`h2_arith`, `h3_arith`, `h4_arith`), which the prover of the `h3`/`h4` cases can
use directly.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.XY.Lam1Lower
import Submission.Work.ZeroFreeTables.HBTheorem1_complex_h3
import Submission.Work.ZeroFreeTables.HBTheorem1_complex_h4
import Submission.Work.ZeroFreeTables.HBTheorem1_complex_h5plus

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **HB Lemma 9.5, contrapositive form.**  For `q` sufficiently large, a pair
`(χ₁, ρ₁)` over which `λ₁ = lamOf q ρ₁` is minimal (over the non-principal zeros of
height `≤ 10`) which is *not* a real pair (`χ₁² ≠ 1` or `ρ₁.im ≠ 0`) satisfies
`λ₁ ≥ 348/1000`. -/
theorem HBTheorem1_complex : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → (χ₁ ^ 2 ≠ 1 ∨ ρ₁.im ≠ 0) → (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨q₁, H₁⟩ := Work.ZeroFreeTables.XY.Lam1Lower
  obtain ⟨q₂, H₂⟩ := HBTheorem1_complex_h3
  obtain ⟨q₃, H₃⟩ := HBTheorem1_complex_h4
  obtain ⟨q₄, H₄⟩ := HBTheorem1_complex_h5plus
  refine ⟨q₁ + q₂ + q₃ + q₄, ?_⟩
  intro q hq hNq χ₁ ρ₁ hm hcase
  haveI : NeZero q := hNq
  have hq₁ : q₁ ≤ q := by omega
  have hq₂ : q₂ ≤ q := by omega
  have hq₃ : q₃ ≤ q := by omega
  have hq₄ : q₄ ≤ q := by omega
  -- `IsMin1WideAt 10` gives `IsZ`, hence `χ₁ ≠ 1`
  have hZ : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  have hχ1 : χ₁ ≠ 1 := hZ.1
  -- a character which is neither `1` nor of order `2` has order at least `3`
  have h3le_of : χ₁ ^ 2 ≠ 1 → 3 ≤ orderOf χ₁ := by
    intro hchi
    have hpos : 0 < orderOf χ₁ := orderOf_pos χ₁
    have hne1 : orderOf χ₁ ≠ 1 := fun hh => hχ1 (orderOf_eq_one_iff.mp hh)
    have hne2 : orderOf χ₁ ≠ 2 := by
      intro h2
      exact hchi (by rw [← h2]; exact pow_orderOf_eq_one χ₁)
    omega
  -- the three cases of HB's order `h ≥ 3` analysis, with the thresholds of HB Lemma 9.5
  have key : 3 ≤ orderOf χ₁ → (348 : ℝ) / 1000 ≤ lamOf q ρ₁ := by
    intro h3le
    by_cases h5 : 5 ≤ orderOf χ₁
    · exact H₄ q hq₄ χ₁ ρ₁ hm h5
    · have h34 : orderOf χ₁ = 3 ∨ orderOf χ₁ = 4 := by omega
      rcases h34 with h33 | h44
      · exact H₂ q hq₂ χ₁ ρ₁ hm h33
      · exact H₃ q hq₃ χ₁ ρ₁ hm h44
  rcases hcase with hne | him
  · exact key (h3le_of hne)
  · by_cases hchi : χ₁ ^ 2 = 1
    · -- the `h = 2` case: `XY.Lam1Lower` gives the sharp `λ₁ ≥ 0.518`
      have h518 : (518 : ℝ) / 1000 ≤ lamOf q ρ₁ := H₁ q hq₁ χ₁ ρ₁ hm hchi him
      linarith
    · exact key (h3le_of hchi)

end Work.ZeroFreeTables
