/-
# ZeroFreeTables — HBLemma8_4_proof

`Work.ZeroFreeTables.HBLemma8_4` is Heath-Brown's **Lemma 8.4** (PLMS 64 (1992) 265–338,
p. 46): for a real character `χ₁` with a real exceptional zero `ρ₁` (HB's §6 numbering,
`IsMin1WideAt 10`) and `λ₁ = λ(ρ₁) = (1 - Re ρ₁)·log q`,

* `λ₀ ≥ (2 - ε)·log(λ₁⁻¹)` whenever `λ₁ ≤ 0.2` (`ε > 0`, `q ≥ q₀(ε)`), and
* `λ₀ ≥ max((3/2)·log(λ₁⁻¹), 1.294)` for all (large) `q`,

where `λ₀` is the least `λ` over the zeros of `χ₁` other than `ρ₁` (and other than `conj ρ₁`,
which for real `ρ₁` is `ρ₁` itself) — i.e. `Lam0Bound χ₁ ρ₁ c` for these two `c`.

The proof follows HB's own case analysis of §8, and is assembled in `HB84Assembly.lean`
(`HBLemma8_4_of_pieces`) from four analytic inputs of `HB8Defs.lean`:

| input | HB reference | content |
|---|---|---|
| `HBLemma8_1` | Lemma 8.1 (p. 37) | the §6 triangle method: `λ₀ ≥ (2-ε)log(λ₁⁻¹)` for `λ₀ ≥ 4e` |
| `HBTable2and3` | Tables 2, 3 (p. 38) | the §7 optimal test function (`k = 2/3`): the range `λ₀ < 4e`, and the ε-free `λ₀ ≥ (3/2)log(λ₁⁻¹)` for `λ₁ ≤ 0.4` |
| `HBTable4range` | Table 4 (p. 43) | the `P₃` method of Lemma 8.3 / the `µ⁰ = 0` case of Lemma 6.4: `λ₀ ≥ max((3/2)log(λ₁⁻¹), 1.294)` for `0.4 ≤ λ₁ ≤ 1.294` |
| `HBRepZero84` | §6, repeated zero | a *multiple* exceptional zero forces `λ₁ ≥ 1.294` |

With `λ₁ ≥ 1.294` the two bounds are immediate from the minimality of `λ₁` (`IsMin1`), and
the multiplicity clause of `Lam0Bound` is vacuous by `HBRepZero84` in both conjuncts.

## A note on HB's constants (recorded for the team)

HB's §6/§8 constants use `φ(χ₁) = 1/4` (his Lemma 2.5: *"`φ(χ) = 1/4` if `q` is cube-free, or
if the order of `χ` is at most `L`"*, p. 8 — a real character has order `2 ≤ L`), hence the
§6 inequality (6.18) has the coefficient `f(0)(1/4 + ε)`.  For a general `φ` the triangle
method of §8.1 with support `x₀ = λ₀⁻¹ + 2(2c + 4ε)` (where `c = φ/2`) gives
`λ₁ ≥ (λ₀/(4x₀))e^{-x₀λ₀}`, i.e. the repulsion constant `1/(2φ)` — `2` for `φ = 1/4` (HB) and
only `3/2` for `φ = 1/3`, which is the value of the workspace's `l52HypRealFixed`.
`HB8Defs.L52HypQuarterReal` is the missing `φ = 1/4` input; it is reachable here because
Burgess' `k`-th character-sum bound is available for every `k` (`cubefree_charSum_all_k`) and
the cubeful-moduli correction factor `√(orderOf χ) ≤ √2` for `χ² = 1`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB84Assembly
import Submission.Work.ZeroFreeTables.HBLemma8_1_witness
import Submission.Work.ZeroFreeTables.HBTable2and3_all
import Submission.Work.ZeroFreeTables.HBTable4range_engine
import Submission.Work.ZeroFreeTables.HBRepZero84_proof

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

theorem HBLemma8_4_proof : Work.ZeroFreeTables.HBLemma8_4 :=
  HBLemma8_4_of_pieces HBLemma8_1_witness HBTable2and3_all HBTable4range_engine HBRepZero84_proof

end Work.ZeroFreeTables
