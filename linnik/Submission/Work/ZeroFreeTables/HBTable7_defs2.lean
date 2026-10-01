/-
# ZeroFreeTables — HBTable7_defs2

The counting function used by the *second-number reconstruction* needed for HB's Table 7 (see
`STATUS_HBTable7_secondNumber.md`), and (in this docstring) the design of that reconstruction.

## The counting function

`otherLamCount χ₁ Λ H` is the multiplicity-weighted number of zeros `ρ` of the characters
`χ ∉ {1, χ₁, χ₁⁻¹}` with `λ(ρ) = (1 - Re ρ) log q ≤ Λ` and `|Im ρ| ≤ H`.

## The analytic input to be consumed

For `Λ` bounded and `H ≤ 10 log q`, the count is bounded by an *absolute constant*; this is
HB's §6 numbering input (his Lemma 6.1, hence Jutila's log-free family zero-density estimate:
`Σ_{χ ≠ 1} N(1-Λ/log q, H, χ) ≤ C (qH)^{(2+ε)Λ/log q} ≤ C e^{(2+ε)Λ} (10 log q)^{(2+ε)Λ/log q}
≤ C'`).  In this workspace that node is `Work.LinnikAreas.FamilyZeroDensityJutila`; the reduction
`Work.LinnikAreas.DhRepel.nearLineCountFromNode` performs the analogous computation for a *single*
character.  The lemma `Work.ZeroFreeTables.second_pair_wide` takes the input in the abstract form

> `hcount : ∃ C > 0, ∃ Q, ∀ q ≥ Q, ∀ χ₁ Λ H, Λ ≤ 3 → H ≤ 10 log q → otherLamCount χ₁ Λ H ≤ C`

so that it is usable both from the Jutila node and from the Deuring–Heilbronn variant
(`ZeroDensity.DHLogFreeSpec`).

## The design of `second_pair_wide` (for the prover)

Goal: given `χ₁` real with `IsMin1WideAt 10 χ₁ ρ₁` and a zero `ρ` of `χ ∉ {χ₁^{±1}}` with
`|ρ.im| ≤ 1` and `λ(ρ) < Λ`, produce a *second pair* `(χ₂,ρ₂)` with

* `χ₂ ∉ {1, χ₁, χ₁⁻¹}`, `zeroMult χ₂ ρ₂ ≠ 0`,
* `λ(ρ₂) ≤ λ(ρ)`,
* `2|ρ₂.im| + 1 ≤ 10 log q` (the height condition of the engine `lemma8_7_region`),
* `λ(ρ₂)` minimal over the strip `|u.im| ≤ 2|ρ₂.im| + 1` (i.e. over `|γ₂| + 1` and
  `2|γ₂| + 1`, the two window heights of the engine's four non-principal characters).

Iteration (Heath-Brown's §6 "second maximum", run in reverse): for `H : ℝ`, let `V(H)` be the set
of pairs `(ψ,u)` with `ψ ≠ 1, ψ ≠ χ₁, ψ ≠ χ₁⁻¹`, `zeroMult ψ u ≠ 0`, `|u.im| ≤ H`,
`λ(u) ≤ λ(ρ)`; it is non-empty once `H ≥ 1` (it contains `(χ,ρ)`), and it is finite for each `H`
by `Work.ZeroFreeTables.exists_min_other_wide` (which produces, for every `H`, a `V(H)`-minimiser
with `|u.im| ≤ H`).

* Start with `H₀ := 1` and a `V(H₀)`-minimiser `(χ⁰,ρ⁰)` (whose `|Im|` is `≤ 1`).
* If `2|ρ^k.im| + 1 ≤ H_k` then `(χᵏ,ρᵏ)` is good: `λ(ρᵏ) = min_{V(H_k)} λ ≤ min_{V(2|ρᵏ.im|+1)} λ`
  because `V(2|ρᵏ.im|+1) ⊆ V(H_k)`, while `(χᵏ,ρᵏ) ∈ V(2|ρᵏ.im|+1)`.
* Otherwise set `H_{k+1} := 2|ρᵏ.im| + 1 > H_k` and take a `V(H_{k+1})`-minimiser.  In the failure
  case the minimisers have **strictly increasing** `|Im|` (`|ρ^{k+1}.im| > |ρᵏ.im|`, otherwise
  `λ(ρ^{k+1}) ≤ λ(ρᵏ)` would put `(χᵏ,ρᵏ)` in `V(H_{k+1})` with the minimal value, contradicting
  failure at level `k+1`), so the `K+1` pairs obtained in `K+1` failing steps are **distinct** and
  all lie in the strip `|Im| ≤ H_K`, where `H_{k+1} = 2|ρᵏ.im| + 1 ≤ 2H_k + 1` gives
  `H_K ≤ 2^K(H₀+1) - 1`.

Hence, if the count bound is `otherLamCount χ₁ Λ H ≤ C` for all `H ≤ 10 log q`, the iteration
cannot fail more than `⌈C⌉` times, so some step `k ≤ ⌈C⌉` produces a good pair; its height is
`≤ 2^{⌈C⌉+1}`.  The threshold `Q` of the conclusion is therefore chosen from `C` and `Q` of
`hcount` so large that `2·(2^{⌈C⌉+1}) + 1 ≤ 10 log q` for `q ≥ Q` (this is why the `Q` of the
conclusion may, and must, depend on the `C` delivered by `hcount`: the height of the good pair is
bounded by an exponential in `C`, so no fixed threshold works for all `C`).

Note that the heights can grow *linearly* (e.g. `H_k ≈ k` when the minimisers sit near the middle
of their strips) — that is compatible with the argument: the count bound caps the *number* of
steps, and the geometric bound `H_K ≤ 2^{K+1}` caps the height.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- The multiplicity-weighted number of zeros of the characters `χ ≠ 1`, `χ ≠ χ₁`, `χ ≠ χ₁⁻¹`
with `λ(ρ) = (1 - Re ρ) log q ≤ Λ` and `|Im ρ| ≤ H`. -/
def otherLamCount {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ) : ℝ :=
  ∑ᶠ p : DirichletCharacter ℂ q × ℂ,
    if p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
        |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ
      then (Work.LinnikContract.zeroMult p.1 p.2 : ℝ) else 0

end Work.ZeroFreeTables
