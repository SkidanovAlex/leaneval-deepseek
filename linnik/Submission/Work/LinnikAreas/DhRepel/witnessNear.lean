/-
# `Work.LinnikAreas.DhRepel.witnessNear` — the `λ`-minimal zero of a narrow box

The Deuring–Heilbronn §6 triangle inequality `Work.LinnikAreas.DhRepel.dhTrianglePtH` needs a test
zero `ρ' ≠ ρ₀` of the same `L`-function `L(·,χ₀)` together with a **box height** `Hb` such that

* `|Im ρ'| + 1/2 ≤ Hb` (so that the window `‖1 + i·Im ρ' - u‖ ≤ 1/2` of `ρ'` is contained in the
  box on which the maximality hypothesis is assumed), and
* `ρ'` is `λ`-minimal among the zeros of `χ₀` other than `ρ₀` in the box `|Im| ≤ Hb`,

while `ρ'` itself must satisfy `|Im ρ'| ≤ 10 log q` (the range of the log-derivative input `L52Hyp`
and of the principal-character Lemma 5.3) and `λ(ρ') ≤ λ(ρ)` (so that the conclusion of §6 is at
least as strong as required for the given zero `ρ`).

The natural candidate is the `λ`-minimiser over a box `|Im| ≤ K`: it is automatically minimal over
every *sub*-box, so it is a witness as soon as its own height is at most `K - 1/2`.  This file
isolates exactly that existence statement.

Route (the candidate `u*` of smallest `λ` over a slightly larger box):  let `u*` be a zero of `χ₀`
other than `ρ₀` with `|Im u*| ≤ 10 log q + 1/2` which minimises `λ` among all zeros of `χ₀` other
than `ρ₀` with `|Im| ≤ 10 log q + 1/2`, and such that `λ(u*) ≤ λ(ρ)`.  Then `u*` is `λ`-minimal over
the box `|Im| ≤ |Im u*| + 1/2` (which is contained in the box of definition), so `(u*, Hb)` with
`Hb := |Im u*| + 1/2` is a witness **provided** `|Im u*| ≤ 10 log q`.

Consequently the only case left open is the one in which every zero of `χ₀` other than `ρ₀` of
minimal `λ` in the boxes `|Im| ≤ 10 log q + k/2`, `k ≥ 0`, lies at height `> 10 log q`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.boxMaxZeroH

open DirichletCharacter Complex
open scoped Classical

namespace Work.LinnikAreas.DhRepel

/-- **A `λ`-minimal test zero with a box containing its window.**  For every sufficiently large
modulus `q`, every real character `χ₀` of level `q` with a minimal real zero `ρ₀` (`IsMin1`,
`ρ₀.im = 0`, `λ(ρ₀) ≤ 1/100`) and every other zero `ρ` of `χ₀` with `|Im ρ| ≤ 1` and
`λ(ρ) ≤ (1/3)·log log log q`, there is a zero `ρ' ≠ ρ₀` of `χ₀` and a height `Hb` with

* `|Im ρ'| ≤ 10 log q` and `|Im ρ'| + 1/2 ≤ Hb`,
* `λ(ρ') ≤ λ(ρ)`,
* `ρ'` is `λ`-minimal among the zeros of `χ₀` other than `ρ₀` with `|Im| ≤ Hb`. -/
theorem witnessNear : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      Work.LinnikContract.lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
    ∃ (ρ' : ℂ) (Hb : ℝ), Work.LinnikContract.zeroMult χ₀ ρ' ≠ 0 ∧ ρ' ≠ ρ₀ ∧
      |ρ'.im| ≤ 10 * Real.log (q : ℝ) ∧ |ρ'.im| + 1 / 2 ≤ Hb ∧
      Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q ρ ∧
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ Hb →
        u = ρ₀ ∨ Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q u) := by
  sorry

end Work.LinnikAreas.DhRepel
