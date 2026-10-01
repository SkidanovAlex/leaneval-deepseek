/-
# ZeroFreeTables — HBTheorem1_proof

**HB Theorem 1** (D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the
least prime in an arithmetic progression*, PLMS (3) **64** (1992), 265–338, p. 3), in the form
in which AREA 3 consumes it, i.e. clause `Z1` of `Work.ZeroFreeTables.Z1`:

> If `q` is sufficiently large the function `∏_{χ mod q} L(s,χ)` has at most one zero in the
> region `σ ≥ 1 − 0.348 / log q`, `|t| ≤ 1`.  Such a zero, if it exists, is real and simple,
> and corresponds to a non-principal real character.

Formalised as `HBTheorem1 = ∃ q₀, ∀ q ≥ q₀, ∀ [NeZero q] (χ₁) (ρ₁),
IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁` with `λ₁ = lamOf q ρ₁` the minimum of `λ(ρ) = (1 − Re ρ) log q`
over the non-principal zeros of height `≤ 10` (HB's §6 numbering, `IsMin1WideAt 10`).

## The proof

The clause `Z1 χ₁ ρ₁` is `λ₁ < 0.348 → χ₁² = 1 ∧ ρ₁.im = 0 ∧ (ρ₁ simple) ∧ (no other zero with
λ < 0.348)`, and it splits into two independent halves, each a separate theorem of this area:

* **`HBTheorem1_complex`** (HB Lemma 9.5, p. 59) — the *realness* half: if `χ₁` or `ρ₁` is
  complex, then `λ₁ ≥ 0.348`; hence `λ₁ < 0.348` forces `χ₁² = 1` and `ρ₁.im = 0`.  HB's proof
  runs the `P₃`/Chebyshev engine of §9 (the pointwise non-negative trigonometric polynomials
  (9.15)–(9.16) and the `P₃` functional of (8.4), with the near/far split and HB Lemma 3.1) for
  characters of order `h = 2, 3, 4` and the optimal test functions of Lemma 7.1 for `h ≥ 5`,
  giving `λ₁ ≥ 0.518, 0.389, 0.348, 0.397, 0.364` respectively — the worst case is `h = 4`, which
  is where the constant `0.348` comes from.

* **`HBTheorem1_second`** — the *simplicity + uniqueness* half, for the (now known to be) real
  pair: the repeated-zero case `λ₀ ≥ 1.724` (`HBRepZero`) makes `ρ₁` simple, Table 4
  (`λ₀ ≥ 1.724` for `λ₁ ≤ 0.7`) rules out further zeros of `χ₁`, and Table 7 / Lemma 9.4
  (`λ₂ ≥ 0.702`) rules out zeros of any `χ ≠ χ₁^{±1} = χ₁`.

Both halves are `∃ q₀` statements; the conclusion takes `q₀ = max` of the two thresholds, and the
case distinction on `χ₁² = 1`/`ρ₁.im = 0` is the only glue needed: the two branches in which the
pair is complex contradict `λ₁ < 0.348` by `HBTheorem1_complex`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.HBTheorem1_complex
import Submission.Work.ZeroFreeTables.HBTheorem1_second

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

theorem HBTheorem1_proof : Work.ZeroFreeTables.HBTheorem1 := by
  obtain ⟨q₁, h₁⟩ := HBTheorem1_complex
  obtain ⟨q₂, h₂⟩ := HBTheorem1_second
  refine ⟨max q₁ q₂, ?_⟩
  intro q hq
  have hq₁ : q₁ ≤ q := le_trans (le_max_left q₁ q₂) hq
  have hq₂ : q₂ ≤ q := le_trans (le_max_right q₁ q₂) hq
  refine fun [inst : NeZero q] χ₁ ρ₁ hm hlt => ?_
  -- the two literals `0.348` (of `Z1`) and `(348 : ℝ)/1000` (of the two halves)
  have h348 : (0.348 : ℝ) = (348 : ℝ) / 1000 := by norm_num
  have hlt' : lamOf q ρ₁ < (348 : ℝ) / 1000 := by rw [h348] at hlt; exact hlt
  by_cases hchi : χ₁ ^ 2 = 1
  · by_cases him : ρ₁.im = 0
    · -- the pair is real: `HBTheorem1_second` gives simplicity and uniqueness
      obtain ⟨hone, huniq⟩ := h₂ q hq₂ χ₁ ρ₁ hm hchi him hlt'
      refine ⟨hchi, him, hone, fun χ ρ hZ hne => ?_⟩
      have h := huniq χ ρ hZ hne
      linarith
    · -- `χ₁` real, `ρ₁` complex: `HBTheorem1_complex` contradicts `λ₁ < 0.348`
      exact absurd (h₁ q hq₁ χ₁ ρ₁ hm (Or.inr him)) (by linarith)
  · -- `χ₁` complex: `HBTheorem1_complex` contradicts `λ₁ < 0.348`
    exact absurd (h₁ q hq₁ χ₁ ρ₁ hm (Or.inl hchi)) (by linarith)

end Work.ZeroFreeTables
