/-
# Deuring–Heilbronn repulsion for other characters — shared vocabulary

This file fixes the notions used by the proof of `Work.LinnikAreas.dhRepelOtherChar`.

Setting: `q` is a modulus, `χ₀` a real character of level `q` with the *exceptional* zero `ρ₀`
(real, of minimal `λ = lamOf q ρ = (1 - Re ρ) log q` over all zeros of non-principal characters
of level `q` in the working region `|Im ρ| ≤ 1`), and we want to repel every zero `ρ` of every
*other* character (`χ ≠ χ₀`, `χ ≠ 1`).

The proof goes through the "second minimal zero" `(χ₂,ρ₂)`: among all zeros of *other* characters
(and of the principal character) `λ(ρ₂)` is minimal.  Since the window arguments of Heath-Brown
§5/§6 need the maximality of `ρ₂` only up to height `|Im ρ₂| + δ`, and since the classical
zero-free region bounds `λ` from below for zeros of large imaginary part, we work with the
minimum over the box `|Im u| ≤ 4` and require the minimiser itself to lie in the smaller box
`|Im u| ≤ 2`.  The existence statement is proved by finiteness of the zero set.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.DhRepel

/-- `(χ₂,ρ₂)` is a zero of an *other* character (i.e. `χ₂ ≠ χ₀`, `χ₂ ≠ 1`) with minimal `λ`
among all zeros of characters `ψ ≠ 1` of level `q` lying in the box `|Im u| ≤ 4`, the pair
`(χ₀,ρ₀)` itself excluded; moreover `|Im ρ₂| ≤ 2`.

The box `|Im u| ≤ 4` is what makes the maximality hypotheses of the window lemmas of
Heath-Brown §6 automatic: every zero that can appear in a window around a point `s` with
`|Im s| ≤ 2` (window radius `δ ≤ 1`) has `|Im| ≤ 3 ≤ 4`. -/
def IsSecondMin (q : ℕ) [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ)
    (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ) : Prop :=
  χ₂ ≠ χ₀ ∧ χ₂ ≠ 1 ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧
  |ρ₂.im| ≤ 2 ∧
  ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
    |u.im| ≤ 4 → (ψ, u) ≠ (χ₀, ρ₀) →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u

/-- Unfolding of `IsSecondMin`. -/
theorem isSecondMin_spec {q : ℕ} [NeZero q] {χ₀ χ₂ : DirichletCharacter ℂ q} {ρ₀ ρ₂ : ℂ} (h : IsSecondMin q χ₀ ρ₀ χ₂ ρ₂) :
    χ₂ ≠ χ₀ ∧ χ₂ ≠ 1 ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ 2 ∧
    ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ 4 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u := h

/-- **Existence of the second-minimal zero.**  If some character `χ ≠ χ₀`, `χ ≠ 1` has a zero
`ρ` with `|Im ρ| ≤ 1` (in particular the hypothesis `χ ≠ χ₀` of the target theorem supplies
one), then there is a pair `(χ₂,ρ₂)` which is `IsSecondMin` and whose `λ` is at most that of
`(χ,ρ)`. -/
theorem exists_isSecondMin (q : ℕ) [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hχ : χ ≠ χ₀) (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) (him : |ρ.im| ≤ 1) :
    ∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ), IsSecondMin q χ₀ ρ₀ χ₂ ρ₂ ∧
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ := by
  sorry

/-- The `λ` of the second-minimal zero bounds the `λ` of any zero of an other character in the
working region: `λ(ρ₂) ≤ λ(ρ)` whenever `χ ≠ χ₀`, `χ ≠ 1`, `zeroMult χ ρ ≠ 0`, `|Im ρ| ≤ 1`,
`(χ,ρ) ≠ (χ₀,ρ₀)`. -/
theorem isSecondMin_le {q : ℕ} [NeZero q] {χ₀ χ₂ : DirichletCharacter ℂ q} {ρ₀ ρ₂ : ℂ} (h : IsSecondMin q χ₀ ρ₀ χ₂ ρ₂) {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hχ : χ ≠ χ₀) (hχ1 : χ ≠ 1) (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0)
    (him : |ρ.im| ≤ 1) :
    Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ := by
  sorry

end Work.LinnikAreas.DhRepel
