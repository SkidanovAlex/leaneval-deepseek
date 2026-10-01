/-
# The `λ₀`-weighted ("Deuring–Heilbronn") log-free zero count for the other characters

**Status: this is an *assumption node*, not a provable lemma of this workspace.**  Its truth is
the `T = 1` instance of the `λ₁`-saving log-free family zero-density estimate

  `Σ_χ N(σ,T,χ) ≤ C·λ(ρ₀)·(qT)^{c(1-σ)}`

(Bombieri, *Le grand crible*, Thm. 14; Jutila 1977; Heath-Brown (1992) §1 Principle 3 with the
`λ₁` factor), restricted to the characters `χ ≠ χ₀, 1` and to zeros with `|Im ρ| ≤ 1`.  It is the
same input that the workspace records as irreducible in `SiegelBase.lean`
(`DensityInput` / `PairDensityInput`) and in `area6.lean` §7 ("true but not a provable lemma
here"): every unconditional zero count available in the workspace
(`FamilyZeroCountNonPrincipal`, `PrincipalZeroCount`) is σ-blind and therefore cannot produce the
factor `λ(ρ₀)`.

It is used by `Work.LinnikAreas.otherCharRepelSiegel`, whose proof is otherwise complete and
consists of the explicit reduction described in that file's header: the singleton instance
`s = {(χ, ρ)}`, `t = λ(ρ)` gives `1 ≤ C·λ(ρ₀)·e^{c·λ(ρ)}`, which is the Deuring–Heilbronn
repulsion `λ(ρ) ≥ c′·log(1/λ(ρ₀))` up to the multiplicative/additive constants (the moderate
range `λ(ρ₀) ≥ e^{-2max 1 (log C)}` being covered by `IsMin1`'s minimality alone).
-/
import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.LinnikAreas.OtherCharRepel

theorem otherCharDensityInput : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
      ∀ t : ℝ, 0 < t → t ≤ Real.log q → ∀ s : Finset (DirichletCharacter ℂ q × ℂ),
        (∀ p ∈ s, p.1 ≠ χ₀ ∧ p.1 ≠ 1 ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
          |p.2.im| ≤ 1 ∧ p.2 ≠ ρ₀ ∧ Work.LinnikContract.lamOf q p.2 ≤ t) →
        (∑ p ∈ s, (Work.LinnikContract.zeroMult p.1 p.2 : ℝ))
          ≤ C * Work.LinnikContract.lamOf q ρ₀ * Real.exp (c * t) := by
  sorry

end Work.LinnikAreas.OtherCharRepel
