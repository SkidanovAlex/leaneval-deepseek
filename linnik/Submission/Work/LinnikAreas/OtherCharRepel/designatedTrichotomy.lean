import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.DhRepel.existsDesignated3
import Submission.Work.LinnikAreas.OtherCharRepel.existsDesignatedDecent

namespace Work.LinnikAreas.OtherCharRepel

/-!
# `designatedTrichotomy`

**Existence of a designated second-minimal pair of zeros, with the far bound `1/25`.**

This is `Work.LinnikAreas.OtherCharRepel.existsDesignatedDecent`, which differs only in that it
carries the *extra* hypothesis `ρ ≠ ρ₀`.  We remove that hypothesis by treating `ρ = ρ₀` directly:

`IsMin1 χ₀ ρ₀` says `λ(ρ₀)` is the minimum of `λ` over *all* zeros `(ψ,u)` of non-principal
characters with `|Im u| ≤ 1`.  Since `ρ₀` is real (`ρ₀.im = 0`), the ball
`|Im u| ≤ |ρ₀.im| + 1 = 1` of the third alternative is then *exactly* the `IsMin1` region, so the
pair `(χ, ρ₀)` — which is Legitimate (`χ ≠ χ₀`, `χ ≠ 1`, `zeroMult χ ρ₀ ≠ 0`, `|Im ρ₀| = 0 ≤ 1`,
`λ(ρ₀) ≤ λ(ρ₀)`) — already satisfies the third alternative's minimality clause.  This holds
regardless of whether `λ(ρ₀) ≥ 1/25`, but in fact `λ(ρ₀) ≤ 1/100 < 1/25` rules out the first
alternative anyway.
-/
theorem designatedTrichotomy (hfar : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → Work.LinnikContract.zeroMult χ u ≠ 0 →
    1 ≤ |u.im| → |u.im| ≤ 4 → (1 / 25 : ℝ) ≤ Work.LinnikContract.lamOf q u) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ 1 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      (1 / 25 : ℝ) ≤ Work.LinnikContract.lamOf q ρ ∨
      (∃ ρ' : ℂ, Work.LinnikContract.zeroMult χ₀ ρ' ≠ 0 ∧ |ρ'.im| ≤ 1 ∧ ρ' ≠ ρ₀ ∧
        Work.LinnikContract.lamOf q ρ' < Work.LinnikContract.lamOf q ρ ∧
        (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
          |u.im| ≤ |ρ'.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
            Work.LinnikContract.lamOf q ρ' ≤ Work.LinnikContract.lamOf q u)) ∨
      (∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
        χ₂ ≠ χ₀ ∧ χ₂ ≠ 1 ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ 1 ∧
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
        (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
          |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
            Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)) := by
  obtain ⟨q₀, hdesig⟩ := existsDesignatedDecent hfar
  refine ⟨q₀, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him0 hlam0 χ ρ hχχ₀ hχ1 hzm himρ
  haveI : NeZero q := hqne
  by_cases hρ : ρ = ρ₀
  · -- `ρ = ρ₀`: the pair `(χ, ρ₀)` itself satisfies the third alternative
    refine Or.inr (Or.inr ⟨χ, ρ, hχχ₀, hχ1, hzm, ?_, le_rfl, ?_⟩)
    · -- `|ρ₀.im| ≤ 1`
      rw [hρ, him0]
      norm_num
    · -- ball-minimality at `ρ₀`: `|u.im| ≤ |ρ₀.im| + 1 = 1` is the `IsMin1` region
      intro ψ u hψ hzmu himu _
      rw [hρ]
      exact hmin.2 ψ u ⟨hψ, hzmu, by rw [hρ, him0] at himu; simpa using himu⟩
  · -- `ρ ≠ ρ₀`: apply the `decent` version
    exact hdesig q hq χ₀ ρ₀ hmin hsq him0 hlam0 χ ρ hχχ₀ hχ1 hzm himρ hρ

end Work.LinnikAreas.OtherCharRepel
