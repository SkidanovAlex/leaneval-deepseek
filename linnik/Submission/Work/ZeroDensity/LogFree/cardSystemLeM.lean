import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.ZeroDensity.LogFree

/-- Enumeration wrapper: a `Finset` of (character, zero) pairs whose members satisfy
pointwise the hypotheses of a cardinality bound `hM` for `Fin`-indexed families can be
enumerated by `Finset.equivFin`, whence its cardinality inherits the bound. -/
theorem cardSystemLeM {q : ℕ} [NeZero q] {σ T L c₀ M : ℝ}
    (hM : ∀ (m : ℕ) (χ : Fin m → DirichletCharacter ℂ q) (ρ : Fin m → ℂ),
        (∀ i, χ i ≠ 1) → (∀ i, Work.LinnikContract.zeroMult (χ i) (ρ i) ≠ 0) →
        (∀ i, σ ≤ (ρ i).re) → (∀ i, (ρ i).re < 1) → (∀ i, |(ρ i).im| ≤ T) →
        (∀ i, c₀ ≤ (1 - (ρ i).re) * L) →
        (∀ i j, i ≠ j → χ i = χ j → 1 / L ≤ |(ρ i).im - (ρ j).im|) →
        (m : ℝ) ≤ M)
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hne : ∀ p ∈ S, p.1 ≠ 1)
    (hzm : ∀ p ∈ S, Work.LinnikContract.zeroMult p.1 p.2 ≠ 0)
    (hσ : ∀ p ∈ S, σ ≤ p.2.re) (hre : ∀ p ∈ S, p.2.re < 1)
    (him : ∀ p ∈ S, |p.2.im| ≤ T)
    (hexc : ∀ p ∈ S, c₀ ≤ (1 - p.2.re) * L)
    (hsep : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 / L ≤ |p.2.im - p'.2.im|) :
    (S.card : ℝ) ≤ M := by
  let e : Fin S.card ≃ ↥S := S.equivFin.symm
  exact hM S.card (fun i => (e i).1.1) (fun i => (e i).1.2)
    (fun i => hne (e i).1 (e i).2)
    (fun i => hzm (e i).1 (e i).2)
    (fun i => hσ (e i).1 (e i).2)
    (fun i => hre (e i).1 (e i).2)
    (fun i => him (e i).1 (e i).2)
    (fun i => hexc (e i).1 (e i).2)
    (fun i j hij hχ => by
      have hne' : (e i).1 ≠ (e j).1 := by
        intro h
        exact hij (e.injective (Subtype.ext h))
      exact hsep (e i).1 (e i).2 (e j).1 (e j).2 hne' hχ)

end Work.ZeroDensity.LogFree
