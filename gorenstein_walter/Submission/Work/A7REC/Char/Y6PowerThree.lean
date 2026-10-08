import Mathlib
import Submission.Work.A7REC.Char.Y6Defs
import Submission.OddOrder.GroupTheory.RepresentationTheory.CyclotomicGaloisAction

namespace Work.A7REC.Char

open OddOrder.RepresentationTheory

/-- **The power map `g ↦ g³` on elements of order `7`** (`A7Y6PowerThreeProp`).

Let `ρ` be an irreducible degree-`6` representation of a finite group `G` over `ℂ`, and
suppose that the degree-`6` irreducible character is unique (every irreducible degree-`6`
representation has the same trace function as `ρ`).  Then for `x` of order `7`,
`tr (ρ (x³)) = tr (ρ x)`.

The proof picks a cyclotomic Galois automorphism `σ : ℂ ≃+* ℂ` acting as `ζ ↦ ζ³` on the
`7`-th roots of unity (Peterfalvi (1.9), `exists_complexRingEquiv_pow_of_rootsOfUnity`),
twists `ρ` by `σ` (`galoisTwist`), which stays irreducible of degree `6`, and invokes the
uniqueness hypothesis: its character `σ ∘ χ_ρ` equals `χ_ρ`.  Since the eigenvalues of
`ρ x` are `7`-th roots of unity, `σ (χ_ρ x) = χ_ρ (x³)`, whence the claim. -/
theorem Y6PowerThree : Work.A7REC.A7Y6PowerThreeProp := by
  intro G _ _ V _ _ _ ρ hirr hdim huniq x hx
  -- A cyclotomic Galois automorphism acting as `ζ ↦ ζ ^ 3` on `7`-th roots of unity.
  obtain ⟨σ, hσ⟩ :=
    exists_complexRingEquiv_pow_of_rootsOfUnity (n := 7) (k := 3) (by norm_num) (by norm_num)
  -- The `σ`-twist of `ρ`.
  let b := Module.Free.chooseBasis ℂ V
  let ρ' := galoisTwist σ ρ b
  have hρ'irr : Representation.IsIrreducible ρ' := isIrreducible_galoisTwist σ b hirr
  have hdim' : Module.finrank ℂ (Module.Free.ChooseBasisIndex ℂ V → ℂ) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, (Module.finrank_eq_card_basis b).symm]
    exact hdim
  -- Uniqueness of the degree-`6` character, applied to the twist.
  have hTraceEq : ∀ g : G,
      LinearMap.trace ℂ (Module.Free.ChooseBasisIndex ℂ V → ℂ) (ρ' g) =
        LinearMap.trace ℂ V (ρ g) :=
    huniq _ ρ' hρ'irr hdim'
  -- The character of the twist is `σ ∘ χ_ρ`.
  have hcharTwist : σ (LinearMap.trace ℂ V (ρ x)) =
      LinearMap.trace ℂ V (ρ x) := by
    have h1 := hTraceEq x
    have h2 : LinearMap.trace ℂ (Module.Free.ChooseBasisIndex ℂ V → ℂ) (ρ' x) =
        σ (LinearMap.trace ℂ V (ρ x)) := by
      simpa [ρ', b, Representation.character] using character_galoisTwist σ ρ b x
    rw [h2] at h1
    exact h1
  -- On `7`-th roots of unity, `σ` is the power map `ζ ↦ ζ ^ 3`.
  have hσ7 : ∀ ζ : ℂ, ζ ^ orderOf x = 1 → σ ζ = ζ ^ 3 := by
    intro ζ hζ
    rw [hx] at hζ
    exact hσ ζ hζ
  -- `σ (χ_ρ x) = χ_ρ (x³)`, because the eigenvalues of `ρ x` are `7`-th roots of unity.
  have hpow : σ (LinearMap.trace ℂ V (ρ x)) =
      LinearMap.trace ℂ V (ρ (x ^ 3)) := by
    simpa [Representation.character] using
      map_character_eq_character_pow σ ρ (isOfFinOrder_of_finite x) (k := 3) hσ7
  rw [← hpow, hcharTwist]

end Work.A7REC.Char
