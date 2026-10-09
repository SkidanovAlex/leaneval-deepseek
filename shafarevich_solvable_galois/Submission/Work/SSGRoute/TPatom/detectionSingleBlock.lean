import Mathlib
import Submission.Work.SSGRoute.TPatom.valueFormulaDirac
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Single-block detection

The final step of the value side of the unramified detector: if the coefficient functional of *one*
block `x₀` is non-zero at the additive character value `y (c x₀ d^f)`, and the character kills the
coefficient values of all other blocks, then the Shapiro cocycle's value at `d` is not killed by
`μ`.  This is the form in which the detector consumes the *arithmetic* input (the existence of a
level and a character with exactly one non-killed block); the character values are written in the
additive notation `Multiplicative.toAdd`.
-/

namespace Work.SSGRoute.TPatom

open CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- **Single-block detection.** -/
theorem shapiroValue_ne_zero_of_single_block {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    {H : Subgroup Γ} (hH : H.Normal)
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H) [Finite W]
    (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (c : Γ → Γ → ↥H)
    (hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ))
    (hcunit : ∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1)
    (hcoinv : ∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ)
    (y : ↥H →* Multiplicative W.V)
    (D : Subgroup Γ) (d : ↥D) (f : ℕ) (hf : 0 < f)
    (hdH : ((d : Γ)) ^ f ∈ H)
    (X : Finset Γ)
    (hpart : ∀ γ : Γ, ∃! q : Γ × Fin f, q.1 ∈ X ∧ γ * (q.1 * (d : Γ) ^ (q.2 : ℕ))⁻¹ ∈ H)
    (hblock : ∀ x ∈ X, ∀ δ : ↥D, ∃ j : Fin f,
      (x * (δ : Γ)) * (x * (d : Γ) ^ (j : ℕ))⁻¹ ∈ H)
    {M : Type} [AddCommGroup M] [Module SSGRoute.PTExt.Coeff M]
    (μ : Rep.res D.subtype (Rep.coind H.subtype W) ⟶
      Rep.trivial SSGRoute.PTExt.Coeff ↥D M)
    (x₀ : Γ) (hx₀ : x₀ ∈ X)
    (hinj : ∀ a : W.V, a ≠ 0 →
      (μ.hom.toAddMonoidHom.comp
        (Work.Sha2Lib.diracHom W (fun n _ a => htriv n a) x₀)) a ≠ 0)
    (hne : Multiplicative.toAdd (y (c x₀ ((d : Γ) ^ f))) ≠ 0)
    (hvan : ∀ x ∈ X, x ≠ x₀ → Multiplicative.toAdd (y (c x ((d : Γ) ^ f))) = 0) :
    μ.hom
        (⟨fun g : Γ => Multiplicative.toAdd (y (c g (d : Γ))), by
          intro n g
          show Multiplicative.toAdd (y (c ((n : Γ) * g) (d : Γ)))
            = W.ρ n (Multiplicative.toAdd (y (c g (d : Γ))))
          rw [hcoinv g (d : Γ) n]
          exact (htriv n _).symm⟩ : (Rep.coind H.subtype W).V)
      ≠ 0 := by
  classical
  obtain ⟨cwf, hsupp, hdecomp, hval, hcanon⟩ :=
    coindValueFormula_dirac hH W htriv c hcmul hcunit hcoinv y D d f hf hdH X hpart hblock μ
  have hcanon' : cwf x₀ = (μ.hom.toAddMonoidHom.comp
      (Work.Sha2Lib.diracHom W (fun n _ a => htriv n a) x₀)) := by
    simpa only [] using hcanon x₀ hx₀
  rw [hval, Finset.sum_eq_single x₀]
  · rw [hcanon']
    exact hinj _ hne
  · intro x hx hne'
    rw [hvan x hx hne', map_zero]
  · intro hnot
    exact absurd hx₀ hnot

end Work.SSGRoute.TPatom
