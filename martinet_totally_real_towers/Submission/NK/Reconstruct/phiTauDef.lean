import Submission.NK.Reconstruct.ambient4f3
import Submission.NK.Reconstruct.gammaHaus
import Submission.NK.Reconstruct.tauStarDef
import Submission.NK.Reconstruct.continuous_tauStar
import Submission.NK.Reconstruct.denseSet_avoidClosedSubgroups
import Submission.NK.Reconstruct.gammaBaseChange

/-!
# The maps `φ_τ` and their torsion-free quotients `Ψ_τ` of Shimizu's Proposition 4f.3

For `τ ∈ Gal(L/ℚ)`, Shimizu's Proposition 4f.3 (arXiv:2009.10431, §4) forms the homomorphism

  `φ_τ : Γ_L → Γ_{K₂},  γ ↦ (σ̄ ∘ π_{L/K₁})(γ) · ((π_{L/K₂} ∘ τ^*)(γ))⁻¹`

(the target being abelian, this pointwise product is a homomorphism), and observes that the
assumption "for all `τ`, `σ̄ ∘ π_{L/K₁} ≠ π_{L/K₂} ∘ τ^*`" says precisely that all `φ_τ` are
non-trivial.  The Baire/measure step of the proof needs `ker φ_τ` to be *closed and not open*; on
`Γ_L` this is supplied by passing to the torsion-free quotient
`Ψ_τ : Γ_L → Γ_{K₂}^{tf}` (`NK.Reconstruct.gammaHausLift`), whose non-trivial elements have
non-open kernels (`NK.Reconstruct.not_isOpen_ker_of_continuous_to_gammaHaus`).

## Contents

* `NK.Reconstruct.phiTau'` — the homomorphism `φ_τ`;
* `NK.Reconstruct.phiTau'_continuous` — its continuity;
* `NK.Reconstruct.psiTau'` — the composite `Γ_L → Γ_L^{tf} → Γ_{K₂}^{tf}`;
* `NK.Reconstruct.psiTau'_continuous`, `psiTau'_apply`;
* `NK.Reconstruct.psiTau'_eq_one_iff` — `Ψ_τ = 1` iff the two sides of Shimizu's conclusion agree
  after `gammaHausMk` (the form consumed by Lemma 4f.4).

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Prop. 4f.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField


open NK.Chebotarev
open scoped NumberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- φ_τ. -/
noncomputable def phiTau' (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ)
    (τstar : Gamma ↥L.L Ω ℓ ≃* Gamma ↥L.L Ω ℓ) :
    Gamma ↥L.L Ω ℓ →* Gamma ↥K₂.L Ω ℓ :=
  ((σbar : Gamma ↥K₁.L Ω ℓ →* Gamma ↥K₂.L Ω ℓ).comp (ambientPi K₁ L h₁ ℓ))
    * (((ambientPi K₂ L h₂ ℓ).comp (τstar : Gamma ↥L.L Ω ℓ →* Gamma ↥L.L Ω ℓ))⁻¹)

theorem phiTau'_continuous (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (τstar : Gamma ↥L.L Ω ℓ ≃* Gamma ↥L.L Ω ℓ) (hτ : Continuous ⇑τstar) :
    Continuous ⇑(phiTau' K₁ K₂ L h₁ h₂ ℓ σbar τstar) := by
  unfold phiTau'
  refine Continuous.mul ?_ (Continuous.inv ?_)
  · exact hσbar.comp (gammaBaseChange_continuous (K := ↥K₁.L) (K' := Ω) ℓ (levelExtendGen K₁ L h₁))
  · exact (gammaBaseChange_continuous (K := ↥K₂.L) (K' := Ω) ℓ (levelExtendGen K₂ L h₂)).comp hτ

/-- Ψ_τ : Γ_L → Γ_{K₂}^{tf}. -/
noncomputable def psiTau' (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (τstar : Gamma ↥L.L Ω ℓ ≃* Gamma ↥L.L Ω ℓ) (hτ : Continuous ⇑τstar) :
    Gamma ↥L.L Ω ℓ →* GammaHaus ↥K₂.L Ω ℓ :=
  (gammaHausLift ℓ (phiTau' K₁ K₂ L h₁ h₂ ℓ σbar τstar)
      (phiTau'_continuous K₁ K₂ L h₁ h₂ ℓ σbar hσbar τstar hτ)).comp
    (gammaHausMk ↥L.L Ω ℓ)

theorem psiTau'_continuous (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (τstar : Gamma ↥L.L Ω ℓ ≃* Gamma ↥L.L Ω ℓ) (hτ : Continuous ⇑τstar) :
    Continuous ⇑(psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar τstar hτ) :=
  (continuous_gammaHausLift ℓ _ _).comp (continuous_gammaHausMk (K := ↥L.L) (K' := Ω) (ℓ := ℓ))

theorem psiTau'_apply (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (τstar : Gamma ↥L.L Ω ℓ ≃* Gamma ↥L.L Ω ℓ) (hτ : Continuous ⇑τstar)
    (γ : Gamma ↥L.L Ω ℓ) :
    psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar τstar hτ γ
      = gammaHausMk ↥K₂.L Ω ℓ (phiTau' K₁ K₂ L h₁ h₂ ℓ σbar τstar γ) :=
  gammaHausLift_comp ℓ _ _ γ

/-- The equivalence needed to convert the negation of the conclusion into `Ψ_τ ≠ 1`. -/
theorem psiTau'_eq_one_iff (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (τstar : Gamma ↥L.L Ω ℓ ≃* Gamma ↥L.L Ω ℓ) (hτ : Continuous ⇑τstar) :
    psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar τstar hτ = 1
      ↔ ∀ γ : Gamma ↥L.L Ω ℓ,
          gammaHausMk ↥K₂.L Ω ℓ (σbar (ambientPi K₁ L h₁ ℓ γ))
            = gammaHausMk ↥K₂.L Ω ℓ (ambientPi K₂ L h₂ ℓ (τstar γ)) := by
  constructor
  · intro h γ
    have h1 : psiTau' K₁ K₂ L h₁ h₂ ℓ σbar hσbar τstar hτ γ = 1 := by rw [h]; rfl
    rw [psiTau'_apply] at h1
    have h2 : gammaHausMk ↥K₂.L Ω ℓ (σbar (ambientPi K₁ L h₁ ℓ γ))
        * (gammaHausMk ↥K₂.L Ω ℓ (ambientPi K₂ L h₂ ℓ (τstar γ)))⁻¹ = 1 := by
      have h3 := h1
      simp only [phiTau', MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply,
        map_mul, map_inv] at h3
      exact h3
    exact mul_inv_eq_one.mp h2
  · intro h
    refine MonoidHom.ext fun γ => ?_
    rw [psiTau'_apply]
    have h1 : gammaHausMk ↥K₂.L Ω ℓ (phiTau' K₁ K₂ L h₁ h₂ ℓ σbar τstar γ)
        = 1 := by
      simp only [phiTau', MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply,
        map_mul, map_inv]
      change gammaHausMk ↥K₂.L Ω ℓ (σbar ((ambientPi K₁ L h₁ ℓ) γ))
        * (gammaHausMk ↥K₂.L Ω ℓ ((ambientPi K₂ L h₂ ℓ) (τstar γ)))⁻¹ = 1
      rw [h γ, mul_inv_cancel]
    exact h1


end NK.Reconstruct
