import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK

theorem AwayAlgEquivOfComp {K : Type} [Field K] {n : ℕ}
    (F G : MvPolynomial (Fin n) K)
    (Φ : Localization.Away F →ₐ[K] Localization.Away G)
    (Ψ : Localization.Away G →ₐ[K] Localization.Away F)
    (h1 : ∀ i : Fin n,
      Ψ (Φ (algebraMap (MvPolynomial (Fin n) K) (Localization.Away F) (MvPolynomial.X i)))
        = algebraMap (MvPolynomial (Fin n) K) (Localization.Away F) (MvPolynomial.X i))
    (h2 : ∀ i : Fin n,
      Φ (Ψ (algebraMap (MvPolynomial (Fin n) K) (Localization.Away G) (MvPolynomial.X i)))
        = algebraMap (MvPolynomial (Fin n) K) (Localization.Away G) (MvPolynomial.X i)) :
    Nonempty (Localization.Away F ≃ₐ[K] Localization.Away G) := by
  -- On the `A := K[X_1,…,X_n]`-generators `X i`, the composite `Ψ ∘ Φ` fixes the image of `A`,
  -- so as an endomorphism of the localisation `A[1/F]` it is the identity.
  have hΘ : Ψ.comp Φ = AlgHom.id K (Localization.Away F) := by
    apply IsLocalization.algHom_ext (Submonoid.powers F)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    exact h1 i
  have hΞ : Φ.comp Ψ = AlgHom.id K (Localization.Away G) := by
    apply IsLocalization.algHom_ext (Submonoid.powers G)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    exact h2 i
  exact ⟨AlgEquiv.ofAlgHom Φ Ψ hΞ hΘ⟩

end Work.MotK
