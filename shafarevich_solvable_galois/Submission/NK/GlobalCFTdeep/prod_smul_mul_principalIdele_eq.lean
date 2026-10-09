import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep

open scoped NumberField RestrictedProduct

/-- The product over `Gal(L/K)` of the translates of `(σ₀ • x / x) · (b)` in `𝕀 L` is the
principal idèle of `b`'s norm: the first factor's total product is `1` (the product over a group is
invariant under right translation of the index) while
`∏ σ, σ • principalIdele L b = principalIdele L (∏ σ, σ • b)`
(`Galois.globalCFT_smul_principalIdele` together with `map_prod`). -/
theorem prod_smul_mul_principalIdele_eq {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ₀ : L ≃ₐ[K] L) (x : NK.GlobalCFT.Idele L) (b : Lˣ) :
    (∏ σ : L ≃ₐ[K] L, σ • ((σ₀ • x * x⁻¹) * NK.GlobalCFT.Idele.principalIdele L b)) =
      NK.GlobalCFT.Idele.principalIdele L (∏ σ : L ≃ₐ[K] L, σ • b) := by
  -- The translate of the principal idèle of `b` is the principal idèle of the translate of `b`.
  have hkey : ∀ σ : L ≃ₐ[K] L, σ • NK.GlobalCFT.Idele.principalIdele L b
      = NK.GlobalCFT.Idele.principalIdele L (σ • b) := by
    intro σ
    rw [NK.GlobalCFT.Galois.globalCFT_smul_principalIdele]
    rfl
  -- The product of the translates of the "coboundary" `σ₀ • x / x` is `1`, by reindexing the
  -- product over the group `Gal(L/K)` by right translation.
  have hboundary : (∏ σ : L ≃ₐ[K] L, σ • (σ₀ • x * x⁻¹)) = 1 := by
    have hstep : ∀ g : L ≃ₐ[K] L, g • (σ₀ • x * x⁻¹) = (g * σ₀) • x * (g • x)⁻¹ := by
      intro g
      rw [smul_mul', smul_inv', mul_smul]
    have hreindex : (∏ g : L ≃ₐ[K] L, (g * σ₀) • x) = ∏ g : L ≃ₐ[K] L, g • x :=
      Equiv.prod_comp (Equiv.mulRight σ₀) (fun g => g • x)
    calc ∏ g : L ≃ₐ[K] L, g • (σ₀ • x * x⁻¹)
        = ∏ g : L ≃ₐ[K] L, ((g * σ₀) • x * (g • x)⁻¹) :=
          Finset.prod_congr rfl (fun g _ => hstep g)
      _ = (∏ g : L ≃ₐ[K] L, (g * σ₀) • x) * (∏ g : L ≃ₐ[K] L, (g • x)⁻¹) :=
          Finset.prod_mul_distrib
      _ = (∏ g : L ≃ₐ[K] L, (g * σ₀) • x) * (∏ g : L ≃ₐ[K] L, g • x)⁻¹ := by
          rw [Finset.prod_inv_distrib]
      _ = (∏ g : L ≃ₐ[K] L, g • x) * (∏ g : L ≃ₐ[K] L, g • x)⁻¹ := by rw [hreindex]
      _ = 1 := mul_inv_cancel _
  -- Split the product using multiplicativity of the action and conclude.
  have hsplit : (∏ σ : L ≃ₐ[K] L,
        σ • ((σ₀ • x * x⁻¹) * NK.GlobalCFT.Idele.principalIdele L b))
      = (∏ σ : L ≃ₐ[K] L, σ • (σ₀ • x * x⁻¹)) *
        (∏ σ : L ≃ₐ[K] L, σ • NK.GlobalCFT.Idele.principalIdele L b) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun σ _ => smul_mul' _ _ _)
  rw [hsplit, hboundary, one_mul]
  rw [Finset.prod_congr rfl (fun σ (_ : σ ∈ Finset.univ) => hkey σ)]
  rw [map_prod]

end NK.GlobalCFTdeep
