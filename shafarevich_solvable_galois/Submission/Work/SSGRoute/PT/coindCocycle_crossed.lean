import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **The Shapiro cochain is a crossed homomorphism.**  For any `1`-cocycle `φ : U → M` on the
subgroup `U ≤ G`, the cochain `g ↦ (x ↦ coord U x • φ (A g (x U)))` on `G` with values in the
coinduced module `Coind G U M` satisfies the crossed-homomorphism identity

  `coindCocycle U φ (g * h) = g • coindCocycle U φ h + coindCocycle U φ g`.

Pointwise at `x : G` this is exactly the multiplicativity `A (g*h) (x U) = A g (x U) * A h (g⁻¹ • x U)`
of the `U`-coordinates together with the equivariance `coord U (g⁻¹ * x) = coord U x * A g (x U)`,
fed into the crossed-homomorphism identity for `φ`. -/
theorem coindCocycle_crossed {G : Type*} [Group G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (φ : U → M)
    (hφ : Work.GroupCohomology.IsCrossedHom U M φ) (g h : G) :
    Work.SSGRoute.PT.coindCocycle U φ (g * h) =
      g • Work.SSGRoute.PT.coindCocycle U φ h + Work.SSGRoute.PT.coindCocycle U φ g := by
  apply Subtype.ext
  funext x
  simp only [coindCocycle_apply, Coind.smul_apply, AddSubgroup.coe_add, Pi.add_apply]
  rw [coset_smul U g x]
  rw [A_mul' U g h (x : G ⧸ U)]
  rw [coord_smul U g x]
  rw [hφ (Shapiro.A 0 G U g (x : G ⧸ U))
        (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)))]
  simp only [smul_add, mul_smul]

end Work.SSGRoute.PT
