import Mathlib
import Submission.Work.SSGRoute.e7comega_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The places of an `Ω`-level over the `Gal(K/k)`-orbit of a place of `K` form a single
`Gal(L/k)`-orbit.**  Put it in namespace `Work.SSGRoute`.  If `u` is a place of the level `L` over
`w` and `v` is a place of `L` whose place below `u'` is the `Gal(K/k)`-conjugate `σ • w` of `w`,
then `v` is a `Gal(L/k)`-conjugate of `u`.  Ingredients: the transitivity statement
`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver` for the Galois extension `↥L / K`
(applied to `τ • u` and `v`, both over `u'`), surjectivity of the restriction
`AlgEquiv.restrictNormalHom K` for `↥L / K` (lift `σ` to `σ̃`), and
`NK.HassePrinciple.liesOver_smul_of_restrict` (a place stays over its place under the restricted
automorphism).  Conclude with the `Gal(↥L/K)`-element obtained from transitivity, composed with
`σ̃` after coercing it to a `k`-algebra automorphism.  The instances `FiniteDimensional K ↥L` and
`IsGalois K ↥L` are derivable (`FiniteDimensional.right`, `IsGalois.tower_top_of_isGalois`); the
file `Submission/Work/SSGRoute/decompK_restrict_surjective.lean` (around line 394) does exactly
this. -/
theorem exists_smul_eq_of_liesOver_under {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (u : NK.GlobalCFT.Place ↥L)
    (hu : NK.GlobalCFT.Place.LiesOver u w)
    (v : NK.GlobalCFT.Place ↥L) (u' : NK.GlobalCFT.Place K)
    (hu' : NK.GlobalCFT.Place.LiesOver v u')
    (σ : K ≃ₐ[k] K) (hσ : σ • w = u') :
    ∃ τ : ↥L ≃ₐ[k] ↥L, τ • u = v := by
  haveI : IsGalois K ↥L := IsGalois.tower_top_of_isGalois k K ↥L
  haveI : FiniteDimensional K ↥L := FiniteDimensional.right k K ↥L
  -- Lift `σ : Gal(K/k)` to some `σ̃ : Gal(↥L/k)` restricting to `σ`.
  obtain ⟨σt, hσt⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) ↥L σ
  have hA : ∀ y : K, algebraMap K ↥L (σ y) = σt (algebraMap K ↥L y) := by
    intro y
    have hres : σt.restrictNormal K = σ := hσt
    rw [← hres]
    exact AlgEquiv.restrictNormal_commutes σt K y
  -- The lifted place `σ̃ • u` still lies over `u' = σ • w`.
  have hlies : NK.GlobalCFT.Place.LiesOver (σt • u) u' := by
    have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := ↥L) σt σ hA hu
    rwa [hσ] at h1
  -- Transitivity of `Gal(↥L/K)` on the places over `u'`.
  obtain ⟨ρ, hρ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := K) (L := ↥L) hlies hu'
  have hsmul : ∀ x : NK.GlobalCFT.Place ↥L, (AlgEquiv.restrictScalars k ρ) • x = ρ • x :=
    fun x => rfl
  refine ⟨(AlgEquiv.restrictScalars k ρ) * σt, ?_⟩
  rw [mul_smul, hsmul, hρ]

end Work.SSGRoute
