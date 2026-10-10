import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cOmega

theorem mem_orbit_of_liesOver_conj {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w) (v : NK.GlobalCFT.Place L) (σ : K ≃ₐ[k] K)
    (hv : NK.GlobalCFT.Place.LiesOver v (σ • w)) :
    ∃ ρ : L ≃ₐ[k] L, ρ • w' = v := by
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
  -- lift `σ : Gal(K/k)` to an automorphism `σt : Gal(L/k)`
  obtain ⟨σt, hσt⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) L σ
  have hA : ∀ y : K, algebraMap K L (σ y) = σt (algebraMap K L y) := by
    intro y
    have hres : σt.restrictNormal K = σ := hσt
    rw [← hres]
    exact AlgEquiv.restrictNormal_commutes σt K y
  -- the lifted place `σt • w'` still lies over `σ • w`
  have hlies : NK.GlobalCFT.Place.LiesOver (σt • w') (σ • w) :=
    NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L) σt σ hA hw'
  -- transitivity of `Gal(L/K)` on the places over `σ • w`
  obtain ⟨ρ, hρ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := K) (L := L) hlies hv
  have hsmul : ∀ x : NK.GlobalCFT.Place L, (AlgEquiv.restrictScalars k ρ) • x = ρ • x :=
    fun x => rfl
  refine ⟨(AlgEquiv.restrictScalars k ρ) * σt, ?_⟩
  rw [mul_smul, hsmul, hρ]

end Work.SSGRoute.E7cOmega
