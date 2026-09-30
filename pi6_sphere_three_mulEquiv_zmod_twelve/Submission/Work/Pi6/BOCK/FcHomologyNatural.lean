import Mathlib
import Submission.Work.Pi6.BOCK.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.BOCK

noncomputable section

/-- **Naturality of the homology comparison `H_n(F(K)) ≅ F(H_n(K))`.** -/
theorem fcHomologyIsoNatural {𝕜 : Type*} [CommRing 𝕜]
    (F : ModuleCat 𝕜 ⥤ ModuleCat ℤ) [F.Additive] [F.PreservesHomology]
    (K K' : ChainComplex (ModuleCat 𝕜) ℕ) (φ : K ⟶ K') (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n ≫
      (fcHomologyIso F K' n).hom =
    (fcHomologyIso F K n).hom ≫ F.map (HomologicalComplex.homologyMap φ n) := by
  have hmap : (F.mapShortComplex).map
        ((shortComplexFunctor (ModuleCat 𝕜) (ComplexShape.down ℕ) n).map φ) =
      (shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) := by
    ext <;> rfl
  have h := ShortComplex.mapHomologyIso_hom_naturality (F := F)
    (S₁ := K.sc n) (S₂ := K'.sc n)
    ((shortComplexFunctor (ModuleCat 𝕜) (ComplexShape.down ℕ) n).map φ)
  simp only [HomologicalComplex.homologyMap, fcHomologyIso, hmap] at h ⊢
  exact h

end

end Work.Pi6.BOCK
