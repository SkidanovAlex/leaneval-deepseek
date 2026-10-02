import Mathlib
import Submission.Work.Cohomology.relCohMV_les
import Submission.Work.StemsB.RatBaseNaturality
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Cohomology.hmv_chain_shortExact
import Submission.Work.Cohomology.hmv_isIso_eta
import Submission.Work.Cohomology.hmv_naturality

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `ℤ → ℚ` dual of a `ℤ`-chain complex, and its comparison with rational cochains

For a `ℤ`-chain complex `C`, the cochain complex `DQ C` is the `ℚ`-dual of the base change
`IntRatCM C = C ⊗[ℤ] ℚ`:  in degree `n` it is `Hom_ℚ(ℚ ⊗[ℤ] Cₙ, ℚ)`, with differential
`f ↦ f ∘ d`.  Since `ℚ` is flat over `ℤ` and a field, the functor `DQ` is exact: it carries short
exact sequences of `ℤ`-chain complexes to short exact sequences of `ℚ`-cochain complexes
(contravariantly).

The absolute comparison `thetaAbs X : C^*(X;ℚ) ≅ DQ (C_*(X;ℤ))` is the dual of the base change
`Phi : C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)` (whose naturality in the space is `RatBC.Phi_naturality`); it
is therefore natural in `X`.

These are the tools with which the rational relative Mayer–Vietoris sequence is built in
`Submission/Work/Serre/relCohMV_les_rat.lean`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-! ## The complex `DQ` and its functoriality -/

/-- The `ℚ`-dual of the base change to `ℚ` of a `ℤ`-chain complex. -/
abbrev DQ (C : ChainComplex (ModuleCat ℤ) ℕ) : CochainComplex (ModuleCat ℚ) ℕ :=
  Work.Cohomology.dualComplex ℚ (Work.StemsB.IntRatCM.obj C)

/-- **The contravariant functoriality of `DQ`.** -/
def dqMap {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) : DQ D ⟶ DQ C :=
  Work.Cohomology.dualComplexMap ℚ (Work.StemsB.IntRatCM.obj C) (Work.StemsB.IntRatCM.obj D)
    (Work.StemsB.IntRatCM.map φ)

theorem dqMap_comp {C D E : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (ψ : D ⟶ E) :
    dqMap (CategoryTheory.CategoryStruct.comp φ ψ)
      = CategoryTheory.CategoryStruct.comp (dqMap ψ) (dqMap φ) := by
  simp only [dqMap, Functor.map_comp, Work.Cohomology.dualComplexMap_comp]

theorem dqMap_id (C : ChainComplex (ModuleCat ℤ) ℕ) :
    dqMap (𝟙 C) = 𝟙 (DQ C) := by
  rw [dqMap, Work.StemsB.IntRatCM.map_id, Work.Cohomology.dualComplexMap_id]

theorem dqMap_zero {C D : ChainComplex (ModuleCat ℤ) ℕ} :
    dqMap (0 : C ⟶ D) = 0 := by
  simp only [dqMap, Functor.map_zero, Work.Cohomology.dualComplexMap_zero]

/-! ## The absolute comparison `C^*(X;ℚ) ≅ DQ (C_*(X;ℤ))` -/

/-- **The absolute comparison morphism**: the rational singular cochains are the `ℚ`-dual of the
base change of the integral singular chains, by pullback along `Phi`. -/
def thetaAbs (X : TopCat) :
    Work.Cohomology.singularCochainComplex ℚ X
      ⟶ DQ (Work.Cohomology.singularChains ℤ X) :=
  Work.Cohomology.dualComplexMap ℚ _ _
    (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom

/-- **Naturality of the absolute comparison** in the space. -/
theorem thetaAbs_natural {X Y : TopCat} (f : X ⟶ Y) :
    thetaAbs Y ≫ dqMap (Work.Cohomology.chainMap ℤ X Y f)
      = Work.Cohomology.dualChainMap ℚ X Y f ≫ thetaAbs X := by
  have h := Work.StemsB.RatBC.Phi_naturality (TopCat.toSSet.map f)
  have hd : Work.Cohomology.dualChainMap ℚ X Y f
      = Work.Cohomology.dualComplexMap ℚ (Work.Cohomology.singularChains ℚ X)
          (Work.Cohomology.singularChains ℚ Y) (Work.Cohomology.chainMap ℚ X Y f) := rfl
  rw [thetaAbs, thetaAbs, dqMap, hd, ← Work.Cohomology.dualComplexMap_comp,
    ← Work.Cohomology.dualComplexMap_comp]
  congr 1
  exact h.symm

end

end Work.Serre
