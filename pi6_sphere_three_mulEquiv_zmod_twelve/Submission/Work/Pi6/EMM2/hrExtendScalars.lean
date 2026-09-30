import Mathlib
import Submission.Work.Pi6.EMM2.extendScalars_homology_iso
import Submission.Work.Cohomology.singularChains_free
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Pi6.K2Z.baseChangeFlat
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Change of coefficients `ℤ → 𝕜` for singular homology in one degree

`Work.Pi6.EMM2.HRisoExtendScalarsTF`: for a topological space `X`, a commutative ring `𝕜` and a
degree `m` in which the integral homology `H_m(X;ℤ)` is torsion-free, the `𝕜`-homology in degree
`m+1` is the extension of scalars of the integral one,

`H_{m+1}(X;𝕜) ≅ 𝕜 ⊗[ℤ] H_{m+1}(X;ℤ)`.

This is the general change-of-coefficients theorem in the single degree `m+1`, with the
torsion-freeness hypothesis in degree `m` that makes the `Tor` term vanish.  The singular chains are
free in every degree, so the chain-level theorem `Work.Pi6.EMM2.extendScalars_homology_iso` applies;
the identification of the `𝕜`-singular chains with the coefficient extension of the integral ones
is `Work.StemsB.SphRat.chainComplexBaseChange` (the same comparison as in
`Work.Pi6.K2Z.baseChangeFlat`).
-/

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

theorem HRisoExtendScalarsTF (𝕜 : Type) [CommRing 𝕜] {X : Type} [TopologicalSpace X] (m : ℕ)
    (hH : Module.IsTorsionFree ℤ (Work.Pi6.HR ℤ X m)) :
    Nonempty (Work.Pi6.HR 𝕜 X (m + 1) ≅
      (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ X (m + 1))) := by
  let F : ModuleCat ℤ ⥤ ModuleCat 𝕜 := ModuleCat.extendScalars (Int.castRingHom 𝕜)
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ Y
  let L : ChainComplex (ModuleCat 𝕜) ℕ := Work.Cohomology.singularChains 𝕜 Y
  -- the `𝕜`-singular chains are the coefficient extension of the integral ones
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Y) (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Y)
        (Work.Pi6.K2Z.extendScalarsIntFieldIso 𝕜)
  -- the integral singular chains are free, hence flat, in every degree
  have hfree : ∀ i : ℕ, Module.Free ℤ (K.X i) := fun i =>
    Work.Cohomology.singularChains_free Y i
  -- the chain-level change of coefficients in degree `m+1`
  obtain ⟨e⟩ := extendScalars_homology_iso 𝕜 K m hfree hH
  exact ⟨(HomologicalComplex.homologyMapIso hΦ (m + 1)).symm ≪≫ e⟩

end

end Work.Pi6.EMM2
