import Mathlib
import Submission.Work.SSSR.serreE1CoefExplicit
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The components of the normalized coefficient isomorphism

`Work.SSSR.normalizedCoeffIsoIso X M : X.normalizedChainComplex M ≅ expTens (X.normalizedChainComplex R) M`
is by definition `Work.SSSR.normCoeff_coeffIso X M (Work.SSSR.sigmaConstTensorIsoIso M)`, i.e. the
composite

`e₂.symm ≪≫ e₁`

where `e₂` is the chain isomorphism with components `(sigmaConstTensorIsoIso M).app (X.splitting.N n)`
(coming from the natural transformation `sigmaConst.obj R ⋙ tensorRight M ⟶ sigmaConst.obj M`) and
`e₁ = normCoeff_map_tensorRight_iso ...` is the comparison `(s.map (tensorRight M)).nondegComplex ≅
expTens s.nondegComplex M`, which is the identity on objects (its components are `Iso.refl`).

Hence the `d`-th component of `(normalizedCoeffIsoIso X M).hom` is
`(sigmaConstTensorIsoIso M).app (X.splitting.N d)⁻¹ ≫ 𝟙 = CategoryTheory.inv ((sigmaConstTensorIsoIso M).hom.app (X.splitting.N d))`.

The `set_option` below is needed because the defining equations of `normCoeff_coeffIso` and
`normCoeff_map_tensorRight_iso` were themselves elaborated with `backward.isDefEq.respectTransparency
false` (the coproduct/instance diamonds of `ModuleCat` force this); unfolding them requires the same
setting.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS

theorem normalizedCoeffIsoIso_hom_f {R : Type} [CommRing R] [Nontrivial R] (X : SSet.{0})
    (M : ModuleCat R) (d : ℕ) :
    (Work.SSSR.normalizedCoeffIsoIso X M).hom.f d
      = CategoryTheory.inv ((Work.SSSR.sigmaConstTensorIsoIso M).hom.app (X.splitting.N d)) := by
  unfold Work.SSSR.normalizedCoeffIsoIso Work.SSSR.normCoeff_coeffIso
  rw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.symm_hom]
  simp only [HomologicalComplex.Hom.isoOfComponents_inv_f]
  rw [Work.SSSR.normCoeff_map_tensorRight_iso.eq_def]
  simp only [HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom, Category.comp_id]
  simp

end Work.Pi6.MSS
