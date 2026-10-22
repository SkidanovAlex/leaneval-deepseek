import Mathlib
import Submission.Work.TOOLKIT.Basic

/-!
# Coproducts of cochain complexes of light condensed abelian groups

This file provides the instances and definitions used by
`Submission.Work.TOOLKIT.Sigma.quasiIso_sigma`.

`LightCondAb` is a Grothendieck abelian category, hence satisfies AB4: small coproducts
are exact.  We make the relevant instances available explicitly (they are found by
typeclass search only with difficulty), and we set up the canonical comparison maps
between coproducts of (co)kernels and (co)kernels of coproducts.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open scoped CategoryTheory.Pretriangulated.Opposite

namespace Work.TOOLKIT

noncomputable section

/-! ## Colimits and exactness of coproducts in `LightCondAb` and `Cpx` -/

/-- Coproducts of light condensed abelian groups exist: they are computed by sheafifying
the pointwise coproduct. -/
instance instHasColimitsOfShapeDiscreteLightCondAb (J : Type) :
    HasColimitsOfShape (Discrete J) LightCondAb where
  has_colimit F := by
    haveI : HasColimitsOfShape (Discrete J) (ModuleCat.{0} ℤ) := inferInstance
    exact HasColimit.mk
      ⟨Sheaf.sheafifyCocone (colimit.cocone (F ⋙ sheafToPresheaf _ _)),
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩

/-- Small coproducts are exact in `LightCondAb`: `LightCondAb` is a Grothendieck abelian
category (AB5), hence AB4. -/
instance instHasExactColimitsOfShapeDiscreteLightCondAb (J : Type) :
    HasExactColimitsOfShape (Discrete J) LightCondAb := by
  haveI : HasColimitsOfShape (Discrete J) (ModuleCat.{0} ℤ) := inferInstance
  haveI : HasExactColimitsOfShape (Discrete J) (ModuleCat.{0} ℤ) := inferInstance
  haveI : HasColimitsOfShape (Discrete J) LightCondAb := inferInstance
  exact Sheaf.hasExactColimitsOfShape (coherentTopology LightProfinite.{0})

instance instHasCoproductsLightCondAb : HasCoproducts.{0} LightCondAb := fun J => inferInstance

/-- `LightCondAb` satisfies AB4 (all small coproducts are exact). -/
instance instAB4LightCondAb : AB4OfSize.{0} LightCondAb where
  ofShape _ := instHasExactColimitsOfShapeDiscreteLightCondAb _

/-- Coproducts of cochain complexes of light condensed abelian groups exist. -/
instance instHasColimitsOfShapeDiscreteCpx (J : Type) :
    HasColimitsOfShape (Discrete J) Cpx where
  has_colimit F := by
    haveI : HasColimitsOfShape (Discrete J) LightCondAb := inferInstance
    haveI : ∀ n : ℤ, HasColimit (F ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n) :=
      fun n => HasColimitsOfShape.has_colimit _
    exact HasColimit.mk
      ⟨HomologicalComplex.coconeOfHasColimitEval F,
        HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩

/-- Coproducts of cochain complexes of light condensed abelian groups are exact. -/
instance instHasExactColimitsOfShapeDiscreteCpx (J : Type) :
    HasExactColimitsOfShape (Discrete J) Cpx := by
  haveI : HasColimitsOfShape (Discrete J) LightCondAb := inferInstance
  haveI : HasExactColimitsOfShape (Discrete J) LightCondAb := inferInstance
  exact HomologicalComplex.hasExactColimitsOfShape LightCondAb (ComplexShape.up ℤ) (Discrete J)

instance instHasCoproductsCpx : HasCoproducts.{0} Cpx := fun J => inferInstance

/-- The category of cochain complexes of light condensed abelian groups satisfies AB4. -/
instance instAB4Cpx : AB4OfSize.{0} Cpx where
  ofShape _ := instHasExactColimitsOfShapeDiscreteCpx _

end

end Work.TOOLKIT
