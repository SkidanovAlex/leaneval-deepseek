/-
AREA TOOLKIT — coproduct/colimit instances for `LightCondAb` and `Cpx`.

Instance search for `HasColimitsOfShape (Discrete J) LightCondAb` (and hence for small
coproducts in light condensed abelian groups and in cochain complexes) times out at the default
heartbeat limit, because unification has to unfold `LightCondMod`, `LightCondensed` and the
`SmallModel` machinery of the essentially small site.  The instances below are stated directly in
terms of `LightCondAb`, so that they are found immediately.  They are the same terms that Mathlib
provides for sheaves.

With these instances, all of the following are synthesized by `inferInstance`:
`HasCoproduct f` in `LightCondAb` and in `Cpx`, `HasExactColimitsOfShape (Discrete J) LightCondAb`
(i.e. Grothendieck's AB4: small coproducts are exact) and `HasExactColimitsOfShape ℕ LightCondAb`
(AB5).

This file depends only on Mathlib.
-/
import Mathlib

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

namespace Work.TOOLKIT

/-- `LightCondAb` is a Grothendieck abelian category, hence has all small colimits. -/
instance instHasColimitsA : HasColimitsOfSize.{0, 0} LightCondAb :=
  IsGrothendieckAbelian.hasColimits LightCondAb

/-- Small coproducts in light condensed abelian groups exist. -/
instance instHasCoprodA (J : Type) : HasColimitsOfShape (Discrete J) LightCondAb :=
  HasColimitsOfSize.has_colimits_of_shape (Discrete J)

/-- Small coproducts in cochain complexes of light condensed abelian groups exist. -/
instance instHasCoprodCpx (J : Type) : HasColimitsOfShape (Discrete J) (CochainComplex LightCondAb ℤ) :=
  HomologicalComplex.instHasColimitsOfShape

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Grothendieck's AB4 for light condensed abelian groups: small coproducts are exact. -/
instance instAB4 : AB4OfSize.{0} LightCondAb := AB4.of_AB5 LightCondAb

end Work.TOOLKIT
