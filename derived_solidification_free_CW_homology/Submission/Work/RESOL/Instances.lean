/-
AREA RESOL — coproduct/colimit instances for `LightCondAb` and `Cpx`.

Instance search for `HasColimitsOfShape (Discrete J) LightCondAb` (equivalently `HasCoproduct` on a
family of light condensed abelian groups) times out at the default heartbeats, because the
unification has to unfold `LightCondMod` and the `SmallModel` machinery of the essentially small
site.  The instances below are stated directly, so that they are found immediately.

This block is taken from `NOTES_LEAD_solid_gaps1.md` §0 (verified by the lead).  With it,
`HasCoproduct` in `LightCondAb` and in `CochainComplex LightCondAb ℤ`, AB4 and AB5 for
`LightCondAb`, and `HasTotal` for a bicomplex of cochain complexes are all found instantly.
`HasCoproduct` is a `Prop`, so the coproduct built from these instances is definitionally the
coproduct built from a user-supplied `[HasCoproduct K]` (proof irrelevance).
-/
import Mathlib
import ChallengeDeps

open CategoryTheory Limits

noncomputable section

namespace Work.RESOL

attribute [local instance] Abelian.hasFiniteBiproducts

instance instHasColimitsA : HasColimitsOfSize.{0, 0} LightCondAb :=
  IsGrothendieckAbelian.hasColimits LightCondAb

instance instHasCoprodA (J : Type) : HasColimitsOfShape (Discrete J) LightCondAb :=
  HasColimitsOfSize.has_colimits_of_shape (Discrete J)

instance instHasCoprodCpx (J : Type) :
    HasColimitsOfShape (Discrete J) (CochainComplex LightCondAb ℤ) :=
  HomologicalComplex.instHasColimitsOfShape

instance instAB4 : AB4OfSize.{0} LightCondAb := AB4.of_AB5 LightCondAb

end Work.RESOL
