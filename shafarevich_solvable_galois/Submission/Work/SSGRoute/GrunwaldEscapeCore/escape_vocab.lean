import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ges_escape_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the correction node of Grünwald with escape

`Work.SSGRoute.GrunwaldEscapeCore.gesU` is the open finite-index subgroup of the idèle class group
`C_K` whose class field is the field in which the escape prime is chosen:

`U = im(Kˣ · E_{T,unr})` where `E_{T,unr}` consists of the idèles whose component at every prime of
`T'` is a `p`-th power and whose component outside the places above `T'` is a local unit.

Its openness is `Work.SSGRoute.isOpen_gesU` (`ges_escape_aux.lean`, proved) and its finite index is
`Work.SSGRoute.finiteIndex_gesU` (proved).

`Work.SSGRoute.GrunwaldEscapeCore.gesReadOff` states the "reading off" of `U`, which is the local
half of the escape construction: a fractional ideal coprime to `T'` whose idèle class lies in `U`
is `(γ)·𝔡^p` with `γ` a local `p`-th power at every prime of `T'`.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open _root_.SSGRoute

/-- **The subgroup `U` of the idèle class group** underlying the escape construction (the class
field of `U` is the field `M` of the design's route). -/
noncomputable def gesU (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal K)) : Subgroup (NK.GlobalCFT.IdeleClassGroup K) :=
  (NK.GlobalCFT.Idele.principalSubgroup K ⊔ Work.SSGRoute.powTIdeles K p T').map
    (NK.GlobalCFT.IdeleClassGroup.mk K)

end Work.SSGRoute.GrunwaldEscapeCore
