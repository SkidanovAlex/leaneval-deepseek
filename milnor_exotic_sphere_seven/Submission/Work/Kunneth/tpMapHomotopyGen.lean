import Mathlib
import Submission.Work.Kunneth.EZAWTensor
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.tpMap_homotopy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

/-- Homotopy invariance of Milnor's Koszul tensor product `tpMap` of chain maps: if `f ~ f'` and
`g ~ g'`, then `tpMap f g ~ tpMap f' g'`.  This is the two-variable form of
`Work.Kunneth.tpMap_homotopy`, obtained by splicing the first-variable and second-variable
one-sided homotopies. -/
theorem tpMapHomotopyGen (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ)
    (f f' : Work.Kunneth.chHom C C') (g g' : Work.Kunneth.chHom D D')
    (Hf : Homotopy f f') (Hg : Homotopy g g') :
    Nonempty (Homotopy (Work.Kunneth.tpMap C C' D D' f g)
      (Work.Kunneth.tpMap C C' D D' f' g')) :=
  tpMap_homotopy C C' D D' f f' g g' Hf Hg

end Work.Kunneth
