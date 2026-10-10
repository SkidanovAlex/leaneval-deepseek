import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.GlobalCFTdeep.CoCore.FundamentalClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Audit

/-- For the trivial extension `K / K` the norm subgroup `N_{K/K} C_K` is all of `C_K`, so its
index is `1 = [K : K]`.  This is the `K = L` case of the field axiom, which is proved
unconditionally in `NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self`. -/
theorem index_normClassSubgroup_self {K : Type} [Field K] [NumberField K] :
    (NK.GlobalCFT.Idele.normClassSubgroup K K).index = 1 := by
  rw [(NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self K).index_eq, Module.finrank_self]

end NK.GlobalCFTdeep.Audit
