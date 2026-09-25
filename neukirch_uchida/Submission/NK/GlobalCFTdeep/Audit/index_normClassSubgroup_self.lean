import Mathlib
import Submission.NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self
import Submission.NK.GlobalCFTdeep.Audit.cohomologicalFieldAxiom_self

namespace NK.GlobalCFTdeep.Audit

/-- For the trivial extension `K / K` the norm subgroup `N_{K/K} C_K` is all of `C_K`, so its
index is `1 = [K : K]`.  This is the `K = L` case of the field axiom, which is proved
unconditionally in `NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self`. -/
theorem index_normClassSubgroup_self {K : Type} [Field K] [NumberField K] :
    (NK.GlobalCFT.Idele.normClassSubgroup K K).index = 1 := by
  rw [(NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self K).index_eq, Module.finrank_self]

end NK.GlobalCFTdeep.Audit
