import Submission.Work.SSGRoute.E1aClean.BaseChangeResGalOIncl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `resH1_fixing'`: the `H¹`-restriction with its coefficient instances as explicit arguments

§2k's cure (a).  `AbsoluteKummer.H1` takes four instance arguments —
`[TopologicalSpace G] [Group G] [AddCommGroup M] [DistribMulAction G M]` — and
`PT.H2Fin.resH1` takes `[Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]` before its explicit
`N`, `P` and then `[AddCommGroup P] [DistribMulAction Γ P]` (signatures read off with `#check`).
This wrapper surfaces the two coefficient arguments so that the `H¹` produced by
`ExtChain.e1cMap` (which carries `homCoind.instDistribMulActionAlgEquiv`) can be fed straight in. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- **The `H¹`-restriction with explicit coefficient instances.** -/
noncomputable def resH1_fixing' (L : IntermediateField k K)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (instA : AddCommGroup (Work.SSGRoute.homCoind k Ω K R))
    (instM : DistribMulAction (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)) :
    @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)
        _ _ instA instM →+
      @Work.AbsoluteKummer.H1 ↥((LOmega L).fixingSubgroup) (Work.SSGRoute.homCoind k Ω K R)
        _ _ instA (Subgroup.instDistribMulActionSubtypeMem (LOmega L).fixingSubgroup) :=
  @Work.SSGRoute.PT.H2Fin.resH1 (Ω ≃ₐ[k] Ω) _ _ _ (LOmega L).fixingSubgroup
    (Work.SSGRoute.homCoind k Ω K R) instA instM

end

end Work.SSGRoute.E1aClean
