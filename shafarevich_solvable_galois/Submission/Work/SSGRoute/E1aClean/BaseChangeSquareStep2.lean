import Submission.Work.SSGRoute.E1aClean.BaseChangeSquareStep1
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Step 2 of the wiring: the δ-rule on the generator

`PT.e1cMap_PhiE_eq_delta_gen` gives the dictionary on `PhiE`-generators as the connecting map of
the explicit dualised resolution applied to `PsiEMap`.  Step 1 replaced `z` by a generator, and the
`[Finite R.V]` hypothesis (settled in §2n) licenses this rule verbatim.  The only question this file
settles is whether `ExtChain.e1cMap` and `E1cGeneric.e1cMap` are the *same* definition (so that the
rule transfers by `rfl`) or two definitions to be bridged. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **Are the two `e1cMap`s the same definition?**  `rfl` if yes (the expected case). -/
example (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    [Finite R.V] :
    (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K) R)
      = (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) R) := rfl

/-- **Step 2**: the δ-rule for `ExtChain.e1cMap` on generators. -/
theorem e1cMap_PhiE_eq_delta (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    [Module.Finite ℤ R.V] [Finite R.V]
    (w : CategoryTheory.Abelian.Ext
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R)
        (SSGRoute.PTExt.unitsK k K) 0) :
    Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K) R
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R w)
      = (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) R).delta
          (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) R) w) :=
  Work.SSGRoute.PT.e1cMap_PhiE_eq_delta_gen (k := k) (Ω := Ω) (K := K) R w

end

end Work.SSGRoute.E1aClean
