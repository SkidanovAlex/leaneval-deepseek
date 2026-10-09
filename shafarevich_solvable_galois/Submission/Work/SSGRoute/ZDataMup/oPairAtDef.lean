import Submission.Work.SSGRoute.ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Kummer pairing at a finite place, packaged with its instance

`oPairAt ζ hζ A hA a b` is the local Kummer pairing `⟨a, b⟩_A = χ_α(θ_A(β_A))` of the odd-`p`
pairing at the finite place `A` (`a`, `b` the level-`K` Kummer cochains of `α`, `β`), written as the
descended `oPairForm` on the level-`K` local groups.

This module contains **only** the definition, with the level-`K` subgroup action instance supplied by
a `letI` inside the definition body (`Work.SSGRoute.subgroupDistribMulAction`, the way
`ZDataMup/mupH1locLcHoms.lean` does it).  It exists separately so that statements about the pairing
can be elaborated without importing the (still open) statement module
`ZDataMup/twoPlaceReciprocity.lean`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The local Kummer pairing `⟨a, b⟩_A` at a finite place `A`**, with the level-`K` subgroup action
instance supplied locally. -/
noncomputable def oPairAt (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (a b : (Ω ≃ₐ[k] Ω) → ZMod p) : ZMod p :=
  letI : DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p) :=
    Work.SSGRoute.subgroupDistribMulAction k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
  oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
    (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
    (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b)

end Work.SSGRoute.ZDataMup.OddForm
