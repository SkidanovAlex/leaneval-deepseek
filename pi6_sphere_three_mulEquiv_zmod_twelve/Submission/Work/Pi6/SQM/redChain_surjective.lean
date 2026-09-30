import Mathlib
import Submission.Work.Pi6.SQM.SqOneDefs
import Submission.Work.Pi6.SQM.redChainKernel
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Pi6/SQM/redChain_surjective`

The coefficientwise reduction of integral chains `redChain : C_m(Y;ℤ) → C_m(Y;𝔽₂)`
(`Work.Pi6.SQM.RedDefs`) is **surjective**: every mod-2 chain lifts to an integral chain.

This is the statement that `redChain` is the reduction of coefficients in the coordinates of
`eZ : C_m(Y;ℤ) ≅ (Y_m →₀ ℤ)` and `eF : C_m(Y;𝔽₂) ≅ (Y_m →₀ 𝔽₂)` (see
`Work.Pi6.SQM.RCK.mapRange_redChain`).  A lift of `z` is obtained by reading off the coordinates
of `z` and lifting each coefficient along the section `valZ : 𝔽₂ → ℤ` of the reduction
`intCast_valZ : ((valZ a : ℤ) : 𝔽₂) = a`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

/-- **The reduction of integral chains mod `2` is surjective** in every degree: a mod-2 chain is
the reduction of an integral chain, namely the one whose coefficients are the `0/1` lifts of the
coefficients of the given mod-2 chain. -/
theorem redChain_surjective (X : SSet) (n : ℕ)
    (z : ↥((X.chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))).X n)) :
    ∃ c, Work.Pi6.SQM.redChain X n c = z := by
  refine ⟨(RCK.eZLE X n).symm
    (Finsupp.mapRange valZ valZ_zero ((Iso.toLinearEquiv (eF X n)) z)), ?_⟩
  apply (Iso.toLinearEquiv (eF X n)).injective
  rw [RCK.mapRange_redChain, LinearEquiv.apply_symm_apply]
  ext σ
  simp [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, RCK.castF2_apply,
    intCast_valZ]

end

end Work.Pi6.SQM
