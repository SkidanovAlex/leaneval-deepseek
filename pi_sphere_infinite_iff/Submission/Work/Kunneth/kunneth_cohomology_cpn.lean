import Mathlib
import Submission.Work.Kunneth.kunneth_cohomology
import Submission.Work.Kunneth.cpn_kunneth_hypotheses

/-!
# Künneth with a projective space: `Hⁿ(X × ℂPᵐ)`

`Work.Kunneth.cpn_kunneth_hypotheses` supplies the three hypotheses of the cohomological Künneth
theorem for `ℂPᵐ` (its chain modules are free, its homology is free of finite rank), so the Künneth
isomorphism holds with no hypotheses on `X`:

`Hⁿ(X × ℂPᵐ; ℤ) ≅ ⨁_{p+q=n} Hᵖ(X;ℤ) ⊗ H^q(ℂPᵐ;ℤ)`.

Since `H^q(ℂPᵐ) = ℤ` for `q` even and `≤ 2m` and `0` otherwise, this is the statement that
`H^*(X × ℂPᵐ)` is **free over `H^*(X)` on `1, ζ, …, ζ^m`** (the Leray–Hirsch base case); see
`Submission/Work/Kunneth/README.md` §5.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **Künneth with a projective space**: for every simplicial set `X` and all `m`, `n`,
`Hⁿ(X × ℂPᵐ) ≅ ⨁_{p+q=n} Hᵖ(X) ⊗ H^q(ℂPᵐ)`. -/
theorem kunneth_cohomology_cpn (X : SSet) (m n : ℕ) :
    Nonempty (CategoryTheory.Iso
      ((Work.Cohomology.cochainC ℤ
        (Work.Kunneth.sProd X (TopCat.toSSet.obj (Work.Projective.CPSpace m)))).homology n)
      (Work.Kunneth.kunnethTarget X (TopCat.toSSet.obj (Work.Projective.CPSpace m)) n)) :=
  kunneth_cohomology X _ n (fun q => (cpn_kunneth_hypotheses m q).1)
    (fun q => (cpn_kunneth_hypotheses m q).2.1) (fun q => (cpn_kunneth_hypotheses m q).2.2)

end

end Work.Kunneth
