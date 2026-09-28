import Mathlib
import Submission.Work.SSS.LESFacts

/-!
# The differential of the E¹ row complex, cycle-free

`Work.SSS.E1Complex ξ t` is `ChainComplex.of (E1 ξ · t) (d1 ξ · t)`.  The identification of its
differential in degree `j` with `d1 ξ j t` is `ChainComplex.of_d`, but the file
`Submission/Work/SSS/packetOfFiltration.lean` which records this as `Work.SSS.E1Complex_d` sits
downstream of `Work.SSS.fibreCol` and hence of the present development; to keep the first-page
computation `FirstPageCF.*` free of that import cycle we restate it here under a fresh name.

`E1Complex` and `d1` are defined in `Submission/Work/SSS/Filtration.lean`, which is imported
through `Submission.Work.SSS.LESFacts`, so nothing below depends on `packetOfFiltration`.
-/

set_option autoImplicit false

namespace Work.SSS.FirstPageCF

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- Copy of `Work.SSS.E1Complex_d`, proved against the cycle-free import `LESFacts`: the
differential `E¹_{j+1,t} → E¹_{j,t}` of the row complex is `d¹`. -/
theorem E1Complex_d (ξ : Filtration C) (t j : ℕ) :
    (E1Complex ξ t).d (j + 1) j = d1 ξ j t :=
  ChainComplex.of_d (fun s => E1 ξ s t) (fun s => d1 ξ s t) j

end

end Work.SSS.FirstPageCF
