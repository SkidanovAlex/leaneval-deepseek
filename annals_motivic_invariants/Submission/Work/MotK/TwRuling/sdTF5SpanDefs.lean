import Mathlib
import Submission.Work.MotK.TwRuling.TwFivetenDefs
import Submission.Work.MotK.TwRuling.SdWNdeg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vocabulary for `Work.MotK.TwRuling.sdTF5Span`

Let `R` be a field and `E` a Weierstrass curve over `R`.  Write `Om := E.FunctionField` and
`sdBas E = ![1, x, y, x², xy]` (`x = genX E`, `y = genY E`), the basis of `L(5·O)`.

* `Q E n` is the `R`-span of the `n`-fold products of elements of `sdBas E`.
  Thus `Q E 5` is the submodule of the target statement and `Q E 2` is `L(10·O)`.

This file only holds the definition; the lemmas about it are proved in
`Submission.Work.MotK.TwRuling.sdTF5Span`.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling.Five

noncomputable section

variable {R : Type} [Field R]

/-- The `R`-span of the `n`-fold products of elements of the basis `sdBas E = ![1, x, y, x², xy]`. -/
def Q (E : WeierstrassCurve R) (n : ℕ) : Submodule R (Affine.FunctionField E) :=
  Submodule.span R (Set.range (fun q : Fin n → Fin 5 => ∏ i, sdBas E (q i)))

end

end Work.MotK.TwRuling.Five
