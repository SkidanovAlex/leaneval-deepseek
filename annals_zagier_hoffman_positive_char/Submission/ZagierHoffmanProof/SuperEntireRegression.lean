import Mathlib.Algebra.Field.ZMod
import Submission.ZagierHoffmanProof.SuperEntireApp
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks for `ε`

Concrete instances of `SuperEntire` over `F₂` and `F₃`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq
attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

noncomputable section

/-- The zero series is super-entire. -/
example : SuperEntire (0 : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) :=
  SuperEntire.zero

/-- Constants are super-entire (in both characteristics). -/
example : SuperEntire (PowerSeries.C (1 : RatFunc.CompletionAtInfty (ZMod 3))) :=
  SuperEntire.C _

/-- Sums and products of super-entire series are super-entire. -/
example (f g : PowerSeries (RatFunc.CompletionAtInfty (ZMod 2)))
    (hf : SuperEntire f) (hg : SuperEntire g) : SuperEntire (f * g + f ^ 3) :=
  (hf.mul hg).add (hf.pow 3)

/-- The Frobenius twist preserves `ε`. -/
example (f : PowerSeries (RatFunc.CompletionAtInfty (ZMod 3))) (hf : SuperEntire f) :
    SuperEntire (frobTwist (R := RatFunc.CompletionAtInfty (ZMod 3)) (p := 3) 2 f) :=
  hf.frobTwist 2

/-- **The Carlitz exponential belongs to `ε`** (over `F₂` and `F₃`). -/
example : SuperEntire (seriesToK (ZMod 2) (carlitzExp (ZMod 2))) :=
  superEntire_carlitzExp (ZMod 2)

example : SuperEntire (seriesToK (ZMod 3) (carlitzExp (ZMod 3))) :=
  superEntire_carlitzExp (ZMod 3)

/-- `ε` is contained in the Tate algebra. -/
example : SeriesBounded (seriesToK (ZMod 2) (carlitzExp (ZMod 2))) :=
  (superEntire_carlitzExp (ZMod 2)).bounded

end

end ZagierHoffmanPositiveChar
