import Mathlib
import Submission.Work.ANALYTIC.towerFEAsetup

/-!
# Naturality of `truncDataElem` in the light profinite variable

`truncDataElem S x` is the element of `∏^bnd ℤ` over `(ℕ∪{∞}) × S` with `m`-th component
`(k,s) ↦ x_m(s)·(1 - ∏_{i ≤ m}(1 - δ_i(k)))` (i.e. `x_m(s)·[k ≤ m]`).  This file proves
`Work.ANALYTIC.TruncDataElemNat`: for `f : T ⟶ S`, pulling `truncDataElem S x` back along
`(ℕ∪{∞}) × f` gives `truncDataElem T (x|_T)`.

The two ingredients are the pointwise descriptions
`(whiskerLeft (ℕ∪{∞}) f) p = (p.1, f p.2)` (definitional for the product monoidal structure on
`LightProfinite`) and `boundedSeq_map_apply` / `truncDataElem_val` (the pointwise values of the
restriction along `boundedSeq` and of `truncDataElem`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-- **Compatibility of `truncDataElem` with restriction.**  For `f : T ⟶ S` and
`x ∈ ∏^bnd ℤ(S)`, the pullback of `truncDataElem S x` along `(ℕ∪{∞}) × f` is
`truncDataElem T (x|_T)`. -/
theorem truncDataElemNat : Work.ANALYTIC.TruncDataElemNat := by
  intro T S f x
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  -- The monoidal structure on `LightProfinite` is the product, so
  -- `whiskerLeft (ℕ∪{∞}) f p = (p.1, f p.2)`; together with the pointwise descriptions of the
  -- restriction along `boundedSeq` and of `truncDataElem` this is a `rfl`-identity.
  show (x.1 m) (f p.2) * (1 - ∏ i ∈ Finset.range (m+1), (1 - deltaFun i p.1))
      = (x.1 m) (f p.2) * (1 - ∏ i ∈ Finset.range (m+1), (1 - deltaFun i p.1))
  rfl

end Work.ANALYTIC

end
