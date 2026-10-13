import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Operators.detOp_extH_eq_zero

namespace Work.Strat

/-- Adjoining the base-coordinate shifts `x_i - z_i` (together with the base directions as pivots)
to a system `h` whose pivots `ι` all lie in fibre directions does not change the operator
`detOp c · · (yDir p l) f`.

This is the statement of `Work.WilE5.Operators.det_extH_eq`, restated in the `Work.Strat`
namespace for downstream use. -/
theorem detOp_extH_eq {p q r j : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r) (ι : Fin j → Fin (p + q))
    (hι : ∀ a, ∃ l : Fin q, ι a = Work.WilE5.yDir p l)
    (z : Fin (p + q) → ℝ) (f : WilkiesDesign.E.EAPoly (p + q) r) (l : Fin q) :
    WilkiesDesign.E.detOp c (Work.WilE5.extH h z) (Work.WilE5.extι ι) (Work.WilE5.yDir p l) f =
      WilkiesDesign.E.detOp c h ι (Work.WilE5.yDir p l) f :=
  Work.WilE5.Operators.det_extH_eq c h ι hι z f l

end Work.Strat
