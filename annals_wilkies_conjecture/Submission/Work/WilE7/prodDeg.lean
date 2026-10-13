import Mathlib
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.sumProduct

namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-- The product of two restricted semi-Pfaffian sets has degree bounded by `2 (1 + d + d')²`,
where `d`, `d'` are the degrees of the two factors.  The bound is the conjunction of the two
elementary estimates obtained in `ProdDefs`:

* `Basic.prod_deg_le` : merging two branches does not raise the degree, so the degree of the
  product DNF is at most the sum of the two degrees over the product list;
* `redBasics_length_le` / `redBasics_deg_le` : after collapsing a trivial branch, a factor of
  degree `d` contributes at most `max 1 d` branches of total degree at most `d`.

`sumProduct` turns the sum over the product list into `n'·S + n·S'`, and `deg_bound_arith`
bounds that by `2 (1 + (d + d'))²`. -/
theorem prodDeg {k k' : ℕ} (X : WilkiesDesign.E.SemiPf k) (X' : WilkiesDesign.E.SemiPf k') :
    (Work.WilE7.SemiPf.prod X X').deg ≤ 2 * (1 + (X.deg + X'.deg)) ^ 2 := by
  have hsum : (SemiPf.prod X X').deg
      ≤ (((redBasics X).product (redBasics X')).map
          (fun p : Basic k X.r × Basic k' X'.r => p.1.deg + p.2.deg)).sum := by
    simp only [SemiPf.deg, SemiPf.prod_basics, SemiPf.prod_r]
    rw [List.map_map]
    refine sum_map_le_of_pointwise _ _ _ ?_
    rintro ⟨B, B'⟩ -
    exact Basic.prod_deg_le B B'
  rw [sumProduct] at hsum
  exact le_trans hsum (deg_bound_arith X.deg X'.deg (redBasics X).length (redBasics X').length
    ((redBasics X).map Basic.deg).sum ((redBasics X').map Basic.deg).sum
    (redBasics_length_le X) (redBasics_length_le X') (redBasics_deg_le X) (redBasics_deg_le X'))

end Work.WilE7
