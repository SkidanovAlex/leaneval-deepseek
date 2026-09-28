import Mathlib
import Submission.Work.ThomBordism.man8Finiteness
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.nondegenerate_midForm_of_good

set_option synthInstance.maxHeartbeats 400000

/-!
# Middle-degree Poincaré duality for a `Man8`

The middle intersection form of a closed oriented `8`-manifold of the `Man8` model (a compact `T2`
`C^∞` `8`-manifold together with a *locally generating* fundamental class `c`) is non-degenerate:

`Work.ThomBordism.man8MidFormNondegenerate`.

This is the closed Poincaré duality input of the closed pieces of a null-bordism, needed for the
disjoint-union reduction of `Work.ThomBordism.bdryMidFormNondegenerate`.  The proof is the
assembly:

* the local generation `Man8.c_fund` upgraded to `Good 8 c Set.univ`
  (`Work.ThomBordism.goodUniv_of_localGen`), i.e. Poincaré duality for the whole closed manifold;
* the homological finiteness `Work.ThomBordism.compactHomologyFinite` (a compact `C^∞` manifold has
  finitely generated singular homology, from a finite good cover);
* `Work.ThomBordism.nondegenerate_midForm_of_good` (the `ℤ → ℚ` base-change argument: the radical
  of the middle intersection form consists of torsion classes, and torsion dies in `⊗[ℤ] ℚ`).
-/

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism

noncomputable section

/-- **Middle-degree Poincaré duality for a `Man8`**: the middle intersection form of a closed
oriented `8`-manifold is non-degenerate. -/
theorem man8MidFormNondegenerate (V : Man8) :
    Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) V.toClosedOriented) := by
  have hgood : Work.Cohomology.Good 8 (V.c) Set.univ isOpen_univ :=
    goodUniv_of_localGen (N := 8) V.c (fun x => V.c_fund x) (by norm_num)
  have hfg : ∀ k, Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (Man8.X V)).homology k) :=
    fun k => compactHomologyFinite (n := 8) (k := k) V.pt
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (4 + 4))) ↑(Man8.X V) := Man8.chartedSpace V
  exact nondegenerate_midForm_of_good (n := 4) (by norm_num) hgood hfg

end

end Work.ThomBordism
