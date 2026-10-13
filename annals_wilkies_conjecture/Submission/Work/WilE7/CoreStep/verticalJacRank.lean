import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE5.Basic
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.CoreStep.VertIncl
import Submission.Work.WilE7.CoreStep.finrankKerComp
import Submission.Work.WilE7.CoreStep.submatrixMulVecComp

namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- **Vertical Jacobian rank.**  For an absolute `Good` stratum `T` of `ℝ^{0+(n+(m+1))}` and any
`z ∈ T.X.set`, the rank of the *vertical* block of the Jacobian of the defining equations of `T`
(the `T.j × (m+1)` matrix of the partial derivatives in the last `m+1` coordinates) equals
`(m+1) - ((N - T.j) - projRank T z)` with `N = n + m + 1`.

This is a pure dimension count.  Write `A` for the full `T.j × N` Jacobian matrix at `z` and
`Φ := M.mulVecLin` for the vertical block `M = A.submatrix id (fun l ↦ natAdd 0 (natAdd n l))`.
Then

* `Φ = (jac T z).comp (vertIncl n m)`, where `vertIncl n m : ℝ^{m+1} ↪ ℝ^N` inserts the vertical
  coordinates (`Work.WilE7.CoreStep.submatrixMulVecComp`);
* `(vertIncl n m).range = (basePrLin n (m+1)).ker` (`Work.WilE7.CoreStep.vertIncl_range`), so the
  general rank–nullity identity `Work.WilE7.CoreStep.finrankKerComp` gives
  `finrank (ker Φ) = finrank (ker (jac T z)) - finrank ((ker (jac T z)).map (basePrLin n (m+1)))`
  `= (N - T.j) - projRank T z`, the second term being `projRank T z` by definition and the first
  `N - T.j` by rank–nullity, `jac T z` being surjective on a `Good` stratum
  (`Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux`);
* rank–nullity for `Φ` itself then turns this into the claimed formula for `M.rank`. -/
theorem verticalJacRank {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) :
    ∀ z ∈ T.X.set, (Matrix.of fun (a : Fin T.j) (l : Fin (m + 1)) =>
        WilkiesDesign.E.eaEval T.X.c
          (WilkiesDesign.E.eaD T.X.c (Fin.natAdd 0 (Fin.natAdd n l)) (T.h a)) z).rank
      = (m + 1) - ((n + m + 1 - T.j) - Work.WilE7.MainDesign.projRank T z) := by
  intro z hz
  -- the full Jacobian matrix of the defining equations of `T` at `z`
  set A : Matrix (Fin T.j) (Fin (0 + (n + (m + 1)))) ℝ :=
    Matrix.of fun (a : Fin T.j) (i : Fin (0 + (n + (m + 1)))) =>
      eaEval T.X.c (eaD T.X.c i (T.h a)) z with hA
  have hsurj : (jac T z).range = ⊤ :=
    Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux T hT hz
  have hdimker : Module.finrank ℝ (jac T z).ker = (0 + (n + (m + 1))) - T.j :=
    Work.WilE7.finrank_ker_of_surjective (jac T z) hsurj
  -- the general rank–nullity identity, with `ι = vertIncl`, `π = basePrLin`, `Ψ = jac T z`
  have hkey : Module.finrank ℝ ((jac T z).comp (vertIncl n m)).ker
      = Module.finrank ℝ (jac T z).ker
        - Module.finrank ℝ ((jac T z).ker.map (basePrLin n (m + 1))) :=
    finrankKerComp (vertIncl n m) (vertIncl_injective n m) (basePrLin n (m + 1)) (jac T z)
      (vertIncl_range n m)
  -- the vertical block is `jac T z` precomposed with `vertIncl`
  have hcomp : (A.submatrix id (fun l : Fin (m + 1) => Fin.natAdd 0 (Fin.natAdd n l))).mulVecLin
      = (jac T z).comp (vertIncl n m) := by
    rw [submatrixMulVecComp]
    rfl
  have hmat : (Matrix.of fun (a : Fin T.j) (l : Fin (m + 1)) =>
        eaEval T.X.c (eaD T.X.c (Fin.natAdd 0 (Fin.natAdd n l)) (T.h a)) z)
      = A.submatrix id (fun l : Fin (m + 1) => Fin.natAdd 0 (Fin.natAdd n l)) := rfl
  rw [hmat]
  show Module.finrank ℝ (LinearMap.range
      ((A.submatrix id (fun l : Fin (m + 1) => Fin.natAdd 0 (Fin.natAdd n l))).mulVecLin))
    = (m + 1) - ((n + m + 1 - T.j) - projRank T z)
  rw [hcomp]
  -- rank–nullity for the vertical Jacobian, with the kernel identified above
  have hnull := LinearMap.finrank_range_add_finrank_ker ((jac T z).comp (vertIncl n m))
  rw [Module.finrank_fin_fun, hkey, hdimker] at hnull
  have hpr : projRank T z
      = Module.finrank ℝ ((jac T z).ker.map (basePrLin n (m + 1))) := rfl
  rw [← hpr] at hnull
  omega

end Work.WilE7.CoreStep
