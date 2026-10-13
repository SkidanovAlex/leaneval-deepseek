import Mathlib
import Submission.Work.CoreStep.StratReindexDefs
import Submission.Work.WilE7.MainDesignDefs

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- **Reindexing transports the Jacobian linear map.**  For a stratum `S` in `ℝ^{0+N}`, the
coordinate equivalence `e : Fin (0+N) ≃ Fin (0+N')`, and the pulled-back tangent vector
`w ∘ e`, the Jacobian of the reindexed stratum `Stratum.reindex e S` at `y` equals the
Jacobian of `S` at `y ∘ e` evaluated at `w`.

Entrywise this is exactly `Stratum.reindex_jac_entry`; the only remaining point is that the
defining sum over the `N'` new directions is the pull-back under `e` of the sum over the `N`
old directions (`Equiv.sum_comp`). -/
theorem stratReindex_jac_aux {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) (y : Fin (0 + N') → ℝ) (w : Fin (0 + N') → ℝ) :
    Work.WilE7.MainDesign.jac (Stratum.reindex e S) y w =
      Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i))
        (fun i : Fin (0 + N) => w (e i)) := by
  -- Replace the reindexed stratum by its (definitionally equal) explicit form, so that the
  -- index type `Fin (Stratum.reindex e S).j` reduces to `Fin S.j` without unfolding a `def`.
  change jac (⟨Work.WilE7.SemiPf.reindex e S.X, S.j,
          fun a => Work.WilE7.EAPoly.reindex e (S.h a)⟩ : Stratum 0 N') y w =
      jac S (fun i : Fin (0 + N) => y (e i))
        (fun i : Fin (0 + N) => w (e i))
  funext a
  simp only [jac, Matrix.mulVecLin_apply, Matrix.mulVec_apply, Matrix.row, dotProduct,
    Matrix.of_apply]
  -- Both sides are now explicit sums; rewrite the summands by `Stratum.reindex_jac_entry`,
  -- then reindex the summation index along `e`.
  trans ∑ i : Fin (0 + N'),
      eaEval S.X.c (eaD S.X.c (e.symm i) (S.h a)) (fun i : Fin (0 + N) => y (e i)) * w i
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact Stratum.reindex_jac_entry e S y a i
  · have hb := Equiv.sum_comp e.symm (fun i : Fin (0 + N) =>
        eaEval S.X.c (eaD S.X.c i (S.h a)) (fun i : Fin (0 + N) => y (e i)) * w (e i))
    simpa using hb

theorem stratReindex_jac {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) (y : Fin (0 + N') → ℝ) (v : Fin (0 + N) → ℝ) :
    Work.WilE7.MainDesign.jac (Work.CoreStep.Stratum.reindex e S) y
        (fun j : Fin (0 + N') => v (e.symm j)) =
      Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i)) v := by
  rw [stratReindex_jac_aux e S y (fun j : Fin (0 + N') => v (e.symm j))]
  congr 1
  funext i
  simp

end Work.CoreStep
