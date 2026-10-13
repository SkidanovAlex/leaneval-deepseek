import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.CoreStep.stratReindex_exists
import Submission.Work.WilE7.CoreStep.ProjTopTransfer
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.CoreStep.StratReindexDefs
import Submission.Work.WilE7.coreLT_succ.SwapEquiv0
import Submission.Work.WilE7.coreLT_succ.projTop_absPt_reindex
import Submission.Work.WilE7.coreLT_succ.finrank_map_reindex

/-!
  `Work.WilE7.coreLT_succ.stratReindex_projTop`: the frame change that turns a `Good` absolute
  stratum of the `((n+1)+m)`-split (base `ℝ^{n+1}`, vertical coordinate the **first** fibre
  coordinate `n`) into one of the `(n, m+1)`-split used everywhere in the `CoreLT_succ` assembly
  (base `ℝ^n`, vertical coordinate the **last** fibre coordinate `n+m`), without changing its
  data.

  The witness is `Work.CoreStep.Stratum.reindex (swapEquiv0 n m) T`, the coordinate reindexing of
  `T` along the (lifted) transposition of the two vertical coordinates:
  `Work.CoreStep.swapEquiv n m` fixed the base coordinates `0, …, n-1` and exchanged `n` and
  `n+m`, and `swapEquiv0` lifts it through the `0 + ·` bookkeeping of `Stratum 0 ·`.

  * `j`, `X.r`, `deg` are unchanged because reindexing only renames coordinates
    (`Stratum.reindex_j`, `reindex_r`, `reindex_deg`);
  * `Good` is transported by `stratReindex_good_fwd` / `stratReindex_good_bwd` (`p = 0`, so the
    fibre condition of `Good` is vacuous);
  * the `(n+1)`-projection `projFirst (n+1) m '' absSet T` becomes the `(n, m+1)`-projection
    `projTop n m '' absSet T'` (`projTop_absPt_reindex`);
  * the tangent-space ranks are preserved: the rank of the tangent space of `T'` under
    `projTopLin n m ∘ absPtLin (n+(m+1))` is that of `T` under `basePrLin (n+1) m`
    (`finrank_map_reindex`, applied with the identity `projTopLin_absPtLin_swapEquiv0`), which is
    `(n+1)+m - T.j = n+(m+1) - T'.j` by the hypothesis `hrank`.
-/

namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E

theorem stratReindex_projTop {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 ((n + 1) + m))
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = (n + 1) + m - T.j) :
    ∃ T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)),
      T'.j = T.j ∧ T'.X.r = T.X.r ∧ T'.deg = T.deg ∧
      (WilkiesDesign.E.Stratum.Good T' ↔ WilkiesDesign.E.Stratum.Good T) ∧
      Work.WilE7.CoreStep.projTop n m '' Work.WilE7.MainDesign.absSet T' =
        WilkiesDesign.E.projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet T ∧
      (∀ z' ∈ T'.X.set, Module.finrank ℝ
        ((LinearMap.ker (Work.WilE7.MainDesign.jac T' z')).map
          ((Work.WilE7.CoreStep.projTopLin n m).comp (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))))
        = n + (m + 1) - T'.j) := by
  refine ⟨Work.CoreStep.Stratum.reindex (swapEquiv0 n m) T, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact Work.CoreStep.Stratum.reindex_deg (swapEquiv0 n m) T
  · exact ⟨Work.CoreStep.stratReindex_good_fwd (swapEquiv0 n m) T,
      Work.CoreStep.stratReindex_good_bwd (swapEquiv0 n m) T⟩
  · exact projTop_absPt_reindex (n := n) (m := m) T.X
  · intro z' hz'
    have hz : (fun i : Fin (0 + ((n + 1) + m)) => z' ((swapEquiv0 n m) i)) ∈ T.X.set :=
      (Work.CoreStep.Stratum.reindex_mem (swapEquiv0 n m) T z').mp hz'
    have h1 := finrank_map_reindex (swapEquiv0 n m) T z'
      ((Work.WilE7.CoreStep.projTopLin n m).comp (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))
      (Work.WilE7.MainDesign.basePrLin (n + 1) m)
      (fun v => projTopLin_absPtLin_swapEquiv0 n m v)
    rw [h1]
    have h2 := hrank (fun i : Fin (0 + ((n + 1) + m)) => z' ((swapEquiv0 n m) i)) hz
    dsimp only [Work.WilE7.MainDesign.projRank] at h2
    rw [h2]
    rw [show (Work.CoreStep.Stratum.reindex (swapEquiv0 n m) T).j = T.j from rfl]
    omega

end Work.WilE7.coreLT_succ
