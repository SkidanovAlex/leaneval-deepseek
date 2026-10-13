import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE7.pad_eval
import Submission.Work.WilE9G.Lagrange.eaD_pad
import Submission.Work.WilE9G.Lagrange.lagPoint_apply
import Submission.Work.WilE9G.Lagrange.lagEqs_eval
import Submission.Work.WilE3.API.eaD_commute
import Submission.Work.WilE9G.Lagrange.LagBlkEnt

namespace Work.WilE9G.Lagrange

open LagBlk

theorem lagBlock_lagPoint {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Work.WilE9G.Lagrange.lagBlock S Phi c (Work.WilE9G.lagPoint z mu mu0)
      = (Work.WilE9G.Lagrange.lagJacTrue S Phi c z mu mu0).submatrix
          (Work.WilE9G.Lagrange.lagEquiv m S.j) (Work.WilE9G.Lagrange.lagEquiv m S.j) := by
  ext a l
  rw [Matrix.submatrix_apply, lagBlock_apply]
  rcases lt_or_ge a.val (1 + m) with ha | ha
  · rcases lt_or_ge l.val (1 + m) with hl | hl
    · rw [pEntLyt S Phi c z mu mu0 a l ha hl, pJac_Lyt S Phi c z mu mu0 a l ha hl]
    · rcases lt_or_ge l.val (1 + m + S.j) with hl2 | hl2
      · rw [pEntLmu S Phi c z mu mu0 a l ha hl hl2, pJac_Lmu S Phi c z mu mu0 a l ha hl hl2]
      · have hle : l.val = 1 + m + S.j := by omega
        rw [pEntLmu0 S Phi c z mu mu0 a l ha hle, pJac_Lmu0 S Phi c z mu mu0 a l ha hle]
  · rcases lt_or_ge a.val (1 + m + S.j) with ha2 | ha2
    · rcases lt_or_ge l.val (1 + m) with hl | hl
      · rw [pEntHyt S Phi c z mu mu0 a l ha ha2 hl, pJac_Hyt S Phi c z mu mu0 a l ha ha2 hl]
      · rcases lt_or_ge l.val (1 + m + S.j) with hl2 | hl2
        · rw [pEntHmu S Phi c z mu mu0 a l ha ha2 hl hl2,
              pJac_Hmu S Phi c z mu mu0 a l ha ha2 hl hl2]
        · have hle : l.val = 1 + m + S.j := by omega
          rw [pEntHmu0 S Phi c z mu mu0 a l ha ha2 hle,
              pJac_Hmu0 S Phi c z mu mu0 a l ha ha2 hle]
    · have hle : a.val = 1 + m + S.j := by omega
      rcases lt_or_ge l.val (1 + m) with hl | hl
      · rw [pEntNyt S Phi c z mu mu0 a l hle hl, pJac_Nyt S Phi c z mu mu0 a l hle hl]
      · rcases lt_or_ge l.val (1 + m + S.j) with hl2 | hl2
        · rw [pEntNmu S Phi c z mu mu0 a l hle hl hl2, pJac_Nmu S Phi c z mu mu0 a l hle hl hl2]
        · have hle2 : l.val = 1 + m + S.j := by omega
          rw [pEntNmu0 S Phi c z mu mu0 a l hle hle2, pJac_Nmu0 S Phi c z mu mu0 a l hle hle2]

end Work.WilE9G.Lagrange
