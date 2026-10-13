import Mathlib
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.Strat.detOpSt_eq_zero_of_row_combination

namespace Work.WilE7.FibreCalc

theorem critSet_mem_of_rowRelation {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (l : Fin q)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) (lam : Fin S.j → ℝ)
    (hrow : ∀ d : Fin q,
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c (Fin.natAdd p d)
        (MvPolynomial.X (Sum.inl (Fin.natAdd p l)))) z
      = ∑ a : Fin S.j, lam a * WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c (Fin.natAdd p d) (S.h a)) z) :
    z ∈ (Work.WilE7.critSet S l).set := by
  rw [Work.WilE7.critSet_set]
  refine ⟨hz, fun σ => ?_⟩
  have h := Work.Strat.eaEval_detOp_eq_zero_of_row_relation (p := p) (q := q) (r := S.X.r)
    (j := S.j) S.X.c S.h (fun b => σ (Fin.castSucc b))
    (MvPolynomial.X (Sum.inl (Fin.natAdd p l))) z (σ (Fin.last S.j)) lam (fun d => hrow d)
  simpa only [Work.WilE7.critMinor, Work.WilE7.fibDir, Work.WilE5.yDir] using h

end Work.WilE7.FibreCalc
