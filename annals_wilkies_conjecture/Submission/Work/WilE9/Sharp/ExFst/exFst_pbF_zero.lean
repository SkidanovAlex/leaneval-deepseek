import Mathlib
import Submission.Work.WilE9.Sharp.ExFst.Defs
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.eaEval_pbRaise

namespace Work.WilE9.Sharp.ExFst

open Work.WilE9 WilkiesDesign WilkiesDesign.E

theorem exFst_pbF_zero {n m : ℕ} (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    {x : Fin n → ℝ} {w : Fin (n + (1 + m)) → ℝ} (hw : w ∈ E.X.set)
    (sval σ : ℝ)
    (hbase : Work.WilE9.Sharp.stratProj w =
      Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi sval)) :
    ∀ j : Fin (Work.WilE9.Sharp.qpb n m),
      WilkiesDesign.E.eaEval (Work.WilE9.Sharp.pbChain E.X.c)
        (Work.WilE9.Sharp.pbF n m E.X.r E.h j)
        (Work.WilE9.Sharp.exSub (Work.WilE9.Sharp.exPt w x sval σ)) = 0 := by
  intro j
  -- The coordinates of the reconstructed point `exSub (exPt w x sval σ)`.  Its `w`-coordinates
  -- are `psig (x i)` and its `y`-coordinates are `psi (x i)` (by `hbase`), so its `x`-coordinates
  -- are the quotients `psi (x i) / psig (x i)`; similarly for `s`, `τ`, `u`.
  have hY : ∀ i : Fin n,
      exSub (exPt w x sval σ) (pbY n m i) = WilkiesDesign.E.psi (x i) := by
    intro i; rw [exSub_pbY, exPt_exY, wY_of_hbase hbase i]
  have hW : ∀ i : Fin n,
      exSub (exPt w x sval σ) (pbW n m i) = Work.WilE9.psig (x i) := by
    intro i; rw [exSub_pbW, exPt_exW]
  have hX : ∀ i : Fin n,
      exSub (exPt w x sval σ) (pbX n m i)
        = WilkiesDesign.E.psi (x i) / Work.WilE9.psig (x i) := by
    intro i; rw [exSub_pbX, exPt_exY, exPt_exW, wY_of_hbase hbase i]
  have hT : exSub (exPt w x sval σ) (pbT n m) = WilkiesDesign.E.psi sval := by
    rw [exSub_pbT, exPt_exT, wTau_of_hbase hbase]
  have hU : exSub (exPt w x sval σ) (pbU n m) = Work.WilE9.psig sval := by
    rw [exSub_pbU, exPt_exU]
  have hS : exSub (exPt w x sval σ) (pbS n m)
      = WilkiesDesign.E.psi sval / Work.WilE9.psig sval := by
    rw [exSub_pbS, exPt_exT, exPt_exU, wTau_of_hbase hbase]
  -- Reading the stratum coordinates of the reconstructed point returns `w`.
  have hstr : pbStrat (exSub (exPt w x sval σ)) = w := by
    rw [pbStrat_exSub, exStrat_exPt]
  simp only [Work.WilE9.Sharp.pbF]
  split_ifs with h0 h1 h2 h3
  · -- the equation `τ - s * u`
    simp only [WilkiesDesign.E.eaEval, Sum.elim_inl, MvPolynomial.eval_X, map_sub, map_mul]
    rw [hT, hS, hU, div_mul_cancel₀ _ (ne_of_gt (Work.WilE9.Psi.psig_pos sval))]
    ring
  · -- the equations `y i - x i * w i`
    simp only [WilkiesDesign.E.eaEval, Sum.elim_inl, MvPolynomial.eval_X, map_sub, map_mul]
    rw [hY, hX, hW, div_mul_cancel₀ _ (ne_of_gt (Work.WilE9.Psi.psig_pos _))]
    ring
  · -- the equations `y i ^ 2 + w i ^ 2 - 1`
    simp only [WilkiesDesign.E.eaEval, Sum.elim_inl, MvPolynomial.eval_X,
      map_sub, map_add, map_pow, map_one]
    rw [hY, hW, Work.WilE9.Psi.psi_sq_add_psig_sq]
    ring
  · -- the equation `τ ^ 2 + u ^ 2 - 1`
    simp only [WilkiesDesign.E.eaEval, Sum.elim_inl, MvPolynomial.eval_X,
      map_sub, map_add, map_pow, map_one]
    rw [hT, hU, Work.WilE9.Psi.psi_sq_add_psig_sq]
    ring
  · -- the stratum's own equation `h a`, which vanishes on `w ∈ E.X.set` by `E.Good`
    rw [eaEval_pbRaise, hstr]
    exact (hgood w hw).1 _

end Work.WilE9.Sharp.ExFst
