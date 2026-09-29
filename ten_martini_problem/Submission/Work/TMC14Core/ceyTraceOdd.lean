import Mathlib
import Submission.Work.TMC14Core.WeylCount
import Submission.Work.TMC14Core.AdjTrace
import Submission.Work.TMC14Core.TraceRule
import Submission.Work.TMC14Core.WordNormalForm
import Submission.Work.TMC14Core.BlochMatEq
import Submission.Work.TMC14Core.InterleaveWordNorm
import Submission.Work.TMC14Core.InvSumF

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- For `q = 2m+1` odd and `p` coprime to `q`, there is a unitary `W` with
`‖tr(adj(z·1 - blochMat) · W)‖ = q |λ|^m`. -/
theorem ceyTraceOdd (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ) (z : ℂ) :
    ∃ W : Matrix (Fin q) (Fin q) ℂ, W ∈ Matrix.unitaryGroup (Fin q) ℂ ∧
      ‖Matrix.trace (Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMat p q lam θ k) * W)‖
        = (q : ℝ) * |lam| ^ m := by
  have hq : 0 < q := by omega
  have h1 : (om p q) ^ (2*m+1) = 1 := by rw [← hm]; exact om_pow_q' p q
  have h2 : ∀ j : ℕ, 0 < j → j ≤ 2*m → (om p q) ^ j ≠ 1 := by
    intro j hj hjq h
    have hd := (om_pow_eq_one_iff p q hpq hq j).mp h
    have := Nat.le_of_dvd hj hd
    omega
  refine ceyTraceOdd_cond p q m hm hpq lam θ k z
    (fun n f => WordNormalForm p q θ k n f)
    (fun a b c e h => TraceRule p q θ k hq hpq a b c e m h)
    (fun f hf => ?_)
    (InvSumF (om p q) m h1 h2)
    (fun B W h z => AdjTrace q B W h z)
    (BlochMatEq p q lam θ k)
  rw [InterleaveWordNorm p q θ k (2*m) f hf.1]
  have hcard := interleave_card m f hf.1
  have hV : (Finset.univ.filter (fun i : Fin (2*m) => f i = (false,true))).card = m := by omega
  rw [hV, hf.2]

end Work.TMC14Core
