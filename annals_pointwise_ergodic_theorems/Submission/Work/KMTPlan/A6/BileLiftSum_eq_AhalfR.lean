import Mathlib
import Submission.Work.KMTPlan.A6.BileLiftDefs
import Submission.Work.KMTContract.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

/-- The physical halved average of the lifts is the halved average `AhalfR TZ` applied to the
lifts.  Both sides are the same finite sum

`N⁻¹ ∑_{N/2 < n ≤ N} bileLift ψ R u (x - n) · bileLift ψ R v (x - P(n))`,

the only difference being that `AhalfR` writes the translated arguments as `(T_ℤ ^ k) x` with
`T_ℤ` the integer shift `n ↦ n - 1`, while `bileLiftSum` writes them out as `x - k`; the two
agree by `TZ_zpow`.  -/
theorem BileLiftSum_eq_AhalfR (P : Polynomial ℤ) (ψ : ℝ → ℂ) (R N : ℕ) (Q : ℕ)
    (u v : ZMod Q → ℂ) :
    Work.KMTPlan.A6.bileLiftSum P ψ R N u v
      = Submission.PointwiseErgodicTheorems.AhalfR Submission.PointwiseErgodicTheorems.TZ
          (N : NNReal) Polynomial.X P (Work.KMTPlan.A6.bileLift ψ R u)
          (Work.KMTPlan.A6.bileLift ψ R v) := by
  funext x
  simp only [Work.KMTPlan.A6.bileLiftSum, Submission.PointwiseErgodicTheorems.AhalfR,
    Submission.PointwiseErgodicTheorems.Ahalf, Submission.PointwiseErgodicTheorems.Ablock,
    Nat.floor_natCast]
  congr 1
  · push_cast; ring
  · rw [show Finset.Ioc (N / 2) N = Finset.Icc (N / 2 + 1) N from by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have h1 : ((↑Submission.PointwiseErgodicTheorems.TZ : ℤ ≃ ℤ)
        ^ Polynomial.eval (n : ℤ) Polynomial.X) x = x - (n : ℤ) := by
      rw [Polynomial.eval_X]
      exact Submission.PointwiseErgodicTheorems.TZ_zpow _ _
    have h2 : ((↑Submission.PointwiseErgodicTheorems.TZ : ℤ ≃ ℤ)
        ^ Polynomial.eval (n : ℤ) P) x = x - Polynomial.eval (n : ℤ) P :=
      Submission.PointwiseErgodicTheorems.TZ_zpow _ _
    rw [h1, h2]

end Work.KMTPlan.A6
