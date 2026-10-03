import Mathlib
import Submission.Work.Peluse.SwapC.concatStepProved

namespace Work.Peluse.SwapC

/-- **KKL Lemma 6.1 (one concatenation step)**, verbatim from
`Submission/Work/Peluse/P2P3_STATEMENTS.lean.txt`.  The raw slot `qH i[M]` is concatenated across
two independent indices `i₀, i₁`, while all the other slots are doubled:
from `δ ≤ avg_i pbox (s+1) (qH i :: q₁ i) (0 :: q₂ i)` conclude
`C·δ^e ≤ avg_{i₀,i₁} pbox (2s+1) (q₁i₀ ++ q₁i₁ ++ [qH i₁]) (q₂i₀ ++ q₂i₁ ++ [qH i₀])`.

This node is discharged by the sibling lane's development
`Submission/Work/Peluse/SwapC/concatStepProved.lean` (namespace `Work.Peluse.SwapC`, name
`Work.Peluse.SwapC.concatStepProved`), which proves the same statement: the route is KKL §6 —
`pbox_peel` at the raw slot `0`, the α-form `pboxSum_asym_eq`, the gauge Cauchy–Schwarz step
`gauge_cs`, the multilinear Gowers–Cauchy–Schwarz `mCubeSum_norm_le` (`Work.Peluse.Concat.gowersCS`
in the flat form), a second Cauchy–Schwarz in the raw-slot variables and the peel read backwards.
All losses are powers of `δ` (the constants may be astronomically bad). -/
theorem concatStep : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, 1 ≤ e ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
      (M N : ℕ) (x₀ : ℤ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ M → (∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I => Work.Peluse.LadderP.Swap.pbox (s + 1)
              (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i)) M (Work.Peluse.symIcc N) f) →
      C * δ ^ e ≤ Work.Peluse.LadderP.Swap.avg (fun p : I × I =>
        Work.Peluse.LadderP.Swap.pbox (s + s + 1)
          (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
          (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (Work.Peluse.symIcc N) f) :=
  Work.Peluse.SwapC.concatStepProved

end Work.Peluse.SwapC
