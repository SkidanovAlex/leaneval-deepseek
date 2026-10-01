import Mathlib
import Submission.Work.LinnikBurgess.cubicPhase_aux

namespace Work.LinnikBurgess

/-- **The inner sum of the stationary-phase step.**  For a critical point `a` of
`linCoeff β γ δ` modulo `p` (i.e. `p ∣ linCoeff β γ δ a`), the partial sum of the
cubic phase over the arithmetic progression `a, a + p, a + 2p, …` factorises as the
value of the phase at `a` times the complete Gauss sum of the reduced phase
`shiftPhase p β γ δ R a` over `ZMod (p ^ (K - 2))`.

This is the sum over the `u`-variable in the proof of `cubicPhase_rootSum`: the
stationary-phase identity `H(a + p u) = H(a) + p² · shiftPhase(a)(u)` turns each
term into a constant factor times the corresponding term of the reduced sum. -/
theorem cubicPhase_innerSum (p K : ℕ) [Fact p.Prime] (hK : 2 ≤ K) (β γ δ : ℤ)
    (R : Polynomial ℤ) (a : ℕ) (ha : a < p) (hroot : (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ a) :
    (∑ u ∈ Finset.range (p ^ (K - 2)),
        Commons.NumberTheory.GaussSum.E (p ^ K)
          (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) (Work.LinnikBurgess.CubicPhase p β γ δ R)))
      = Commons.NumberTheory.GaussSum.E (p ^ K)
            (Polynomial.eval (a : ℤ) (Work.LinnikBurgess.CubicPhase p β γ δ R))
          * Commons.NumberTheory.GaussSum.Tsum (p ^ (K - 2))
              (Work.LinnikBurgess.shiftPhase p β γ δ R a) := by
  rw [Commons.NumberTheory.GaussSum.Tsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Work.LinnikBurgess.shiftPhase_CubicPhase_eval p β γ δ R a hroot (u : ℤ),
    Commons.NumberTheory.GaussSum.E_add,
    Commons.NumberTheory.GaussSum.E_sq_mul p K hK]

end Work.LinnikBurgess
