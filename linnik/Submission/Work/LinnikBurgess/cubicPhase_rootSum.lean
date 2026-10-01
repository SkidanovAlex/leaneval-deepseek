import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs
import Submission.Work.LinnikBurgess.cubicPhase_aux
import Submission.Work.LinnikBurgess.Tsum_split
import Submission.Work.LinnikBurgess.wSum_eval
import Submission.Work.LinnikBurgess.cubicPhase_innerSum

namespace Work.LinnikBurgess

open scoped BigOperators
open Commons.NumberTheory.GaussSum
open Polynomial

/-- **Root decomposition of the cubic Gauss sum.**

For a prime `p`, `K ≥ 2` and a cubic phase `H = βX + γX² + δX³ + pR`, the complete
exponential sum over `j < p^K` splits into one term per root `r < p` of `linCoeff`
modulo `p`:

`Tsum (p^K) H = p · ∑_{r : p ∣ linCoeff(r)} E(p^K)(H(r)) · Tsum (p^(K-2))(shiftPhase(r))`.

This is the `p`-adic stationary-phase (= van der Corput) step performed simultaneously
at all the critical points of `H` modulo `p`. -/
theorem cubicPhase_rootSum (p K : ℕ) [Fact p.Prime] (hK : 2 ≤ K) (β γ δ : ℤ) (R : Polynomial ℤ) :
    Commons.NumberTheory.GaussSum.Tsum (p ^ K) (Work.LinnikBurgess.CubicPhase p β γ δ R)
      = (p : ℂ) * ∑ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ r),
          Commons.NumberTheory.GaussSum.E (p ^ K)
              (Polynomial.eval (r : ℤ) (Work.LinnikBurgess.CubicPhase p β γ δ R))
            * Commons.NumberTheory.GaussSum.Tsum (p ^ (K - 2)) (Work.LinnikBurgess.shiftPhase p β γ δ R r) := by
  calc Tsum (p ^ K) (CubicPhase p β γ δ R)
      = ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (K - 2)), ∑ w ∈ Finset.range p,
          E (p ^ K) (Polynomial.eval ((a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (K - 2) * (w : ℤ)))
            (CubicPhase p β γ δ R)) := Tsum_split p K hK _
    _ = ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (K - 2)),
          E (p ^ K) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) (CubicPhase p β γ δ R))
            * (if (p : ℤ) ∣ Polynomial.eval (a : ℤ)
                  (Polynomial.derivative (CubicPhase p β γ δ R)) then (p:ℂ) else 0) := by
          apply Finset.sum_congr rfl; intro a ha
          apply Finset.sum_congr rfl; intro u hu
          exact wSum_eval p K hK _ a u
    _ = ∑ a ∈ Finset.range p,
          (if (p : ℤ) ∣ Polynomial.eval (a : ℤ)
                (Polynomial.derivative (CubicPhase p β γ δ R)) then (p:ℂ) else 0)
            * ∑ u ∈ Finset.range (p ^ (K - 2)),
                E (p ^ K) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) (CubicPhase p β γ δ R)) := by
          apply Finset.sum_congr rfl; intro a ha
          rw [← Finset.sum_mul]
          ring
    _ = ∑ a ∈ Finset.range p,
          (if (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ a then (p:ℂ) else 0)
            * ∑ u ∈ Finset.range (p ^ (K - 2)),
                E (p ^ K) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) (CubicPhase p β γ δ R)) := by
          apply Finset.sum_congr rfl; intro a ha
          by_cases h : (p : ℤ) ∣ Polynomial.eval (a : ℤ)
              (Polynomial.derivative (CubicPhase p β γ δ R))
          · rw [if_pos h, if_pos ((dvd_deriv_iff_dvd_linCoeff p β γ δ R a).mp h)]
          · rw [if_neg h, if_neg (fun hh => h ((dvd_deriv_iff_dvd_linCoeff p β γ δ R a).mpr hh))]
    _ = (p:ℂ) * ∑ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ r),
          ∑ u ∈ Finset.range (p ^ (K - 2)),
                E (p ^ K) (Polynomial.eval ((r : ℤ) + (p : ℤ) * (u : ℤ)) (CubicPhase p β γ δ R)) :=
          sum_range_ite_mul_filter p _ _
    _ = (p:ℂ) * ∑ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ Work.LinnikBurgess.linCoeff β γ δ r),
          E (p ^ K) (Polynomial.eval (r : ℤ) (CubicPhase p β γ δ R))
            * Tsum (p ^ (K - 2)) (Work.LinnikBurgess.shiftPhase p β γ δ R r) := by
          apply congrArg (fun z => (p:ℂ) * z)
          apply Finset.sum_congr rfl; intro r hr
          obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
          exact cubicPhase_innerSum p K hK β γ δ R r (Finset.mem_range.mp hr1) hr2

end Work.LinnikBurgess
