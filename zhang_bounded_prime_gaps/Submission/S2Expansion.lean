import Mathlib
import Submission.LevelOfDistribution
import Submission.Commons.NumberTheory.SieveWindows.weighted_divisorSumProduct_window_eq_k

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 1000000

/-!
# The θ-weighted (`S₂`) window expansion (Polymath8a §4.2, step 1)

Polymath8a Theorem 3.5 estimates the *prime* (θ-weighted) window sum

    Σ_{x ≤ n ≤ 2x, n ≡ b (W)} θ(n + h_{i₀}) ∏_{i ≠ i₀} λ_{Fᵢ}(n + hᵢ) λ_{Gᵢ}(n + hᵢ).

Expanding the divisor sums (this file) turns it into a sum over divisor tuples of
the coefficient `∏ᵢ αᵢ(dᵢ)βᵢ(eᵢ)` times the θ-weighted `S`-set sum `S̃` of P8 (43).
The CRT reduction of `S̃` to a single (primitive) residue class, and its
discrepancy decomposition, are in `Submission/LevelOfDistribution.lean`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **θ-weighted `k`-coordinate expansion.**  Over the residue-class window
`n ≡ b (mod W)`, the product of the one-dimensional divisor sums weighted by
`θ(n + h)` expands into a sum over divisor tuples of `∏ᵢ αᵢ(dᵢ)βᵢ(eᵢ)` times the
θ-weighted `S`-set sum `S̃` with moduli `lcm (dᵢ) (eᵢ)`. -/
theorem thetaResidueWindowProduct_eq_weighted_thetaSset {k D N W b : ℕ} {H : Fin k → ℕ}
    (h : ℕ) (α β : Fin k → ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
        thetaNat (n + h) * ∏ i : Fin k,
          (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
    ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h := by
  rw [Commons.NumberTheory.SieveWindows.weighted_divisorSumProduct_window_eq_k
      (k := k) (D := D) (s := (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W))
      (H := H) (g := fun n => thetaNat (n + h)) (α := α) (β := β)]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  have hset : ((Finset.Icc N (2 * N)).filter (fun n => n % W = b % W)).filter
      (fun n => ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ∣ n + H i) =
      Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) := by
    rw [Sset, Finset.filter_filter]
  rw [thetaSset, hset]

end Commons.NumberTheory.MaynardSieve
