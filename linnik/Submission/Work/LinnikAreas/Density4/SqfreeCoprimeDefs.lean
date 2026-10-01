import Mathlib

/-!
# Counting squarefree integers coprime to `r`: shared definitions

This file sets up the notions used by the proof that

`#{n ≤ Q : (n,r) = 1, n squarefree} = (Q/ζ(2))·∏_{p ∣ r} p/(p+1) + O(Q^{1/2+ε} σ_{-1/3}(r))`.

The two analytic objects are

* `moebU r = Σ_{m, (m,r) = 1} μ(m)/m²`, the coprimality restricted Möbius reciprocal sum
  (its value is `ζ(2)⁻¹ ∏_{p ∣ r} (1 - p⁻²)⁻¹`), and
* `moebUtrunc K r = Σ_{m ≤ K, (m,r) = 1} μ(m)/m²`, its truncation.
-/

namespace Work.LinnikAreas.Density4

open Finset

/-- `ζ(2) = π²/6` as a real number, i.e. the real part of the Riemann zeta value at `2`. -/
noncomputable def zeta2 : ℝ := (riemannZeta (2 : ℂ)).re

/-- The coprimality restricted Möbius reciprocal sum `Σ_{m, (m,r) = 1} μ(m)/m²`. -/
noncomputable def moebU (r : ℕ) : ℝ :=
  ∑' m : ℕ, if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0

/-- The truncation `Σ_{m ≤ K, (m,r) = 1} μ(m)/m²` of `moebU r`. -/
noncomputable def moebUtrunc (K r : ℕ) : ℝ :=
  ∑ m ∈ (Icc 1 K).filter (fun m => Nat.Coprime m r),
    (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2

end Work.LinnikAreas.Density4
