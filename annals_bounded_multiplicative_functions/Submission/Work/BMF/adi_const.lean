import Mathlib
import Submission.Work.BMF.adi_basic
import Submission.Work.BMF.adi_main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The explicit constants of the final assembly of `Work.BMF.solve_adi`
-/

namespace Work.BMF

open Polynomial Finset

/-- The final modulus `q`: a `(k+1)`-st power, so that `D_m m! q_m` divides `q^m` for all
`m ≤ k` for either side. -/
noncomputable def Qfin (k : ℕ) (a1 b1 a2 b2 : ℕ) : ℕ :=
  ((k.factorial) ^ (k + 1) * qprod k a1 b1 * qprod k a2 b2) ^ (k + 1)

/-- Exponent of the final constant `C₁`. -/
def Eexp (k : ℕ) : ℕ := 100 * (k + 1) ^ 4 * (k.factorial + 1) + 100

/-- The final constant `C₁ = (C₀+2)^(Eexp k)`. -/
noncomputable def C1c (k : ℕ) (C₀ : ℝ) : ℝ := (C₀ + 2) ^ (Eexp k)

/-- The exponent `K₀` of the final modulus bound `q ≤ Z^{K₀}`. -/
def K0c (k : ℕ) : ℕ := k * (k + 1) ^ 2 + 100 * (k + 1) ^ 2 * (k.factorial + 1)

/-- The exponent `K` of the hypothesis `Z^K ≤ Qm`. -/
def Kc (k : ℕ) : ℕ := K0c k + k + 1 + Eexp k + 2 * k + 2

/-- Bound for the derivative of `ε` on the original interval `Icc x (x+L)`. -/
noncomputable def Ceps1 (k : ℕ) (C₀ : ℝ) : ℝ :=
  ((k : ℝ) + 1) * CTc k C₀ * C₀ ^ (k + 1) / (2 * Real.pi)

/-- Bound for the derivative of `ε` on the enlarged interval `[x - 3C₀²L, x + 3C₀²L]`. -/
noncomputable def Ceps2 (k : ℕ) (C₀ : ℝ) : ℝ :=
  ((k : ℝ) + 1) * CTc k C₀ * C₀ * (3 * C₀ ^ 3) ^ k / Real.pi

/-- Bound for the "other terms" in the estimate of `G'` at a lattice point (in units of
`p₂/L`). -/
noncomputable def C2c (k : ℕ) (C₀ : ℝ) : ℝ :=
  Ceps1 k C₀ + C₀ * Ceps2 k C₀ + 2 * ((k : ℝ) + 1) ^ (2 * k + 4) * C₀

/-- Bound for `|G'| · N^{-k} · L · p₂^{-1}` on the middle of `J`. -/
noncomputable def Cgs (k : ℕ) (C₀ : ℝ) : ℝ :=
  2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi) + C2c k C₀

end Work.BMF
