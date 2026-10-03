import Mathlib
import Submission.Work.FIArea4.WdyadSetup

/-!
# The local variance `W(d₁,d₂)` of the dyadic dual form

Vocabulary for the analysis following `Submission/Work/FIArea4/Wdyad_expansion.lean`.  After the
Poisson step the dual form is a bilinear sum `Σ_{d₁,d₂} Σ_{a < [d₁,d₂]} γ_{a%d₁,d₁}
conj(γ_{a%d₂,d₂}) K(d₁,d₂,a)` with the kernel

`K (d₁,d₂) a = Σ_r χ_r (1/q) Σ_k F̂(k/q) e(k r a / q)`,   `q = [d₁,d₂]`,

where `χ_r = (r | d₁' d₂') [gcd(r,d₁d₂) = 1]` is the Jacobi weight.  The local variance is
`W(d₁,d₂) = Σ_{a<q} |K(d₁,d₂,a)|²`.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Jacobi weight `(r | d₁' d₂') [gcd(r, d₁d₂) = 1]`, `dᵢ' = oddPart dᵢ`. -/
def wChar (d1 d2 : ℕ) (r : ℕ) : ℂ :=
  if Nat.Coprime r (d1 * d2)
  then (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ) else 0

/-- The kernel `K (d₁,d₂) a = Σ_r χ_r (1/q) Σ_k F̂(k/q) e(k r a / q)`, `q = [d₁,d₂]`. -/
def KK (F : ℝ → ℂ) (R : ℕ) (d1 d2 : ℕ) (a : ℕ) : ℂ :=
  (1 / (Nat.lcm d1 d2 : ℝ)) * ∑' k : ℤ, F ((k : ℝ) / (Nat.lcm d1 d2 : ℝ)) *
    (∑ r ∈ Finset.Ioc R (2 * R), wChar d1 d2 r *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) / (Nat.lcm d1 d2 : ℝ)))

/-- The local variance `W(d₁,d₂) = Σ_{a<[d₁,d₂]} |K(d₁,d₂,a)|²`. -/
def Wloc (F : ℝ → ℂ) (R : ℕ) (d1 d2 : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (Nat.lcm d1 d2), Complex.normSq (KK F R d1 d2 a)

/-- `c_m = Σ_{r | m} χ_r F̂((m/r)/[d₁,d₂])` (the sequence whose discrete Fourier transform is `K`). -/
def cCoef (F : ℝ → ℂ) (R : ℕ) (d1 d2 : ℕ) (m : ℤ) : ℂ :=
  ∑ r ∈ Finset.Ioc R (2 * R),
    if (r : ℤ) ∣ m
    then wChar d1 d2 r * F (((m / (r : ℤ) : ℤ) : ℝ) / (Nat.lcm d1 d2 : ℝ)) else 0

end

end Work.FIArea4
