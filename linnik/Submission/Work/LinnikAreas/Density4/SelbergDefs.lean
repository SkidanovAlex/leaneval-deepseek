import Mathlib
import Submission.Commons.NumberTheory.Moebius.log_moebius_lcm_sq_swap
import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
import Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

noncomputable section

/-! ## The objects of the proof

`selLam z d = μ(d) log(z/d)` are the Selberg weights; `selQ z` is the associated
quadratic (sieve) form `Σ_{d,e≤z} λ_d λ_e / lcm(d,e)`.  The sharp bound for the sum
`Σ_{n ≤ N} Λ_z(n)²` is obtained by proving `selQ z ≤ log z + O(1)` and using
`⌊N/lcm⌋ ≤ N/lcm` termwise.

The bookkeeping of the proof goes through the Mertens-type sum
`selU x = Σ_{m ≤ x} μ(m) log(x/m)/m` (which tends to `1`), its "coprime"
variant `selTheta y k = Σ_{m ≤ y, (m,k)=1} μ(m) log(y/m)/m`, and the harmonic
majorant `selRadSum y k = Σ_{d ≤ y, rad d ∣ k} 1/d`. -/

/-- The Selberg weight `λ_d = μ(d) log(z/d)`. -/
def selLam (z : ℕ) (d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))

/-- `U(x) = Σ_{m ≤ x} μ(m)·log(x/m)/m`. -/
def selU (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius m : ℝ) * Real.log (x / (m : ℝ)) / (m : ℝ)

/-- `Θ(y,k) = Σ_{m ≤ y, (m,k)=1} μ(m)·log(y/m)/m`. -/
def selTheta (y : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun m => Nat.Coprime m k),
    (ArithmeticFunction.moebius m : ℝ) * Real.log (y / (m : ℝ)) / (m : ℝ)

/-- `d` is `k`-smooth : every prime factor of `d` divides `k` (equivalently `rad d ∣ k`,
spelled as `d ∣ k^d` to keep the predicate decidable). -/
abbrev SmoothOf (d k : ℕ) : Prop := d ∣ k ^ d

/-- `S_k(y) = Σ_{d ≤ y, rad d ∣ k} 1/d`. -/
def selRadSum (y : ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d => SmoothOf d k), (1 : ℝ) / (d : ℝ)

/-- The Selberg quadratic form `Σ_{d,e ≤ z} λ_d λ_e / lcm(d,e)`. -/
def selQ (z : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
    selLam z d * selLam z e / (Nat.lcm d e : ℝ)

/-- The "combinatorial" majorant of `selQ`, obtained by replacing `U` by `1`. -/
def selComb (z : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 z).filter (fun k => Squarefree k),
    (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * selRadSum ((z : ℝ) / k) k ^ 2

/-- The "correction" term `B_z(n) = Σ_{z < d | n} μ(d)·log(d/z)` appearing in the identity
`Λ_z(n) = Λ(n) + B_z(n)` (valid for `n ≥ 2`, any `z`), used in the case `N < z²` of the
Barban–Vehov (Graham) estimate. -/
noncomputable def selB (z : ℕ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => z < d),
    (ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / (z : ℝ))

end

end Work.LinnikAreas.Density4
