import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the Buchstab/Ramaré decomposition (Matomäki–Radziwiłł §5)

This file only contains the definitions used by the decomposition lemma
`Work.BMF.mrDirect.BuchstabDecomp` (Matomäki–Radziwiłł, *Multiplicative functions in short
intervals*, Lemma `lem:decomp`) and by the `k = 0` Dirichlet-polynomial mean-square bound
`Work.BMF.mr_dirichlet_L2_direct`.
-/

set_option autoImplicit false

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace mrDirect

noncomputable section

/-- The logarithmic Dirichlet polynomial `Σ_{X ≤ n ≤ 2X} a n · n^{-(1+it)}`. -/
def dirPolyM (a : ℕ → ℂ) (X t : ℝ) : ℂ :=
  ∑ n ∈ natIcc X (2 * X), a n * (n : ℂ) ^ (-(1 + Complex.I * t))

/-- `ω(m;P,Q)`: the number of **prime divisors** of `m` lying in the interval `[P,Q]`. -/
def omegaCount (P Q : ℝ) (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter
    (fun p : ℕ => p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ m)).card

/-- The short (dyadic in the logarithmic variable) prime-supported Dirichlet polynomial
`Q_{j,K}(s) = Σ_{e^{j/K} ≤ p ≤ e^{(j+1)/K}, p prime} c p · p^{-s}`. -/
def primePoly (c : ℕ → ℂ) (K : ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ ((Finset.Icc ⌈Real.exp ((j:ℝ) / K)⌉₊ ⌊Real.exp (((j:ℝ) + 1) / K)⌋₊).filter Nat.Prime),
    c p * (p : ℂ) ^ (-(1 + Complex.I * t))

/-- The remainder Dirichlet polynomial
`R_{j,K}(s) = Σ_{X e^{-(j+1)/K} ≤ m ≤ 2X e^{-j/K}} b m · (ω(m;P,Q)+1)^{-1} · m^{-s}`. -/
def remPoly (b : ℕ → ℂ) (P Q K X : ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ natIcc (X * Real.exp (-((j : ℝ) + 1) / K)) (2 * X * Real.exp (-(j : ℝ) / K)),
    b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ * (m : ℂ) ^ (-(1 + Complex.I * t))

/-- The index set `j` for which `[e^{j/K}, e^{(j+1)/K}]` meets `[P,Q]`. -/
def indexSet (K P Q : ℝ) : Finset ℕ :=
  Finset.Icc ⌊K * Real.log P⌋₊ ⌊K * Real.log Q⌋₊

end

end mrDirect

end Work.BMF
