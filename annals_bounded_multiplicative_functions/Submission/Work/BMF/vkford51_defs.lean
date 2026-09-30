import Mathlib
import Submission.Work.BMF.vkford_defs
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ford's Lemma 5.1 : the vocabulary

This file fixes the objects of the proof of `Work.BMF.vkford_lemma51` (K. Ford,
*Vinogradov's integral and bounds for the Riemann zeta function*, Proc. LMS 85 (2002),
Lemma 5.1): the smoothed sum `U`, the `b`-sum `X(c)`, the frequency box, the extended
(`2s`-th moment) sum `T`, the pair-difference vector, the resonant sets `D_j`, and the
final product `Pprod` which is *syntactically* the right-hand side of the target.
-/

namespace Work.BMF

open Finset
open scoped BigOperators

noncomputable section

/-- Ford's `γ_j = (-1)^j t/(2π j z^j)` (indexed by `j ≥ 1`). -/
def gam (j : ℕ) (t z : ℝ) : ℝ := (-1 : ℝ) ^ j * t / (2 * Real.pi * (j : ℝ) * z ^ j)

/-- The kernel coefficient in the `j`-th variable: `(π²K/2)·tentCoeff (1/(2K))`. -/
def kern (K : ℕ) (c : ℤ) : ℝ := (Real.pi ^ 2 * (K : ℝ) / 2) * tentCoeff (1 / (2 * (K : ℝ))) c

/-- Ford's smoothed exponential sum `U = Σ_{a ≤ M₁} Σ_{b ≤ M₂} e(Σ_{j≤k} γ_j (ab)^j)`. -/
def Usum (k M₁ M₂ : ℕ) (γ : Fin k → ℝ) : ℂ :=
  ∑ a ∈ Icc 1 M₁, ∑ b ∈ Icc 1 M₂,
    eZ (∑ j : Fin k, γ j * ((a : ℝ) * (b : ℝ)) ^ ((j : ℕ) + 1))

/-- The inner `b`-sum `X(c) = Σ_{b ≤ M₂} ε_b e(Σ_{j≤k} γ_j b^j c_j)`. -/
def Xsum (k M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) : ℂ :=
  ∑ b ∈ Icc 1 M₂, ε b * eZ (∑ j : Fin k, γ j * (b : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ))

/-- The box `∏_{j≤k} [1, r M₁^j]` of frequencies. -/
def Cbox (r M₁ k : ℕ) : Finset (Fin k → ℤ) :=
  ((Finset.pi Finset.univ (fun j : Fin k => Icc 1 (r * M₁ ^ ((j : ℕ) + 1)))).image
    (fun f j => (f j (Finset.mem_univ j) : ℤ)))

/-- `n(c)`: the number of `r`-tuples in `[1,M₁]^r` with power sums `c`. -/
def ncount (r k M₁ : ℕ) (c : Fin k → ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)).filter
    (fun a => ∀ j : Fin k, ∑ i, (((a i).1 : ℤ) ^ ((j : ℕ) + 1)) = c j)).card

/-- Ford's `T = Σ_{c ∈ ∏ [1, rM₁^j]} ‖X(c)‖^{2s}`. -/
def Tsum (r s M₁ M₂ k : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) : ℝ :=
  ∑ c ∈ Cbox r M₁ k, ‖Xsum k M₂ γ ε c‖ ^ (2 * s)

/-- The pairs of `s`-tuples with entries in `[1,M₂]`. -/
abbrev Pair (s M₂ : ℕ) : Type := (Fin s → Finset.Icc 1 M₂) × (Fin s → Finset.Icc 1 M₂)

/-- The difference `Σ_i b_i^j - Σ_i b'_i^j` of a pair, as an integer. -/
def dvec {s M₂ : ℕ} (j : ℕ) (p : Pair s M₂) : ℤ :=
  (∑ i, (((p.1 i).1 : ℤ) ^ j)) - (∑ i, (((p.2 i).1 : ℤ) ^ j))

/-- The product of the phases `ε_b` over a pair. -/
def epsp {s M₂ : ℕ} (ε : ℕ → ℂ) (p : Pair s M₂) : ℂ :=
  ∏ i, (ε (p.1 i).1 * star (ε (p.2 i).1))

/-- The resonant set `D_j = {|d| ≤ sM₂^j - 1 : ‖dγ‖ < 1/(2rM₁^j)}`. -/
def Dset (r s M₁ M₂ j : ℕ) (γ : ℝ) : Finset ℤ :=
  (Icc (-(((s * M₂ ^ j - 1 : ℕ)) : ℤ)) (((s * M₂ ^ j - 1 : ℕ) : ℤ))).filter
    (fun d => nint ((d : ℝ) * γ) < 1 / (2 * (r : ℝ) * (M₁ : ℝ) ^ j))

/-- The product appearing in the right-hand side of Ford's Lemma 5.1. -/
def Pprod (k r s h g : ℕ) (N t : ℝ) (M₁ M₂ : ℕ) : ℝ :=
  (5 * (r : ℝ)) ^ k * (M₂ : ℝ) ^ (-(2 * (s : ℝ)))
    * (M₁ : ℝ) ^ (-(2 * (r : ℝ)) + (k : ℝ) * ((k : ℝ) + 1) / 2)
    * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁
    * Jincom s g h (Icc 1 M₂)
    * ∏ j ∈ Icc h g, fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j

/-- The inner `a`-sum `Y_b = Σ_{a ≤ M₁} e(Σ_{j≤k} γ_j (ab)^j)`. -/
def Yfun (k M₁ : ℕ) (γ : Fin k → ℝ) (b : ℕ) : ℂ :=
  ∑ a ∈ Icc 1 M₁, eZ (∑ j : Fin k, γ j * ((a : ℝ) * (b : ℝ)) ^ ((j : ℕ) + 1))

/-- The kernel-weighted `2s`-th moment of the `b`-sum, i.e. Ford's `T` with the Fourier kernel
`kern` inserted in every frequency: `∑_c ∏_j kern (r M₁^{j+1}) (c_j) ‖X(c)‖^{2s}`. -/
def Tker (r s M₁ M₂ k : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) : ℝ :=
  ∑' c : Fin k → ℤ,
    (∏ j : Fin k, kern (r * M₁ ^ ((j : ℕ) + 1)) (c j)) * ‖Xsum k M₂ γ ε c‖ ^ (2 * s)

/-- The partial sum `S(N,t) = Σ_{N<n≤R} (n+u)^{-it}`. -/
def Ssum (N u t R : ℝ) : ℂ :=
  ∑ n ∈ Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))

end

end Work.BMF
