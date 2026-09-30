import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.zpt.vk_pre
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the Weyl/Taylor route to `Work.BMF.zpt.vk_bounded_lambda_nat`

The target is the Vinogradov--Korobov type bound `S(N,t) ≪ N^{1-δ}` for the block sum
`Σ_{N<n≤R}(n+u)^{-it}` in the regime `N ≤ t ≤ N^{88}`, with *some* (unprescribed,
astronomically small) saving `δ > 0`.

The route implemented in the surrounding files is the classical **Weyl shift + Taylor
expansion + Weyl's inequality**:

* one shifts the block sum by `m ≤ L`, reducing `S` to the average over `n` of the "relative"
  sums `Σ_{m≤L}(1+m/(n+u))^{-it}` (`Trel` below);
* the phase `-(t/2π)log(1+m/(n+u))` is replaced by its Taylor polynomial of degree `k`
  (`tayPhase`), the remainder being controlled by `Real.abs_log_sub_add_sum_range_le`;
* the resulting polynomial exponential sum is estimated by `weyl_inequality` with the rational
  approximation `a/q = 1/⌈1/γ_k⌉` of its leading coefficient `γ_k = (-1)^k t/(2πk(n+u)^k)`.

All constants in the resulting bound are existential and fixed (the parameters `k` and the
exponent `ε` of the Weyl inequality are absolute), which is what makes the saving uniform
enough for the target statement.
-/

namespace Work.BMF.zpt

open Finset
open scoped BigOperators

noncomputable section

/-- The `j`-th Taylor coefficient of the phase `x ↦ -(t/2π)log(x+u)` at `x = n`:
`γ_j = (-1)^j t / (2π j (n+u)^j)`. -/
def gam (j : ℕ) (t n u : ℝ) : ℝ :=
  (-1 : ℝ) ^ j * t / (2 * Real.pi * (j : ℝ) * (n + u) ^ j)

/-- The Taylor polynomial phase `Σ_{1 ≤ j ≤ k} γ_j m^j` of `-(t/2π)log(1+m/(n+u))`. -/
def tayPhase (k : ℕ) (t n u : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, gam j t n u * (m : ℝ) ^ j

/-- The Taylor polynomial of the phase, as a `Polynomial ℝ` (the form required by
`Commons.Analysis.ExponentialSums.weyl_inequality`). -/
def tayPoly (k : ℕ) (t n u : ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc 1 k, Polynomial.C (gam j t n u) * Polynomial.X ^ j

/-- The "relative" summand `(1 + m/(n+u))^{-it}`, written with the additive character `eC`. -/
def relTerm (n u t : ℝ) (m : ℕ) : ℂ :=
  Work.BMF.eC (-(t / (2 * Real.pi)) * Real.log (1 + (m : ℝ) / (n + u)))

/-- The "relative" exponential sum `Σ_{m ≤ M}(1+m/(n+u))^{-it}`. -/
def Trel (M : ℕ) (n u t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, relTerm n u t m

/-- The corresponding Taylor polynomial exponential sum `Σ_{m ≤ M} e(Σ_{j≤k} γ_j m^j)`. -/
def TrelPoly (k M : ℕ) (n u t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, Work.BMF.eC (tayPhase k t n u m)

/-- The block sum `Σ_{⌊N⌋<n≤⌊R⌋}(n+u)^{-it}` rewritten with the additive character `eC`. -/
def ESbE (N R u t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, Work.BMF.eC (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u))

/-- `eC` is additive. -/
lemma eC_add (a b : ℝ) : Work.BMF.eC (a + b) = Work.BMF.eC a * Work.BMF.eC b := by
  unfold Work.BMF.eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-- `eC` takes values on the unit circle. -/
lemma eC_norm (a : ℝ) : ‖Work.BMF.eC a‖ = 1 := by
  unfold Work.BMF.eC
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) = (((2 * Real.pi * a : ℝ)) : ℂ) * Complex.I from by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The block sum in `cpow` form agrees with its `eC` form (the base `n+u` is positive). -/
lemma ESb_eq_ESbE (N R u t : ℝ) (hu : 0 < u) (hN : 1 ≤ ⌊N⌋₊) :
    ESb N R u t = ESbE N R u t := by
  unfold ESb ESbE
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_Ioc.mp hn).1; omega
  have hpos : (0 : ℝ) < (n : ℝ) + u := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    linarith
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hpos)]
  rw [show Complex.log (((n : ℝ) + u : ℝ) : ℂ) = ((Real.log ((n : ℝ) + u) : ℝ) : ℂ) from
    (Complex.ofReal_log hpos.le).symm]
  unfold Work.BMF.eC
  congr 1
  push_cast
  field_simp

end

end Work.BMF.zpt
