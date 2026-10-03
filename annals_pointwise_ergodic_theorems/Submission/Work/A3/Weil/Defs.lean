import Mathlib
import Submission.Work.A3.Circle
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

/-!
# Shared vocabulary for the proof of Weyl's inequality (`Work.A3.weyl_poly`)

This module collects the objects used by the proof of the polynomial Weyl bound

`‖expSum Q N θ‖ ≤ C N^{1+ε} (q⁻¹ + N⁻¹ + q N^{-d})^{1/2^{d-1}}`   (`‖θ - a/q‖ ≤ 1/q²`)

into a single place, so that the individual steps of the proof (the `k`-fold Weyl
differencing, the finite-difference computation for a polynomial, the geometric sum bound
for a phase that is affine in the summation index, the divisor bound, and the elementary
one-dimensional arithmetic estimate) can be stated and proved independently.

## The `e(·)` convention

`Work.A3.expSum Q N θ = Σ_{n ∈ [1,N]} e(-θ Q(n))` where `e(x) = exp(2πi x)`.  With the
phase `weylPhase Q θ m = -θ·Q(m+1)` (`m ∈ [0,N)`), this is the sum of `e (weylPhase Q θ m)`
over `m ∈ rangeZ N`.

## The differencing operators

`iterDiff k l φ` is the `k`-fold first difference of `φ` along the shifts `l : Fin k → ℤ`
(`Δ_{h₁} ⋯ Δ_{h_k}`), and `iterCorr k l u` is the corresponding `k`-fold autocorrelation
sequence (`u (· + h) · conj (u ·)` iterated).  The van der Corput recursion
`autocorr (iterCorr k l u) N h = iterCorr (k+1) (extend l h) u` is definitional.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace Weil

/-- The summation interval `[0,N)` as a finset of integers. -/
def wRange (N : ℕ) : Finset ℤ := Finset.Icc (0 : ℤ) ((N : ℤ) - 1)

/-- The set of admissible shifts `|h| ≤ N - 1`. -/
def shiftIdx (N : ℕ) : Finset ℤ := Finset.Icc (-(((N : ℤ) - 1))) (((N : ℤ) - 1))

/-- The real phase of `expSum`: `weylPhase Q θ m = -θ·Q(m+1)`, so that
`expSum Q N θ = Σ_{m ∈ wRange N} e (weylPhase Q θ m)`. -/
def weylPhase (Q : ℤ[X]) (θ : ℝ) : ℤ → ℝ := fun m => -θ * (((Q.eval (m + 1) : ℤ) : ℝ))

/-- The zero-extended phase sequence `m ↦ e(φ m)` on `wRange N`. -/
def phaseSeq (φ : ℤ → ℝ) (N : ℕ) : ℤ → ℂ :=
  fun m => if m ∈ wRange N then Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I) else 0

/-- The `k`-fold first difference `Δ_{l (k-1)} ⋯ Δ_{l 0}` of `φ` acting on functions `ℤ → ℝ`. -/
def iterDiff : (k : ℕ) → (Fin k → ℤ) → (ℤ → ℝ) → (ℤ → ℝ)
  | 0, _, φ => φ
  | k + 1, l, φ => fun n =>
      iterDiff k (fun i => l i.castSucc) φ (n + l (Fin.last k)) -
        iterDiff k (fun i => l i.castSucc) φ n

/-- The `k`-fold autocorrelation of the sequence `u` along the shifts `l`. -/
def iterCorr : (k : ℕ) → (Fin k → ℤ) → (ℤ → ℂ) → (ℤ → ℂ)
  | 0, _, u => u
  | k + 1, l, u => fun n =>
      iterCorr k (fun i => l i.castSucc) u (n + l (Fin.last k)) *
        star (iterCorr k (fun i => l i.castSucc) u n)

/-- The geometric-sum bound attached to a linear phase of coefficient `x`, summed over an
interval of length at most `N`: `1 / max (intDist x) (1/N)`. -/
def geomBound (N : ℕ) (x : ℝ) : ℝ :=
  (max (Submission.VanDerCorput.intDist x) ((N : ℝ)⁻¹))⁻¹

/-- The arithmetic sum that the `k`-fold differencing produces:
`Σ_{l ∈ (shiftIdx N)^k} geomBound N (Λ · ∏ l i)`. -/
def arithSum (N k : ℕ) (Λ : ℝ) : ℝ :=
  ∑ l ∈ Fintype.piFinset (fun _ : Fin k => shiftIdx N),
    geomBound N (Λ * ∏ i, ((l i : ℤ) : ℝ))

/-- The constant `d! · |leadingCoeff Q|` attached to `Q`; it is `≥ 1` when `Q ≠ 0`. -/
def weylConst (Q : Polynomial ℤ) : ℕ :=
  Nat.factorial Q.natDegree * (Q.coeff Q.natDegree).natAbs

/-- The slope of the affine phase `Δ_{h₁}⋯Δ_{h_k} (weylPhase Q θ)` for `k + 1 = natDegree Q`:
`-θ · d! · (leading coefficient of Q) · ∏ h`. -/
def weylSlope (Q : ℤ[X]) (θ : ℝ) (k : ℕ) (l : Fin k → ℤ) : ℝ :=
  -θ * (((Nat.factorial (Q.natDegree)) : ℝ) * ((Q.coeff (Q.natDegree) : ℤ) : ℝ)) *
    ∏ i, ((l i : ℤ) : ℝ)

lemma expSum_eq_sum_phaseSeq (Q : ℤ[X]) (N : ℕ) (θ : ℝ) :
    expSum Q N θ = ∑ m ∈ wRange N, phaseSeq (weylPhase Q θ) N m := by
  classical
  unfold expSum phaseSeq weylPhase wRange
  refine Finset.sum_bij (fun n _ => (n : ℤ) - 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n₁ h₁ n₂ h₂ h
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    refine ⟨(m + 1).toNat, ?_, ?_⟩
    · have h1 : (1 : ℤ) ≤ m + 1 := by omega
      have h2 : m + 1 ≤ (N : ℤ) := by omega
      simp only [Finset.mem_Icc]
      exact ⟨(Int.le_toNat (by omega)).mpr h1, (Int.toNat_le).mpr h2⟩
    · rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m + 1)]
      ring
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have hmem : (n : ℤ) - 1 ∈ Finset.Icc (0 : ℤ) ((N : ℤ) - 1) := by
      simp only [Finset.mem_Icc]
      omega
    rw [if_pos hmem]
    have hB : Q.eval (((n : ℤ) - 1) + 1) = Q.eval (n : ℤ) := by
      have : ((n : ℤ) - 1) + 1 = (n : ℤ) := by ring
      rw [this]
    rw [hB]
    congr 1
    push_cast
    ring

end Weil

end

end Work.A3
