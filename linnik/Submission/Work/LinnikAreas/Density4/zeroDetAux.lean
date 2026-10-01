/-
# Area 4 / HB §11 — auxiliary objects for the zero detector

Namespace `Work.LinnikAreas.Density4`.  This file introduces the divisor sums
`psiS`, `thetaS` of the mollifiers of HB (11.6)/(11.7) and the two smoothed Dirichlet
sums `S1` (single exponential `e^{-n/X}`) and `S2` (single exponential `e^{-n𝓛²/U}`)
whose difference is HB's zero detector `detSum`.  It is the vocabulary in which the
delegated analytic pieces of `zero_detector` are stated.  Sorry-free.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikContract.Areas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Work.LinnikContract

/-- `Ψ(n) = Σ_{d | n} ψ_d`, HB (11.6). -/
def psiS (U V : ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, psiM U V d

/-- `Θ(n) = Σ_{d | n} θ_d`, HB (11.7). -/
def thetaS (W : ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, thetaM W d

/-- The common complex coefficient `a_n χ(n) n^{-ρ}` of the detector (with `a_n = Ψ(n)Θ(n)`). -/
def detCoeff (q : ℕ) [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) (n : ℕ) : ℂ :=
  ((psiS U V n : ℝ) : ℂ) * ((thetaS W n : ℝ) : ℂ) * χ (n : ZMod q) * ((n : ℂ) ^ (-ρ))

/-- `S1 = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ} e^{-n/X}` — the smoothed Dirichlet sum whose
`O(1/𝓛)`-smallness is HB (11.9) (equivalently `L(ρ,χ)F(ρ) = 0` with the smoothing error). -/
def Ssm (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, detCoeff q U V W χ ρ n * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ)

/-- `S2 = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ} e^{-n𝓛²/U}` — the second smoothed sum; it equals
`1 + O(1/𝓛)` because `Ψ(n) = 0` for `2 ≤ n ≤ U` and `e^{-𝓛²/U} = 1 + O(1/𝓛)`, while the
tail `n > U` is exponentially small. -/
def Sbig (q : ℕ) [NeZero q] (U V W : ℝ) (L : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, detCoeff q U V W χ ρ n * ((Real.exp (-(n : ℝ) * L ^ 2 / U) : ℝ) : ℂ)

/-- The `n = 1` value: `Ψ(1) = 1`. -/
lemma psiS_one {U V : ℝ} (hU : (1:ℝ) ≤ U) : psiS U V 1 = 1 := by
  rw [psiS, Nat.divisors_one, Finset.sum_singleton]
  simp only [psiM, Nat.cast_one, if_pos hU, ArithmeticFunction.moebius_apply_one, Int.cast_one]

/-- The `n = 1` value: `Θ(1) = 1` (for `W > 1`, so `log W ≠ 0`). -/
lemma thetaS_one {W : ℝ} (hW : (1:ℝ) < W) : thetaS W 1 = 1 := by
  have hW0 : (0:ℝ) < W := by linarith
  have hlog : Real.log W ≠ 0 := ne_of_gt (Real.log_pos hW)
  rw [thetaS, Nat.divisors_one, Finset.sum_singleton]
  simp only [thetaM, Nat.cast_one, if_pos hW.le, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, one_mul]
  rw [Real.log_div hW0.ne' one_ne_zero, Real.log_one, sub_zero]
  exact div_self hlog

lemma psiS_zero (U V : ℝ) : psiS U V 0 = 0 := by simp [psiS]
lemma thetaS_zero (W : ℝ) : thetaS W 0 = 0 := by simp [thetaS]

end Work.LinnikAreas.Density4
