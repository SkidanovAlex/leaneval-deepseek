/-
Auxiliary vocabulary for `Work.ZeroDensity.Montgomery.zeroDetAltPerron`.

We package the two Dirichlet series whose product is the smoothed Möbius sum:

* `charSeq χ n = χ (n : ZMod q)`, the coefficients of the Dirichlet L-function `L(s,χ)`;
* `muTrunc χ X n = μ(n)·χ(n)` if `(n : ℝ) ≤ X` and `0` otherwise, the coefficients of the
  truncated Möbius Dirichlet polynomial `M_X(s,χ)`.

The point of these two sequences is that their Dirichlet convolution is, pointwise, the
coefficient sequence `n ↦ mCoef X n · χ(n)` of the statement.
-/
import Mathlib
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltDefs

open scoped Classical BigOperators

namespace Work.ZeroDensity.Montgomery

/-- The Dirichlet coefficients `n ↦ χ(n)` of the L-function of `χ`. -/
noncomputable def charSeq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q)

/-- The truncated Möbius–character coefficients `n ↦ μ(n)χ(n)·[n ≤ X]`. -/
noncomputable def muTrunc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ) ≤ X then (ArithmeticFunction.moebius n : ℂ) * χ (n : ZMod q) else 0

/-- `charSeq` is the coefficient sequence `fun n => χ (n : ZMod q)`. -/
lemma charSeq_def {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    charSeq χ = fun n : ℕ => χ (n : ZMod q) := rfl

lemma muTrunc_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) :
    muTrunc χ X 0 = 0 := by
  rw [muTrunc]
  split_ifs with h
  · simp
  · rfl

lemma muTrunc_def {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) (n : ℕ) :
    muTrunc χ X n = if (n : ℝ) ≤ X then (ArithmeticFunction.moebius n : ℂ) * χ (n : ZMod q)
      else 0 := rfl


/-- The `n`-th summand of the (absolutely convergent) Dirichlet series
`Σ_n mCoef X n χ(n) n^{-s}`, multiplied by the inverse Mellin kernel `Γ(w) Y^w` and
evaluated on the vertical line `w = c + iu`. -/
noncomputable def perronTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y c : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I)))
    * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
    * (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)

/-- Unfolding lemma for `perronTerm`. -/
lemma perronTerm_def {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y c : ℝ) (n : ℕ) (u : ℝ) :
    perronTerm χ ρ X Y c n u
      = mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I)))
        * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
        * (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) := rfl

/-- `mCoef X 0 = 0`. -/
lemma mCoef_zero (X : ℝ) : mCoef X 0 = 0 := by
  simp [mCoef]

end Work.ZeroDensity.Montgomery
