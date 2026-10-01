/-
# The vocabulary for `ratioZeroL1fixed`

For a real (quadratic) Dirichlet character `χ` modulo `q`, we study the coefficients

  `λ(n) = Σ_{d | n} χ(d)`

of the Dirichlet series `ζ(s)L(s,χ) = Σ_n λ(n) n^{-s}` (valid for `Re s > 1`).  Since `χ` is
real, `λ(n) ∈ ℝ` and in fact `λ(n) ≥ 0`, which is the positivity that the Heath-Brown /
Friedlander--Iwaniec argument for the ratio `L(1,χ)/(1-β)` rests on.

The relevant quantities are

* `Asum χ x = Σ_{n ≤ ⌊x⌋} λ(n)` and `Efun χ x = Asum χ x - x·L(1,χ)`;
* the triangle-weighted sum `Ssm χ β x = Σ_{n ≤ x} λ(n) n^{-β}(1 - n/x)`.

The key analytic input (proved elsewhere in this directory) is the identity

  `∫_1^∞ Efun χ x · x^{-1-β} dx = L(1,χ)/(1-β)`

valid when `1/2 < β < 1` and `L(β,χ) = 0`; together with the exact finite identity
`Ssm χ β x = ∫_1^x ((1-β)u^{-β}/x + β u^{-β-1}) A(u) du` and the crude bound
`‖Efun χ x‖ ≤ C √q (log q) √x` it yields

  `|Ssm χ β x - L(1,χ) x^{1-β}/((1-β)(2-β))| ≤ C' √q (log q) x^{1/2-β}`,

and then `1 - 1/x ≤ Ssm χ β x ≤ x^{1-β}(1+log x)^2` gives the two-sided bound on `L(1,χ)`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

variable {q : ℕ} [NeZero q]

/-- `λ(n) = Σ_{d | n} χ(d)`: the coefficients of the Dirichlet series `ζ(s)L(s,χ)`. -/
def lam (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, χ (d : ZMod q)

/-- The real part of `λ(n)`.  For a *real* character `χ` (i.e. `χ^2 = 1`) this is `λ(n)`
itself; see `Work.LinnikAreas.lamR_eq`. -/
def lamR (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ := (lam χ n).re

/-- The summatory function `A(x) = Σ_{n ≤ ⌊x⌋} λ(n)`. -/
def Asum (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lam χ n

/-- The summatory function `A(x) = Σ_{n ≤ ⌊x⌋} λ(n)`, in its real form. -/
def AsumR (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lamR χ n

/-- `E(x) = A(x) - x·L(1,χ)`. -/
def Efun (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  Asum χ x - (x : ℂ) * LFunction χ 1

/-- The triangle-weighted sum `S(x) = Σ_{n ≤ x} λ(n) n^{-β}(1 - n/x)`, in real form. -/
def Ssm (χ : DirichletCharacter ℂ q) (β x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lamR χ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x)

@[simp] lemma lam_apply (χ : DirichletCharacter ℂ q) (n : ℕ) :
    lam χ n = ∑ d ∈ n.divisors, χ (d : ZMod q) := rfl

@[simp] lemma lamR_apply (χ : DirichletCharacter ℂ q) (n : ℕ) : lamR χ n = (lam χ n).re := rfl

@[simp] lemma Asum_apply (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Asum χ x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lam χ n := rfl

@[simp] lemma AsumR_apply (χ : DirichletCharacter ℂ q) (x : ℝ) :
    AsumR χ x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lamR χ n := rfl

@[simp] lemma Efun_apply (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Efun χ x = Asum χ x - (x : ℂ) * LFunction χ 1 := rfl

@[simp] lemma Ssm_apply (χ : DirichletCharacter ℂ q) (β x : ℝ) :
    Ssm χ β x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lamR χ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / x) := rfl


/-- The main term of the triangle-weighted sum: the contribution of the pole of `ζ(s)L(s,χ)` at
`s = 1`, i.e. `L(1,χ)·x^{1-β}/((1-β)(2-β))`. -/
def mainTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β x : ℝ) : ℂ :=
  LFunction χ 1 * ((x:ℂ) ^ ((1-β:ℝ):ℂ)) / (((1-β:ℝ):ℂ)*((2-β:ℝ):ℂ))

@[simp] lemma mainTerm_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β x : ℝ) :
    mainTerm χ β x = LFunction χ 1 * ((x:ℂ) ^ ((1-β:ℝ):ℂ)) / (((1-β:ℝ):ℂ)*((2-β:ℝ):ℂ)) :=
  rfl

/-- `1 = d * 1` in the divisor convolution.  (Trivial unfolding lemma.) -/
lemma lam_one (χ : DirichletCharacter ℂ q) : lam χ 1 = χ (1 : ZMod q) := by
  simp [lam]

end

end Work.LinnikAreas
