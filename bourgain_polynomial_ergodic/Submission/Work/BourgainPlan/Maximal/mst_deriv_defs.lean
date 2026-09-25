import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs

/-!
# Vocabulary for the derivatives of the lifted one-arc error symbol `mstTht`

`mstTht P J β r u = star (mstG P β) − star (polyWeylKernel P J (r + u))` is, up to the constant
`star (mstG P β)`, the conjugate Weyl kernel read at the lifted offset `r + u`.  Since `P` has
integer coefficients, `star_polyWeylKernel_expand` (in `mst_freeze_defs`) writes it as the finite
sum `J⁻¹ Σ_{n<J} e^{−2πi (r+u) P(n)}`, whose summands are the `mstExpTerm P r n` below.  The
constants `mstPn P n = P(n)` (read as a real), `mstDConst P n = −2πi P(n)` and the normalisation
`mstJInv J = J⁻¹` make the derivative computations of `mstTht_deriv_bounds` readable.
-/

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- `P(n)` read as a real number; `P` has integer coefficients. -/
def mstPn (P : Polynomial ℤ) (n : ℕ) : ℝ := ((P.eval (n : ℤ) : ℤ) : ℝ)

/-- `J⁻¹` as a complex number: the normalisation constant of the Weyl kernel.  Written exactly as
in `star_polyWeylKernel_expand` so that the two are definitionally equal. -/
def mstJInv (J : ℕ) : ℂ := ((J : ℝ)⁻¹ : ℂ)

/-- The `n`-th summand `u ↦ e^{−2πi (r+u) P(n)}` of the conjugate Weyl kernel. -/
def mstExpTerm (P : Polynomial ℤ) (r : ℝ) (n : ℕ) : ℝ → ℂ :=
  fun u => Complex.exp ((((-(2 * Real.pi * ((r + u) * mstPn P n))) : ℝ) : ℂ) * Complex.I)

/-- The derivative constant `−2πi P(n)` of the `n`-th summand. -/
def mstDConst (P : Polynomial ℤ) (n : ℕ) : ℂ :=
  (((-(2 * Real.pi * mstPn P n)) : ℝ) : ℂ) * Complex.I

/-- The (unnormalised) finite sum `u ↦ Σ_{n<J} e^{−2πi (r+u) P(n)}`. -/
def mstExpSum (P : Polynomial ℤ) (J : ℕ) (r : ℝ) : ℝ → ℂ :=
  fun u => ∑ n ∈ Finset.range J, mstExpTerm P r n u

/-- The termwise derivative `u ↦ Σ_{n<J} (−2πi P(n)) e^{−2πi (r+u) P(n)}` of `mstExpSum`. -/
def mstExpSumDeriv (P : Polynomial ℤ) (J : ℕ) (r : ℝ) : ℝ → ℂ :=
  fun u => ∑ n ∈ Finset.range J, mstExpTerm P r n u * mstDConst P n

/-- The termwise second derivative `u ↦ Σ_{n<J} (−2πi P(n))² e^{−2πi (r+u) P(n)}`. -/
def mstExpSumDeriv2 (P : Polynomial ℤ) (J : ℕ) (r : ℝ) : ℝ → ℂ :=
  fun u => ∑ n ∈ Finset.range J, mstExpTerm P r n u * (mstDConst P n) ^ 2

end

end Work.BourgainPlan.Maximal
