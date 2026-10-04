import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `star_seriesFun`: complex conjugation of a Fourier series

The function on the torus attached to a coefficient family `c` is

`seriesFun c x = ∑'_k c k · exp (2πi k·x)`.

Complex conjugation acts on each character by `star (fourierExp k x) = fourierExp (-k) x`
(the characters have unit modulus and are inverse to their conjugate), so conjugating the
series conjugates the coefficients *and* reflects the index:

`star (seriesFun c x) = seriesFun (fun k => star (c (-k))) x`.

This identity needs no summability: `tsum` on `ℂ` (a `T2Space`) commutes with `star`, and
`k ↦ -k` is a bijection of the index type `ι → ℤ`.  The summability hypothesis `hc` of the
statement is therefore recorded but not used in the argument; it makes the identity a
statement about the honest sum (hence one usable in the `Hˢ`-estimates of Layer A, where
`seriesFun c` is assumed to converge absolutely).
-/

noncomputable section

namespace Work.Diff.STE

open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- Conjugating the Fourier character `k` gives the character `-k`: the character
`x ↦ exp (2πi k·x)` and its conjugate `x ↦ exp (-2πi k·x)` are both the exponential of an
imaginary real number, and the conjugation negates the imaginary part. -/
lemma star_fourierExp (k : ι → ℤ) (x : ι → ℝ) :
    star (fourierExp k x) = fourierExp (-k) x := by
  have hstar_exp : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) :=
    fun z => (Complex.exp_conj z).symm
  rw [fourierExp, fourierExp, hstar_exp]
  congr 1
  simp

/-- **Conjugation of a Fourier series**: conjugating `seriesFun c` conjugates the
coefficients and reflects the index, `star (c k) ↦ star (c (-k))`. -/
theorem star_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (hc : Summable (fun k : ι → ℤ => ‖c k‖)) (x : ι → ℝ) :
    star (Work.Diff.STE.seriesFun c x)
      = Work.Diff.STE.seriesFun (fun k : ι → ℤ => star (c (-k))) x := by
  have _ := hc
  -- `star` commutes with the (unconditional) sum over the discrete index type.
  rw [seriesFun, seriesFun, tsum_star]
  -- conj of each summand: `star (c k * char k) = star (c k) * char (-k)`.
  have h1 : (fun k : ι → ℤ => star (c k * fourierExp k x))
      = fun k => star (c k) * fourierExp (-k) x := by
    funext k
    rw [star_mul, star_fourierExp]
    exact mul_comm _ _
  rw [h1]
  -- reindex by the involution `k ↦ -k`.
  have h2 : (∑' k : ι → ℤ, star (c k) * fourierExp (-k) x)
      = ∑' k : ι → ℤ, star (c (-k)) * fourierExp k x := by
    rw [← Equiv.tsum_eq (Equiv.neg (ι → ℤ))
      (fun k : ι → ℤ => star (c k) * fourierExp (-k) x)]
    simp only [Equiv.neg_apply, neg_neg]
  exact h2

end Work.Diff.STE
