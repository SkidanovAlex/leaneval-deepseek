import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi

/-!
# `Ψ`-polynomial is homogeneous of degree `2d`

The quadratic form `Ψ_a^{(α)}(x) = 4α²⟨a,ν(x)⟩² − ‖a‖²‖ν(x)‖²` is a *form* of degree `2d` in `x`:
the Veronese coordinates `ν(x)_m = ∏ᵢ xᵢ^{mᵢ}` are forms of degree `d`, their squares are forms of
degree `2d`, and `⟨a,ν(x)⟩ = ∑_m aₘ ν(x)_m` is a linear combination of them.  Written as a
multivariate polynomial in the variables `X i`, `Ψ` becomes

`C (4α²) * (∑_m C aₘ * ∏_i X i^{mᵢ})² − C (‖a‖²) * (∑_m (∏_i X i^{mᵢ})²)`,

and this file records that this polynomial is homogeneous of the expected degree `2d`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace Work.HP2

/-- Each Veronese monomial `∏ i, X i ^ (m.1 i)` is a homogeneous polynomial of degree `d`. -/
theorem isHomogeneous_monomial_of_Mon (d n : ℕ) (m : Work.HP.Mon d n) :
    (∏ i, MvPolynomial.X (R := ℝ) i ^ (m.1 i : ℕ)).IsHomogeneous d := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (n + 1)))
    (fun i => MvPolynomial.X (R := ℝ) i ^ (m.1 i : ℕ)) (fun i => (m.1 i : ℕ))
    (fun i _ => MvPolynomial.isHomogeneous_X_pow i (m.1 i : ℕ))
  have hd : (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (m.1 i : ℕ)) = d := m.2
  rw [hd] at h
  exact h

theorem PsiPoly_homog (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α : ℝ) :
    (MvPolynomial.C (4 * α ^ 2) *
        (∑ m : Work.HP.Mon d n,
          MvPolynomial.C ((a m : ℝ)) * ∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) ^ 2
      - MvPolynomial.C ((Work.HP.eNorm a) ^ 2) *
        (∑ m : Work.HP.Mon d n,
          (∏ i, MvPolynomial.X i ^ (m.1 i : ℕ)) ^ 2)).IsHomogeneous (2 * d) := by
  have hmono := isHomogeneous_monomial_of_Mon d n
  have hP : (∑ m : Work.HP.Mon d n,
      MvPolynomial.C ((a m : ℝ)) * ∏ i, MvPolynomial.X (R := ℝ) i ^ (m.1 i : ℕ)).IsHomogeneous d := by
    apply IsHomogeneous.sum
    intro m _
    exact IsHomogeneous.C_mul (hmono m) ((a m : ℝ))
  have hP2 : ((∑ m : Work.HP.Mon d n,
      MvPolynomial.C ((a m : ℝ)) * ∏ i, MvPolynomial.X (R := ℝ) i ^ (m.1 i : ℕ)) ^ 2).IsHomogeneous
        (2 * d) := by
    simpa [Nat.mul_comm] using hP.pow 2
  have hQ : (∑ m : Work.HP.Mon d n,
      (∏ i, MvPolynomial.X (R := ℝ) i ^ (m.1 i : ℕ)) ^ 2).IsHomogeneous (2 * d) := by
    apply IsHomogeneous.sum
    intro m _
    simpa [Nat.mul_comm] using (hmono m).pow 2
  have h1 : (MvPolynomial.C (4 * α ^ 2) *
      (∑ m : Work.HP.Mon d n,
        MvPolynomial.C ((a m : ℝ)) * ∏ i, MvPolynomial.X (R := ℝ) i ^ (m.1 i : ℕ)) ^ 2).IsHomogeneous
          (2 * d) :=
    IsHomogeneous.C_mul hP2 (4 * α ^ 2)
  have h2 : (MvPolynomial.C ((Work.HP.eNorm a) ^ 2) *
      (∑ m : Work.HP.Mon d n,
        (∏ i, MvPolynomial.X (R := ℝ) i ^ (m.1 i : ℕ)) ^ 2)).IsHomogeneous (2 * d) :=
    IsHomogeneous.C_mul hQ ((Work.HP.eNorm a) ^ 2)
  exact h1.sub h2

end Work.HP2
