import Mathlib
import Submission.Work.FITop3.Defs3

/-!
# `D₀` of (9.11) is real

The kernel `C0mod fhat z₁ z₂` of (6.13)+(7.10) depends on the pair `(z₁,z₂)` only through the
symmetric quantities `|z₁z₂| = |z₂z₁|`, `|Δ(z₁,z₂)| = |Δ(z₂,z₁)|` and
`Re(z̄₁z₂) = Re(z̄₂z₁)`; the coprimality condition `GaussCoprime` is symmetric as well.  Hence the
double sum over `gBox Rz × gBox Rz` of the conjugate-symmetric kernel `β z₁ · β̄ z₂ · C₀(z₁,z₂)`
equals its own conjugate and is therefore real.

This is the algebraic reason for the paper's treating `D₀` as a real number throughout §§9–10.
-/

namespace Work.FIArea2

open Finset
open scoped BigOperators
open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable

noncomputable section

/-! Symmetries of the ingredients of the (9.11) kernel, kept in a private namespace so that no
name here can clash with a colleague's file in `Work.FIArea2`. -/
namespace D0modAux

/-- `Δ(z₂,z₁) = -Δ(z₁,z₂)` (paper (6.1)): the determinant is alternating. -/
lemma Delta_swap (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z2 z1 = -Work.FIPlan.Delta z1 z2 := by
  simp only [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- `|Δ(z₁,z₂)|` is symmetric. -/
lemma absDelta_swap (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z2 z1 = Work.FIPlan.absDelta z1 z2 := by
  unfold Work.FIPlan.absDelta
  rw [Delta_swap z1 z2, Int.natAbs_neg]

/-- `Re(z̄₁z₂) = r₁r₂ + s₁s₂` is symmetric in `(z₁,z₂)`. -/
lemma re_star_mul_swap (z1 z2 : GaussianInt) :
    (star z1 * z2).re = (star z2 * z1).re := by
  simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- The Jacobi-symbol factor `G₀` of (8.16) is symmetric. -/
lemma G0_swap (z1 z2 : GaussianInt) :
    Work.FIPlan.G0 z1 z2 = Work.FIPlan.G0 z2 z1 := by
  have hd : Work.FIPlan.absDelta z2 z1 = Work.FIPlan.absDelta z1 z2 := absDelta_swap z1 z2
  have hc : (star z2 * z1).re = (star z1 * z2).re := (re_star_mul_swap z1 z2).symm
  unfold Work.FIPlan.G0
  rw [hd, hc]

/-- The logarithm `log(2|z₁z₂|/|Δ(z₁,z₂)|)` of (7.10) is symmetric. -/
lemma logFac_swap (z1 z2 : GaussianInt) :
    Work.FITop3.logFac z1 z2 = Work.FITop3.logFac z2 z1 := by
  unfold Work.FITop3.logFac
  rw [mul_comm z1 z2, absDelta_swap z1 z2]

/-- The (6.13) kernel `C₀` is symmetric. -/
lemma C0mod_swap (fhat : ℝ) (z1 z2 : GaussianInt) :
    Work.FITop3.C0mod fhat z1 z2 = Work.FITop3.C0mod fhat z2 z1 := by
  unfold Work.FITop3.C0mod
  rw [mul_comm z1 z2, logFac_swap z1 z2, G0_swap z1 z2]

/-- Coprimality in `ℤ[i]` is symmetric. -/
lemma GaussCoprime_swap (z1 z2 : GaussianInt) :
    Work.FIPlan.GaussCoprime z1 z2 ↔ Work.FIPlan.GaussCoprime z2 z1 :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩

/-- The conjugate of a real complex number is itself. -/
lemma star_coe_real (r : ℝ) : star (r : ℂ) = r := by simp

/-- A double sum whose kernel satisfies `conj(F a b) = F b a` equals its own conjugate: the
terms pair off under `(z₁,z₂) ↦ (z₂,z₁)`, which is why `D₀` has no imaginary part. -/
lemma star_double_sum_eq_of_swap {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ι → ℂ)
    (hF : ∀ a b, star (F a b) = F b a) :
    star (∑ a ∈ s, ∑ b ∈ s, F a b) = ∑ a ∈ s, ∑ b ∈ s, F a b := by
  simp only [star_sum, hF]
  exact Finset.sum_comm

end D0modAux

/-! ## The theorem -/

end

end Work.FIArea2
