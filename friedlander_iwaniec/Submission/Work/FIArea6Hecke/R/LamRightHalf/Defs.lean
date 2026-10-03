/-
# `Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs`

The **weight-`m` dual theta series** of a strict character `χ` mod `4d`: the function produced by
Poisson summation on the other side of Hecke's functional equation,

  `thetaDualM d χ m w = Σ_{ξ ∈ ℤ²} ĝ(ξ)·(ξ₁ + i ξ₂)^m · e^{-π|ξ|²w}`,   `ĝ(ξ) = gaussSum d χ ξ`,

together with the normalised kernel `thetaDualMG d χ m x = c·thetaDualM d χ m (x/(16 d²))` in which
the Poisson transformation of the *holomorphic* theta series `thetaHol χ m` is written,

  `thetaHol χ m (1/x) = x^{m+1}·thetaDualMG d χ m x`,   `x > 0`

(see the lemma `thetaHol_one_div_dual`).  This generalises `R/A6HeckeDual` (the case `m = 0`, used
for `exists_completion_strict`) to every weight `m : ℕ`; the extra factor `(ξ₁ + i ξ₂)^m` is the
monomial Fourier factor carried by the weight-`m` theta series.  Unlike the primitive case, ĝ is
*not* proportional to `χ̄`, so `thetaDualM` is not itself an `L`-series; it is nonetheless an
exponentially decaying continuous kernel, which is all the Mellin-transform (weak functional
equation) argument needs.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The **weight-`m` dual theta series** `Σ_{ξ ∈ ℤ²} ĝ(ξ)(ξ₁ + iξ₂)^m e^{-π|ξ|²w}` of a strict
character `χ` mod `4d`, where `ĝ(ξ) = gaussSum d χ ξ` is the Gauss sum (finite Fourier transform)
of `χ`. -/
def thetaDualM (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (w : ℝ) : ℂ :=
  ∑' ξ : ℤ × ℤ,
    Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
      (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) ^ m) *
      Complex.exp (((-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)) : ℝ) : ℂ))

/-- The constant of the Poisson transformation
`c = (Σ_{u∈μ₄}χ(u)u^m)^{-1}·(4d)^{-2}·(-i)^m·(4d)^{-m}`. -/
def dualConst (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) : ℂ :=
  (Work.FIArea5.S16Hecke.unitSum chi m)⁻¹ * (1 / (((4 * d : ℕ) : ℂ)) ^ 2) *
    (-Complex.I) ^ m * ((((4 * d : ℕ) : ℂ)) ^ m)⁻¹

/-- The **normalised dual kernel** `thetaDualMG d χ m x = c·thetaDualM d χ m (x/(16d²))`, i.e. the
theta series on the dual side of the Poisson transformation of `thetaHol χ m`. -/
def thetaDualMG (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) : ℝ → ℂ :=
  fun x => dualConst d chi m * thetaDualM d chi m (x / (16 * (d : ℝ) ^ 2))

/-- Size bound for the monomial factor: `‖(ξ₁+iξ₂)^m‖ ≤ (1 + |ξ|²)^m`. -/
lemma norm_pow_le_one_add_gnorm (ξ : ℤ × ℤ) (m : ℕ) :
    ‖(((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) ^ m)‖ ≤ (1 + ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)) ^ m := by
  rw [norm_pow]
  have hsq : ‖((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ))‖ ^ 2 = (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 := by
    rw [Complex.sq_norm]
    rw [show Complex.normSq ((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ))
        = Complex.normSq ((ξ.1 : ℝ) + (ξ.2 : ℝ) * Complex.I) by
      congr 1; push_cast; ring]
    rw [Complex.normSq_add_mul_I]
  have hle : ‖((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ))‖
      ≤ 1 + ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) := by
    have hn : ‖((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ))‖
        = Real.sqrt ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) := by
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    rw [hn, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)]
  exact pow_le_pow_left₀ (norm_nonneg _) hle m

@[simp] lemma thetaDualM_apply (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (w : ℝ) :
    thetaDualM d chi m w = ∑' ξ : ℤ × ℤ,
      Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) ^ m) *
        Complex.exp (((-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w)) : ℝ) : ℂ)) := rfl

@[simp] lemma thetaDualMG_apply (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (x : ℝ) :
    thetaDualMG d chi m x
      = dualConst d chi m * thetaDualM d chi m (x / (16 * (d : ℝ) ^ 2)) := rfl

end

end Work.FIArea6Hecke.R
