/-
# Proposition 5.1 in the contour-shift form

CKMRV prove the two identities of Proposition 5.1 (`(4.5)`) not for the projective integral
`F₂^♯ = Work.Kernels.kernelTransform K` but for the *continuation* `F₂` of `F₂^♯` across the line
`Re τ = 1`, and the two computations are different in character:

* the **first** recurrence is computed on the shifted side: with
  `F₂(τ+2) = F₂^♯(τ+2) + 4 e^{πir²(τ+1)} sin²(πr²/2)` (the paper's `(matchF2sharp)`, obtained by
  deforming the contour across the pole `z = τ-1`, whose residue `1/(2π)` is
  `Work.Residues.hasResidue_Kfun_second`) one gets
  `F₂|(T-I)²(τ) = 4e^{πir²(τ+1)}sin² = -T2op (gaussTerm · r) τ`;
* the **second** recurrence needs no deformation at all: for `τ` such that the three points
  `S•τ`, `ST•τ`, `ST²•τ` are on the convergent side, each of the three terms of
  `F₂|S(T-I)²(τ)` is the integral, and the pointwise kernel identity
  `K(·,it)|S(T-I)² = 0` (`Work.Residues.Kaxis_Kfun_slash_S_T2`) gives `0`.

This file records both reductions in the form the continuation must supply them.  The residue
term is `Work.Asymptotics.resCorr r τ = e^{πir²(τ-1)}` (times `4 sin²(πr²/2)`); the key identity
`Work.Residues.resCorr_vadd_two` says that *at the shifted point* it is exactly the
right-hand side of the recurrence.
-/
import Mathlib
import Submission.Work.Residues.T2op_gaussTerm
import Submission.Work.Residues.Section5
import Submission.Work.Asymptotics.contourLeftDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups Manifold
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-- **The residue correction at the shifted point is the recurrence's right-hand side.**
`sinSqC r * resCorr r (τ+2) = 4 e^{πir²(τ+1)} sin²(πr²/2) = -T2op (gaussTerm · r) τ`: the term
produced by deforming the contour across the pole `z = τ-1` (with residue `1/(2π)`, i.e.
`Work.Residues.hasResidue_Kfun_second`) is exactly the inhomogeneous right-hand side of CKMRV
Proposition 5.1. -/
theorem resCorr_vadd_two (r : ℝ) (τ : ℍ) :
    Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ)
      = - T2op (fun σ : ℍ => gaussTerm σ r) τ := by
  have harg : Real.pi * Complex.I * (r : ℂ) ^ 2 * ((((2 : ℝ) +ᵥ τ : ℍ) : ℂ) - 1)
      = Real.pi * Complex.I * ((((1 : ℝ) +ᵥ τ : ℍ) : ℂ)) * (r : ℂ) ^ 2 := by
    rw [coe_vadd_two, coe_vadd_one]
    ring
  rw [T2op_gaussTerm, Work.Asymptotics.sinSqC, Work.Asymptotics.resCorr, gaussTerm, harg]
  ring

/-- **Proposition 5.1, first recurrence, contour-shift form.**  Suppose `H` is the corrected
`F₂`: it agrees with the projective integral at `τ` and `τ+1`, and at the shifted point `τ+2` it
agrees with the integral *plus the residue correction* `sinSqC r * resCorr r` (this is the
paper's `(matchF2sharp)`, supplied by the contour deformation).  If moreover the projective
integral has vanishing `(T-I)²`-defect at `τ` (the pointwise kernel law of Theorem 4.9(2)
integrated), then `H` satisfies the first recurrence. -/
theorem T2op_of_contourShift (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (τ : ℍ) (H : ℍ → ℂ)
    (h2 : H ((2 : ℝ) +ᵥ τ) = kernelTransform (Kfun ℓ d) ((2 : ℝ) +ᵥ τ) r
      + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ))
    (h1 : H ((1 : ℝ) +ᵥ τ) = kernelTransform (Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r)
    (h0 : H τ = kernelTransform (Kfun ℓ d) τ r)
    (hk : T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ = 0) :
    T2op H τ = - T2op (fun σ : ℍ => gaussTerm σ r) τ := by
  rw [T2op, h2, h1, h0]
  rw [show kernelTransform (Kfun ℓ d) ((2 : ℝ) +ᵥ τ) r
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ)
        - 2 * kernelTransform (Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r + kernelTransform (Kfun ℓ d) τ r
      = Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ)
        + (kernelTransform (Kfun ℓ d) ((2 : ℝ) +ᵥ τ) r
          - 2 * kernelTransform (Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r
          + kernelTransform (Kfun ℓ d) τ r) by ring]
  rw [show kernelTransform (Kfun ℓ d) ((2 : ℝ) +ᵥ τ) r
        - 2 * kernelTransform (Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r + kernelTransform (Kfun ℓ d) τ r
      = T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ from rfl,
    hk, add_zero, resCorr_vadd_two]

/-- **Proposition 5.1, second recurrence, "computed from the integral" form.**  If the corrected
`F₂` agrees with the projective integral at the three contour points `S•τ`, `ST•τ`, `ST²•τ`, and
those integrands are Bochner integrable (so `h5b` applies there — `Work.Residues.slash_of_agrees`
is exactly the case in which the paper says "each of the three terms can be computed using
`(5.2)`"), then `H` satisfies the second recurrence at `τ`. -/
theorem slash_of_agrees (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (τ : ℍ) (H : ℍ → ℂ)
    (hH : ∀ γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support,
      H (γ • τ) = kernelTransform (Kfun ℓ d) (γ • τ) r)
    (hint : ∀ γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support,
      IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) (γ • τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2) H τ = 0 := by
  have hslash : slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2) H τ
      = slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
          (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ := by
    simp only [slash, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun γ hγ => ?_)
    rw [Work.Kernels.slash_apply', Work.Kernels.slash_apply', hH γ hγ]
  rw [hslash]
  exact slash_Kfun_kernelTransform_eq_zero ℓ d hd r τ hint

/-! ## The correction `G = F₂ - F₂^♯` and its two defects

The two theorems above are exactly the paper's computation of Proposition 5.1 for the corrected
generating function `F₂ = Ψ`.  Subtracting the projective integral turns them into the two
conditions on the correction `G = Ψ - F₂^♯` that the socket
`Work.Residues.T2op_kernelTransform_add`/`slash_Kfun_kernelTransform_add` (and hence
`Work.Kernels.satisfiesThm31_of_analysis`) consumes. -/

/-- **The correction has the prescribed `(T-I)²`-defect.**
`T2op (fun σ => Ψ σ - kernelTransform K σ r) τ = -T2op (gaussTerm · r) τ`. -/
theorem T2op_correction (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (τ : ℍ) (Ψ : ℍ → ℂ)
    (h2 : Ψ ((2 : ℝ) +ᵥ τ) = kernelTransform (Kfun ℓ d) ((2 : ℝ) +ᵥ τ) r
      + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ))
    (h1 : Ψ ((1 : ℝ) +ᵥ τ) = kernelTransform (Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r)
    (h0 : Ψ τ = kernelTransform (Kfun ℓ d) τ r)
    (hk : T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ = 0) :
    T2op (fun σ : ℍ => Ψ σ - kernelTransform (Kfun ℓ d) σ r) τ
      = - T2op (fun σ : ℍ => gaussTerm σ r) τ := by
  have h := T2op_of_contourShift ℓ d hd r τ Ψ h2 h1 h0 hk
  have hsplit : T2op Ψ τ
      = T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ
        + T2op (fun σ : ℍ => Ψ σ - kernelTransform (Kfun ℓ d) σ r) τ := by
    simp only [T2op, Pi.sub_apply]
    ring
  rw [hsplit, hk, zero_add] at h
  exact h

/-- **The correction has vanishing `S(T-I)²`-defect.**
`slash (d/2) (S(T-I)²) (fun σ => Ψ σ - kernelTransform K σ r) τ = 0`. -/
theorem slash_correction (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (τ : ℍ) (Ψ : ℍ → ℂ)
    (hH : ∀ γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support,
      Ψ (γ • τ) = kernelTransform (Kfun ℓ d) (γ • τ) r)
    (hint : ∀ γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support,
      IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) (γ • τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun σ : ℍ => Ψ σ - kernelTransform (Kfun ℓ d) σ r) τ = 0 := by
  have h1 : slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2) Ψ τ = 0 :=
    slash_of_agrees ℓ d hd r τ Ψ hH hint
  have h2 : slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ = 0 :=
    slash_Kfun_kernelTransform_eq_zero ℓ d hd r τ hint
  have hsub : (fun σ : ℍ => Ψ σ - kernelTransform (Kfun ℓ d) σ r)
      = Ψ + (-1 : ℂ) • (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) := by
    funext σ; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hsub, Work.Kernels.slash_add_F, Work.Kernels.slash_smul_F]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  ring

end Work.Residues
