/-
# Section 5 of CKMRV: the second recurrence of Proposition 5.1 (`h5b`)

CKMRV Proposition 5.1 shows that the function
`F₂(τ,r) = 4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt` extends to a holomorphic function on `ℍ`
satisfying the recurrences

  `F₂|^τ_{d/2}(T-I)² = -e^{πir²τ}|^τ_{d/2}(T-I)²`  and  `F₂|^τ_{d/2}S(T-I)² = 0`

(equation (4.5) of the paper).  The *second* of these needs no contour shifting: it follows
from the pointwise kernel identity `K(·,it)|^τ_{d/2}S(T-I)² = 0` (Theorem 4.9(2)) together
with the fact that the group-algebra action commutes with the contour integral.

This file isolates that argument: `Work.Residues.slash_Kfun_kernelTransform_eq_zero` proves
`h5b` from the pointwise kernel identity and the Bochner integrability of the contour
integrands (the latter being the analytic input supplied by the bounds of Section 4.5).

The *first* recurrence (`h5a`, the case where the contour shift crosses the pole at `z = τ-1`
and picks up the residue `1/(2π)`) is not proved here; the residue computation it needs is
`Work.Residues.hasResidue_slash_Kfun` (Theorem 4.9(3)), but the analytic continuation of `F₂`
past `Re τ = ±1` (the contour shift across the pole and the `F₂^♯` comparison of
(matchF2sharp)) is not formalised in this chapter.
-/
import Mathlib
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Residues.slash_kernelTransform

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-- **The second recurrence of CKMRV Proposition 5.1 (`h5b`), reduced to integrability.**
For the kernel `K = Kfun ℓ d` and the generator `S(T-I)²` of `𝓘`, the slashed kernel transform
vanishes as soon as the contour integrands are Bochner integrable. -/
theorem slash_Kfun_kernelTransform_eq_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : ℍ)
    (hint : ∀ γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support,
      IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) (γ • τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ = 0 := by
  rw [slash_kernelTransform ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2) (Kfun ℓ d) r τ hint]
  have hzero : (fun t : ℝ => slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun σ : ℍ => Kaxis (Kfun ℓ d) σ t) τ *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    rw [Kaxis_Kfun_slash_S_T2 ℓ d hd t]
    simp
  rw [hzero]
  simp

/-- **`h5b` as a function identity**: the slashed kernel transform is the zero function. -/
theorem slash_Kfun_kernelTransform (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ)
    (hint : ∀ (τ : ℍ) (γ : SL(2,ℤ)), γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support →
      IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) (γ • τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) = 0 := by
  funext τ
  exact slash_Kfun_kernelTransform_eq_zero ℓ d hd r τ (fun γ hγ => hint τ γ hγ)

end Work.Residues
