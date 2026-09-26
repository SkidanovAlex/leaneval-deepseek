import Mathlib
import Submission.Work.Drive.knotPerturbDefs

/-!
# The six jet functionals of the degree-`4` trigonometric perturbation basis

This module collects the objects shared by the proof that the map

`c ↦ (Σ_j trigBasis j p • c j, Σ_j trigBasisD j p • c j, …, Σ_j trigBasisD j r • c j)`

from the perturbation coefficients `c : Fin 9 → Space` to the six jets
(value and velocity at the three points `p, q, r`) is surjective.

The six scalar functionals on the coefficient space are bundled as
`jetCoeff p q r : Fin 6 → Fin 9 → ℝ` (rows `0 … 5` are the values at
`p, q, r` and the derivatives at `p, q, r`, in that order), and the
accompanying complex sequence `jetF` encodes, for each integer frequency `k`,
the corresponding Fourier relation.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The six jet functionals, coefficientwise.  Rows `0`, `2`, `4` are the values at `p`, `q`, `r`
and rows `1`, `3`, `5` the corresponding derivatives. -/
def jetCoeff (p q r : ℝ) : Fin 6 → Fin 9 → ℝ
  | 0 => fun j => trigBasis j p
  | 1 => fun j => trigBasisD j p
  | 2 => fun j => trigBasis j q
  | 3 => fun j => trigBasisD j q
  | 4 => fun j => trigBasis j r
  | 5 => fun j => trigBasisD j r

@[simp] theorem jetCoeff_zero (p q r : ℝ) (j : Fin 9) : jetCoeff p q r 0 j = trigBasis j p := rfl
@[simp] theorem jetCoeff_one (p q r : ℝ) (j : Fin 9) : jetCoeff p q r 1 j = trigBasisD j p := rfl
@[simp] theorem jetCoeff_two (p q r : ℝ) (j : Fin 9) : jetCoeff p q r 2 j = trigBasis j q := rfl
@[simp] theorem jetCoeff_three (p q r : ℝ) (j : Fin 9) : jetCoeff p q r 3 j = trigBasisD j q := rfl
@[simp] theorem jetCoeff_four (p q r : ℝ) (j : Fin 9) : jetCoeff p q r 4 j = trigBasis j r := rfl
@[simp] theorem jetCoeff_five (p q r : ℝ) (j : Fin 9) : jetCoeff p q r 5 j = trigBasisD j r := rfl

/-- A sum over `Fin 6` expanded into its six terms. -/
theorem sum_six (c f : Fin 6 → ℝ) :
    (∑ i : Fin 6, c i * f i)
      = c 0 * f 0 + c 1 * f 1 + c 2 * f 2 + c 3 * f 3 + c 4 * f 4 + c 5 * f 5 := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- The exponential of `p` times the imaginary unit. -/
def jetExp (p : ℝ) : ℂ := Complex.exp ((p : ℂ) * Complex.I)

theorem jetExp_ne_zero (p : ℝ) : jetExp p ≠ 0 := Complex.exp_ne_zero _

/-- de Moivre in the form used throughout: `e^{ipt}` to the integer power `k` is
`cos (kp) + i sin (kp)`. -/
theorem jetExp_zpow (p : ℝ) (k : ℤ) :
    (jetExp p) ^ k
      = (Real.cos ((k : ℝ) * p) : ℂ) + (Real.sin ((k : ℝ) * p) : ℂ) * Complex.I := by
  have h1 : (jetExp p) ^ k = Complex.exp ((k : ℂ) * ((p : ℂ) * Complex.I)) := by
    rw [jetExp, Complex.exp_int_mul]
  rw [h1]
  have h2 : (k : ℂ) * ((p : ℂ) * Complex.I) = (((k : ℝ) * p : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h2, Complex.exp_ofReal_mul_I]

/-- The complex sequence attached to the six jet coefficients: a linear combination of the three
"affine-in-`k`" exponentials `k ↦ (c + i k d) wᵏ`.  Its vanishing at the nine consecutive
integers `-4, …, 4` forces all six coefficients to vanish. -/
def jetFc (z y x : ℂ) (α β γ δ ε ζ : ℝ) (k : ℤ) : ℂ :=
  ((α : ℂ) + (k : ℂ) * Complex.I * (β : ℂ)) * z ^ k
    + ((γ : ℂ) + (k : ℂ) * Complex.I * (δ : ℂ)) * y ^ k
    + ((ε : ℂ) + (k : ℂ) * Complex.I * (ζ : ℂ)) * x ^ k

/-- The version of `jetFc` attached to the three parameters `p, q, r`. -/
def jetF (p q r α β γ δ ε ζ : ℝ) (k : ℤ) : ℂ :=
  jetFc (jetExp p) (jetExp q) (jetExp r) α β γ δ ε ζ k

theorem jetF_eq_jetFc (p q r α β γ δ ε ζ : ℝ) (k : ℤ) :
    jetF p q r α β γ δ ε ζ k = jetFc (jetExp p) (jetExp q) (jetExp r) α β γ δ ε ζ k := rfl

@[simp] theorem jetF_zero (p q r α β γ δ ε ζ : ℝ) :
    jetF p q r α β γ δ ε ζ 0 = (α : ℂ) + (γ : ℂ) + (ε : ℂ) := by
  simp [jetF, jetFc]

/-- The six target jets as an element of `Fin 6 → Space`. -/
def jetTarget (xp yp xq yq xr yr : Space) : Fin 6 → Space
  | 0 => xp
  | 1 => yp
  | 2 => xq
  | 3 => yq
  | 4 => xr
  | 5 => yr

@[simp] theorem jetTarget_zero (xp yp xq yq xr yr : Space) :
    jetTarget xp yp xq yq xr yr 0 = xp := rfl
@[simp] theorem jetTarget_one (xp yp xq yq xr yr : Space) :
    jetTarget xp yp xq yq xr yr 1 = yp := rfl
@[simp] theorem jetTarget_two (xp yp xq yq xr yr : Space) :
    jetTarget xp yp xq yq xr yr 2 = xq := rfl
@[simp] theorem jetTarget_three (xp yp xq yq xr yr : Space) :
    jetTarget xp yp xq yq xr yr 3 = yq := rfl
@[simp] theorem jetTarget_four (xp yp xq yq xr yr : Space) :
    jetTarget xp yp xq yq xr yr 4 = xr := rfl
@[simp] theorem jetTarget_five (xp yp xq yq xr yr : Space) :
    jetTarget xp yp xq yq xr yr 5 = yr := rfl

/-- The `k`-th coordinate of a point of `Space`, as a linear map. -/
def spaceCoord (k : Fin 3) : Space →ₗ[ℝ] ℝ :=
  (LinearMap.proj k).comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap

@[simp] theorem spaceCoord_apply (k : Fin 3) (x : Space) : spaceCoord k x = x.ofLp k := rfl

/-- The point of `Space` with prescribed coordinates. -/
def spaceOfFun (g : Fin 3 → ℝ) : Space := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm g

@[simp] theorem spaceCoord_spaceOfFun (k : Fin 3) (g : Fin 3 → ℝ) :
    spaceCoord k (spaceOfFun g) = g k := by
  simp [spaceCoord, spaceOfFun]

end

end Work.Drive
