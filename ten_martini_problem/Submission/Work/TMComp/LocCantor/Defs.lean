import Mathlib
import Submission.Work.TMContract.Components

/-!
# C17 (`P_LocCantor`) — vocabulary

This file fixes the notation used by the proof of `Work.TMContract.P_LocCantor`
(AJ Thm 5.1: for irrational `α` with `DiophBelow α b₀`, coupling `λ ≥ 1`, and Anderson
localisation a.e. in the phase, the spectrum `Σ_{λ,α}` contains no interval).

The route is AJ §5 (proof of Thm 5.1):

1. Assume `J = (a,b) ⊆ Σ_{λ,α}`.  By Aubry duality (`P_Duality`), `J/λ ⊆ Σ_{λ⁻¹,α}` with
   `λ⁻¹ ≤ 1`.
2. For a.e. phase `θ` and every `E ∈ J` that is a generalised eigenvalue of `H_{λ,α,θ}`
   with exponentially decaying eigenvector `u` (Schnol `P_Schnol` + `ExpLocAE`), the
   *Fourier transform* `U(x) = Σ u_n e^{2πinx}` of `u` is analytic and the Bloch wave
   `W(x) = (U(x)e^{2πiθ}, U(x-α))` satisfies
   `W(x+α) = e^{-2πiθ} S_{λ⁻¹,E/λ}(x) W(x)`.
   Then `M = [W, W̄]` has constant determinant `ci` with `c ≠ 0` (excluding
   `2θ ∈ αℤ + ℤ`), so `A = [Re W, Im W]` conjugates the *dual* cocycle to the rotation
   `R_{±θ}`; adjusting the homotopy class of the conjugacy gives `E/λ ∈ Λ_{λ⁻¹,α}` and
   `N_{λ⁻¹,α}(E/λ) = 1 ∓ 2θ + 2kα - 2j`.
3. Conversely, for a.e. `θ` such an `E` exists, so the full-measure set of phases `θ` is
   contained in a countable union of affine images of `N_{λ⁻¹,α}(Λ_{λ⁻¹,α} ∩ J/λ)`, which
   is null by `P_Reducibility` + `P_Puig`.  Contradiction.

Everything in this file is a definition or an immediately true lemma.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory Filter Topology Set

namespace Work.TMComp

open Work.TMContract

/-- Fourier transform of a bi-infinite sequence: `U(x) = Σ_n u_n e^{2πinx}`.  For
exponentially decaying `u` this is an absolutely convergent series, uniformly in `x`. -/
def fourier (u : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℤ, u n * Complex.exp (2 * Real.pi * (n : ℝ) * x * Complex.I)

/-- The Bloch vector `W(x) = (U(x) e^{2πiθ}, U(x-α))` (AJ §5, proof of Thm 5.1). -/
def blochVec (α θ : ℝ) (u : ℤ → ℂ) (x : ℝ) : Fin 2 → ℂ :=
  ![fourier u x * Complex.exp (2 * Real.pi * θ * Complex.I),
    fourier u (x - α)]

/-- The dual cocycle matrix `S_{λ⁻¹,E/λ}(x)`, as a *complex* matrix, in the form used by the
Bloch identity: `dualMat lam E x = S_{λ⁻¹,E/λ}(x)` (the real transfer matrix `tmR` at
coupling `λ⁻¹` and energy `E/λ`, coerced to `ℂ`). -/
def dualMat (lam E x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((E : ℂ) - ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * ((lam⁻¹ : ℝ) : ℂ), -1; 1, 0]

/-- The matrix `M = [W, W̄]` (AJ §5), columns the Bloch wave and its pointwise conjugate. -/
def blochMat (α θ : ℝ) (u : ℤ → ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![blochVec α θ u x 0, conj (blochVec α θ u x 0);
     blochVec α θ u x 1, conj (blochVec α θ u x 1)]

/-- The real matrix `A = [Re W, Im W]` whose columns are the real and imaginary parts of the
Bloch wave; it conjugates the dual cocycle to the rotation `R_θ`. -/
def blochReal (α θ : ℝ) (u : ℤ → ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(blochVec α θ u x 0).re, (blochVec α θ u x 0).im;
     (blochVec α θ u x 1).re, (blochVec α θ u x 1).im]

/-- The sign matrix `diag(1,σ)`, `σ = ±1`. -/
def sgnMat (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, σ]

/-- The determinant-one conjugacy obtained from a matrix-valued function `A` with constant
nonvanishing determinant: the scaled adjugate of `A · diag(1,σ)`.  If
`A(x+α) = S(x) A(x) R_θ` and `σ d = |d|` with `d = det A`, then
`B(x+α) S(x) = R_{-σθ} B(x)` with `det B = 1`. -/
def normConj (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (σ : ℝ) : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun x => (Real.sqrt |(A x).det|)⁻¹ • (A x * sgnMat σ).adjugate

end Work.TMComp
