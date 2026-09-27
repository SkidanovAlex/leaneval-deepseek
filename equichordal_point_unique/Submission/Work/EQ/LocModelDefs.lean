import Mathlib
import Submission.Work.EQ.SymDefs

/-!
# Auxiliary definitions for the local model of `eqT` at a real fixed point

Setting (see `Submission/Work/EQ/SymDefs.lean`): `O₁ = -a/2`, `O₂ = a/2` on the real axis of `ℂ`,
`chordMap c P = P - (P-c)/‖P-c‖` is the chord involution, and `eqT a = chordMap (O₁) ∘ chordMap (O₂)`.

For `0 < a < 1` and a real base point `A = a₀` with `a/2 - 1 < a₀ < -a/2` we have
`s := A  - O₂ < 0` in absolute value `a/2 - a₀ ∈ (a,1)`, and the two-step map is
`P ↦ P - u₂(P) - u₁(P - u₂(P))`.  Writing `P = A + ξ + η i` this reads, in real coordinates,

* `σ = ‖P - O₂‖`, `X₁ = A + ξ - u/σ` (with `u = ξ - s`), `Y₁ = η - η/σ`,
* `v = X₁ + a/2`, `τ = ‖(v, Y₁)‖`, `X₂ = X₁ - v/τ`, `Y₂ = Y₁ - Y₁/τ`,

so that `eqT a P = X₂ + Y₂ i`.  On the real axis (`η = 0`) one has `X₂ = ξ + A`, `Y₂ = 0`
pointwise near `A`, and the vertical multiplier at `A` is
`λ = (1 - 1/s) (1 - 1/t)` with `t = A + 1 + a/2 ∈ (a,1)`.

The functions below encode exactly these quantities.
-/

namespace Work.EQ

open Complex

noncomputable section

/-- `s = a/2 - a₀`, the distance from `A = a₀` to the right focus `O₂ = a/2`. -/
def lmS (a a₀ : ℝ) : ℝ := a/2 - a₀

/-- `t = a₀ + 1 + a/2`, the distance from the first image `A + 1` to the left focus `O₁ = -a/2`. -/
def lmT (a a₀ : ℝ) : ℝ := a₀ + 1 + a/2

/-- Half-width of the box `[-lmH, lmH]²` on which the local model is established. -/
def lmH (a a₀ : ℝ) : ℝ := min (lmS a a₀) (lmT a a₀) / 16

/-- The box on which the local model is established. -/
def lmBox (a a₀ ξ η : ℝ) : Prop := |ξ| ≤ lmH a a₀ ∧ |η| ≤ lmH a a₀

/-- `u = a₀ + ξ - a/2 = ξ - s`: real part of `P - O₂`. -/
def lmU (a a₀ ξ : ℝ) : ℝ := a₀ + ξ - a/2

/-- `σ = ‖P - O₂‖`. -/
def lmSig (a a₀ ξ η : ℝ) : ℝ := Real.sqrt ((lmU a a₀ ξ)^2 + η^2)

/-- Real part of `chordMap O₂ P`. -/
def lmX1 (a a₀ ξ η : ℝ) : ℝ := (a₀ + ξ) - lmU a a₀ ξ / lmSig a a₀ ξ η

/-- Imaginary part of `chordMap O₂ P`. -/
def lmY1 (a a₀ ξ η : ℝ) : ℝ := η - η / lmSig a a₀ ξ η

/-- `v = X₁ + a/2`: real part of `chordMap O₂ P` relative to `O₁`. -/
def lmV (a a₀ ξ η : ℝ) : ℝ := lmX1 a a₀ ξ η + a/2

/-- `τ = ‖(v, Y₁)‖`. -/
def lmTau (a a₀ ξ η : ℝ) : ℝ := Real.sqrt ((lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2)

/-- Real part of `eqT a P`. -/
def lmX2 (a a₀ ξ η : ℝ) : ℝ := lmX1 a a₀ ξ η - lmV a a₀ ξ η / lmTau a a₀ ξ η

/-- Imaginary part of `eqT a P`. -/
def lmY2 (a a₀ ξ η : ℝ) : ℝ := lmY1 a a₀ ξ η - lmY1 a a₀ ξ η / lmTau a a₀ ξ η

/-- The horizontal displacement `F`: `Re (eqT a P) = a₀ + ξ + F`. -/
def lmF (a a₀ ξ η : ℝ) : ℝ := lmX2 a a₀ ξ η - (a₀ + ξ)

/-- The first factor of the vertical multiplier: `1 - 1/σ`. -/
def lmG1 (a a₀ ξ η : ℝ) : ℝ := 1 - (lmSig a a₀ ξ η)⁻¹

/-- The second factor of the vertical multiplier: `1 - 1/τ`. -/
def lmG2 (a a₀ ξ η : ℝ) : ℝ := 1 - (lmTau a a₀ ξ η)⁻¹

/-- The vertical multiplier at `(ξ,η)`: `Im (eqT a P) = η * G`. -/
def lmG (a a₀ ξ η : ℝ) : ℝ := lmG1 a a₀ ξ η * lmG2 a a₀ ξ η

/-- The vertical multiplier at the base point `A`. -/
def lmLam (a a₀ : ℝ) : ℝ := (1 - (lmS a a₀)⁻¹) * (1 - (lmT a a₀)⁻¹)

/-- `chordMap` on a point of the form `x + y i` with `x y : ℝ` and a real centre `c`. -/
lemma chordMap_ofReal_add (c x y : ℝ) :
    chordMap c (((x:ℝ):ℂ) + ((y:ℝ):ℂ)*I) =
      (((x - (x-c)/Real.sqrt ((x-c)^2+y^2)):ℝ):ℂ) +
        (((y - y/Real.sqrt ((x-c)^2+y^2)):ℝ):ℂ)*I := by
  have hnorm : ‖(((x:ℝ):ℂ) + ((y:ℝ):ℂ)*I - (c:ℂ))‖ = Real.sqrt ((x-c)^2+y^2) := by
    have h1 : (((x:ℝ):ℂ) + ((y:ℝ):ℂ)*I - (c:ℂ)) = (((x-c:ℝ):ℂ) + ((y:ℝ):ℂ)*I) := by
      push_cast; ring
    rw [h1, Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, sub_zero,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one, add_zero]
    ring_nf
  rw [chordMap, hnorm]
  have h1 : (((x:ℝ):ℂ) + ((y:ℝ):ℂ)*I - (c:ℂ)) = (((x-c:ℝ):ℂ) + ((y:ℝ):ℂ)*I) := by
    push_cast; ring
  rw [h1]
  push_cast
  ring

/-- The real-coordinate form of the two-step map is `X₂ + Y₂ i`. -/
theorem eqT_rep (a a₀ ξ η : ℝ) :
    eqT a (((a₀:ℝ):ℂ) + (ξ:ℂ) + (η:ℂ)*I) =
      ((a₀:ℝ):ℂ) + ((ξ + lmF a a₀ ξ η : ℝ):ℂ) + ((η * lmG a a₀ ξ η : ℝ):ℂ)*I := by
  have hO1 : O1_sym a = ((-(a/2):ℝ):ℂ) := by rw [O1_sym]; push_cast; ring
  have hO2 : O2_sym a = ((a/2:ℝ):ℂ) := rfl
  have h1 : (((a₀:ℝ):ℂ) + (ξ:ℂ) + (η:ℂ)*I) = (((a₀ + ξ:ℝ):ℂ) + ((η:ℝ):ℂ)*I) := by
    push_cast; ring
  rw [eqT, hO1, hO2, h1, chordMap_ofReal_add, chordMap_ofReal_add]
  simp only [lmF, lmG, lmG1, lmG2, lmX2, lmX1, lmV, lmTau, lmY1, lmSig, lmU]
  push_cast
  ring_nf

/-- `u = ξ - s`. -/
lemma lmU_eq (a a₀ ξ : ℝ) : lmU a a₀ ξ = ξ - lmS a a₀ := by
  simp only [lmU, lmS]; ring

/-- `lmY₁ = η * lmG₁`. -/
lemma lmY1_eq (a a₀ ξ η : ℝ) : lmY1 a a₀ ξ η = η * lmG1 a a₀ ξ η := by
  simp only [lmY1, lmG1]; ring

/-- `lmY₂ = η * lmG`. -/
lemma lmY2_eq (a a₀ ξ η : ℝ) : lmY2 a a₀ ξ η = η * lmG a a₀ ξ η := by
  simp only [lmY2, lmG, lmG1, lmG2, lmY1]; ring

/-- `lmF = (s - ξ)/σ - v/τ`. -/
lemma lmF_eq (a a₀ ξ η : ℝ) :
    lmF a a₀ ξ η = (lmS a a₀ - ξ)/lmSig a a₀ ξ η - lmV a a₀ ξ η / lmTau a a₀ ξ η := by
  simp only [lmF, lmX2, lmX1, lmU, lmS]; ring

/-- `σ² = u² + η²`. -/
lemma lmSig_sq (a a₀ ξ η : ℝ) : (lmSig a a₀ ξ η)^2 = (lmU a a₀ ξ)^2 + η^2 :=
  Real.sq_sqrt (by positivity)

/-- `τ² = v² + Y₁²`. -/
lemma lmTau_sq (a a₀ ξ η : ℝ) : (lmTau a a₀ ξ η)^2 = (lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2 :=
  Real.sq_sqrt (by positivity)

end

end Work.EQ
