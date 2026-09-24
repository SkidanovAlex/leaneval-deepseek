import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.fine_setup

/-!
# The window / tail decomposition of the far weight (shared definitions)

These are the objects used by `Work.GM.Affine.window_part_L2_estimate`,
`Work.GM.Affine.tail_part_bound` and the final assembly in
`Submission/Work/GM/Affine/far_part_reduction.lean`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `m₂`-sum `H(s) = Σ_{m₂∈R2 M₂} f(s/m₂)`, whose Fourier transform is `Bsum f M₂`. -/
def Hsum (M₂ : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := ∑ m ∈ R2 M₂, f (s / (m : ℝ))

/-- The window part of the far weight: `2/M₃ < |ℓ-y| ≤ B/M₃`. -/
def Wwin (K M₃ B y : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ,
    if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
      psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0

/-- The tail part of the far weight: `B/M₃ < |ℓ-y|` and `2/M₃ < |ℓ-y|`. -/
def Wtail (K M₃ B y : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ,
    if B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y| then
      psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0

/-- An integer bound for the `ℓ`-range of the window pairs. -/
def Lwin (T M₁ M₃ B : ℝ) : ℤ := ⌈T ^ 6 / M₁ + B / M₃⌉ + 1

/-- The window pairs `(m₁,ℓ)` at `ξ`. -/
def Pwin (T M₁ M₃ B : ℝ) (ξ : ℝ) : Finset (ℤ × ℤ) :=
  ((R1 M₁).product (Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B))).filter
    (fun p => 2 / M₃ < |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧
      |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ≤ B / M₃)

/-- The layer-`j` part of the window pair set: `2^j ≤ |M₃(ℓ-ξ/m₁)| < 2^(j+1)`. -/
def Pj (T M₁ M₃ B : ℝ) (ξ : ℝ) (j : ℕ) : Finset (ℤ × ℤ) :=
  (Pwin T M₁ M₃ B ξ).filter (fun p =>
    2 ^ j ≤ |M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧
      |M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))| < 2 ^ (j + 1))

/-- The summand attached to a pair `p = (m₁,ℓ)`. -/
def aTerm (K M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) (p : ℤ × ℤ) : ℂ :=
  ((|(p.1 : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (p.1 : ℝ)) *
    ((M₃ : ℂ) * psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))))

end

end Work.GM.Affine
