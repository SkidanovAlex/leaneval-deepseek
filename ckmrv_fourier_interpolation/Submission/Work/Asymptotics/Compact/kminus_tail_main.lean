/-
# The cusp-`i∞` tail estimate for `K_-`

This file assembles the tail estimate: for `τ` in a compact `K ⊆ 𝒟` and `z` with large imaginary
part,

  `K_-^{(d)}(τ,z) = 𝒢_-^{(d)}(τ,z) + O((1+‖z‖)·‖Ept z‖)`.

The proof uses the exact identity `3456π(K_- - 𝒢_-) = -(Sh)⁻¹(br + Sh·br0)` of
`kminus_tail_core`, the decomposition of `(Sh)⁻¹(br + Sh br0)` into the reference part `Tref`
(whose explicit expansion starts at order `e¹`, whence `Tref = e·R` with `R` bounded, cf.
`norm_Tref*_le`) and seven deviation terms `Dev1, …, Dev7` whose bounds come from the cusp
expansion lemmas.
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_bounds

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.Compact

open Work.Kernels
open Work.Residues (Ept Ept_ne_zero)

/-! ## The decomposition of `(Sh)⁻¹ (br + Sh br0)` -/

def Dev1 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  Sinvref τ z * Dref z * (A24 ℓ τ z - A24ref ℓ τ z)
def Dev2 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ := Sinvref τ z * dDelta z * A24 ℓ τ z
def Dev3 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ := dSinv τ z * (DeltaFun z)⁻¹ * A24 ℓ τ z
def Dev4 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ := Sinvref τ z * C24 ℓ τ * dW z
def Dev5 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ := dSinv τ z * C24 ℓ τ * WFun z
def Dev6 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ := -Dref z * dW z * B24 ℓ τ
def Dev7 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ := -dDelta z * WFun z * B24 ℓ τ

/-- `(-(ab))⁻¹ b = -a⁻¹`. -/
lemma inv_neg_mul_mul_cancel {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) : (-(a * b))⁻¹ * b = -a⁻¹ := by
  have h : a * b ≠ 0 := mul_ne_zero ha hb
  field_simp

/-- `(Sh τ z)⁻¹ (j τ - j z) = -(Δ z)⁻¹` when `Sh τ z ≠ 0`. -/
lemma inv_Sh_mul_J (τ z : ℍ) (hS : Sh τ z ≠ 0) :
    (Sh τ z)⁻¹ * (jInvariantFun τ - jInvariantFun z) = -(DeltaFun z)⁻¹ := by
  have hΔ : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := by
    intro h
    exact hS (by rw [Sh_eq τ z, h, mul_zero, neg_zero])
  have h1 : Sh τ z = -(DeltaFun z * (jInvariantFun τ - jInvariantFun z)) := Sh_eq τ z
  rw [h1]
  exact inv_neg_mul_mul_cancel hΔ hJ

/-- **The decomposition.**  For `Sh τ z ≠ 0` the quantity `(Sh)⁻¹(br + Sh·br0)` is the sum of
the reference part `Tref24` and the seven deviation terms. -/
lemma decomp24 (ℓ : LogLambdaData) (τ z : ℍ) (hS : Sh τ z ≠ 0) :
    (Sh τ z)⁻¹ * (brMinus ℓ 24 τ z + Sh τ z * br0 24 ℓ τ z)
      = Tref24 ℓ τ z + (Dev1 ℓ τ z + Dev2 ℓ τ z + Dev3 ℓ τ z + Dev4 ℓ τ z
          + Dev5 ℓ τ z + Dev6 ℓ τ z + Dev7 ℓ τ z) := by
  have hJ := inv_Sh_mul_J τ z hS
  have hSh : (Sh τ z)⁻¹ * (Sh τ z * br0 24 ℓ τ z) = br0 24 ℓ τ z := by
    rw [← mul_assoc, inv_mul_cancel₀ hS, one_mul]
  have e1 : (Sh τ z)⁻¹ * ((DeltaFun z)⁻¹ * A24 ℓ τ z)
      = Sinvref τ z * Dref z * A24ref ℓ τ z + Dev1 ℓ τ z + Dev2 ℓ τ z + Dev3 ℓ τ z := by
    simp only [Dev1, Dev2, Dev3, dSinv, dDelta, Dref]
    ring
  have e2 : (Sh τ z)⁻¹ * (C24 ℓ τ * WFun z)
      = C24 ℓ τ * Sinvref τ z * Wref z + Dev4 ℓ τ z + Dev5 ℓ τ z := by
    simp only [Dev4, Dev5, dSinv, dW, Wref]
    ring
  have e3 : (Sh τ z)⁻¹ * ((jInvariantFun τ - jInvariantFun z) * WFun z * B24 ℓ τ)
      = -(Dref z * Wref z * B24 ℓ τ) + Dev6 ℓ τ z + Dev7 ℓ τ z := by
    rw [show (Sh τ z)⁻¹ * ((jInvariantFun τ - jInvariantFun z) * WFun z * B24 ℓ τ)
        = (Sh τ z)⁻¹ * (jInvariantFun τ - jInvariantFun z) * (WFun z * B24 ℓ τ) from by ring, hJ]
    simp only [Dev6, Dev7, dDelta, Dref, dW, Wref]
    ring
  rw [mul_add, hSh, brMinus_24_decomp, mul_add, mul_add, e1, e2, e3]
  simp only [Tref24]
  ring

/-! ## The deviation sums

We collect the deviations of `(Sh)⁻¹(br + Sh·br0)` from its reference part `Tref` into single
sums, one per dimension. -/

/-- The sum of the seven deviation terms of dimension `24`. -/
def Dev24Sum (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  Dev1 l τ z + Dev2 l τ z + Dev3 l τ z + Dev4 l τ z + Dev5 l τ z + Dev6 l τ z + Dev7 l τ z

/-- The decomposition of dimension `24` with the deviations collected. -/
lemma decomp24_sum (ℓ : LogLambdaData) (τ z : ℍ) (hS : Sh τ z ≠ 0) :
    (Sh τ z)⁻¹ * (brMinus ℓ 24 τ z + Sh τ z * br0 24 ℓ τ z)
      = Tref24 ℓ τ z + Dev24Sum ℓ τ z := by
  rw [decomp24 ℓ τ z hS]
  simp only [Dev24Sum]

/-! ## The deviations in dimension `8`

The `d = 8` bracket uses the `z`-atoms `E₁₀, 𝓛, E₈, W, E₆, U²-V²`, so its deviations involve
`dE10, dL, dE8, dW, dE6, dD2` in the three possible combinations (`ref·dev`, `dev·ref`,
`dev·dev`).  Writing `br8 = br8ref + Dev8Raw` for the raw atom-by-atom deviations, the factor
`(Sh)⁻¹ = Sinvref + dSinv` acts on both pieces, which gives `Dev8Sum` below. -/

def DevA1 (l : LogLambdaData) (τ z : ℍ) : ℂ := -3456 * E4Fun τ * E10ref z * dL l z
def DevA2 (l : LogLambdaData) (τ z : ℍ) : ℂ := -3456 * E4Fun τ * dE10 z * Lref l z
def DevA3 (l : LogLambdaData) (τ z : ℍ) : ℂ := -3456 * E4Fun τ * dE10 z * dL l z
def DevB1 (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  psi2 l τ * (E14Fun τ / DeltaFun τ) * (E8ref z * dW z - E6ref z * dD2 z)
def DevB2 (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  psi2 l τ * (E14Fun τ / DeltaFun τ) * (dE8 z * Wref z - dE6 z * D2ref z)
def DevB3 (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  psi2 l τ * (E14Fun τ / DeltaFun τ) * (dE8 z * dW z - dE6 z * dD2 z)
def DevC1 (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  psi4 l τ * ((1728 - jInvariantFun τ) * E8ref z * dW z + jInvariantFun τ * E6ref z * dD2 z)
def DevC2 (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  psi4 l τ * ((1728 - jInvariantFun τ) * dE8 z * Wref z + jInvariantFun τ * dE6 z * D2ref z)
def DevC3 (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  psi4 l τ * ((1728 - jInvariantFun τ) * dE8 z * dW z + jInvariantFun τ * dE6 z * dD2 z)

/-- The raw atom-by-atom deviations of `brMinus 8` from `br8ref`. -/
def Dev8Raw (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  DevA1 l τ z + DevA2 l τ z + DevA3 l τ z + DevB1 l τ z + DevB2 l τ z + DevB3 l τ z
    + DevC1 l τ z + DevC2 l τ z + DevC3 l τ z

/-- The deviations of `(Sh)⁻¹(br8 + Sh·br0)` from `Tref8` in dimension `8`. -/
def Dev8Sum (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  dSinv τ z * br8ref l τ z + Sinvref τ z * Dev8Raw l τ z + dSinv τ z * Dev8Raw l τ z

/-- The identity `brMinus 8 = br8ref + Dev8Raw`. -/
lemma brMinus8_decomp (ℓ : LogLambdaData) (τ z : ℍ) :
    brMinus ℓ 8 τ z = br8ref ℓ τ z + Dev8Raw ℓ τ z := by
  simp only [brMinus_eight, Work.Residues.bracket8e, br8ref, Dev8Raw, DevA1, DevA2, DevA3,
    DevB1, DevB2, DevB3, DevC1, DevC2, DevC3, dE8, dE6, dE10, dL, dW, dD2, c1728]
  ring

/-- The decomposition of dimension `8` with the deviations collected. -/
lemma decomp8 (ℓ : LogLambdaData) (τ z : ℍ) (hS : Sh τ z ≠ 0) :
    (Sh τ z)⁻¹ * (brMinus ℓ 8 τ z + Sh τ z * br0 8 ℓ τ z)
      = Tref8 ℓ τ z + Dev8Sum ℓ τ z := by
  have hSh : (Sh τ z)⁻¹ * (Sh τ z * br0 8 ℓ τ z) = br0 8 ℓ τ z := by
    rw [← mul_assoc, inv_mul_cancel₀ hS, one_mul]
  have hsplit : (Sh τ z)⁻¹ = Sinvref τ z + dSinv τ z := by rw [dSinv]; ring
  have e : (Sh τ z)⁻¹ * br8ref ℓ τ z + (Sh τ z)⁻¹ * Dev8Raw ℓ τ z
      = Sinvref τ z * br8ref ℓ τ z + Dev8Sum ℓ τ z := by
    rw [hsplit, Dev8Sum]; ring
  rw [mul_add, hSh, brMinus8_decomp, mul_add, e]
  simp only [Tref8]
  ring


end Work.Asymptotics.Compact
