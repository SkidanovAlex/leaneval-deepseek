import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.PhiSplit

/-!
# The `Sm1`-slice: `Sm1 = Sm1Ref + dSm1`

Building on `PhiSplit`, this module splits `K24F.Sm1` into an explicit *reference* expression
(a polynomial in `E = Ept z` over the `τ`-atoms and `S0z z`) plus an explicit *deviation* sum,
each summand of which is one of `dPhi`, `dE4c`, `dI4`, `dDinv` times a reference cofactor.

The three pieces of `Sm1` are handled as follows.

* `j(τ)(Φ - Φ_ref)`: split `Φ = PhiRef + dPhi`, giving `j(τ)(PhiRef - Φ_ref) + j(τ)·dPhi`.
* `E₄(z)³ Q₁ (q/Δ - 1)`: with `1/Δ = DeltaInvRef + dDinv` (`DeltaInvRef = q⁻¹ + 24`), one has
  `q/Δ - 1 = (q·DeltaInvRef - 1) + q·dDinv`, and `E₄(z)³ = E4Ref³ + dE4c`.
* `E₄(z)³ (Φ - Φ_ref - qQ₁)/Δ`: with `Φ - Φ_ref - qQ₁ = W0' + dPhi` (where `W0'` is its
  reference value) and `1/Δ = DeltaInvRef + dDinv`.

The single identity `Sm1 = Sm1Ref + dSm1` is then a polynomial identity in the atoms
(`q`, `q⁻¹`, `E₄(z)`, `E4Ref z`, `dE4 z`, `E2S`, `E2SRef`, `E14Fun`, …), verified by `ring`
after the atom splits of `KPlus24Refs`/`PhiSplit`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

set_option maxRecDepth 4000

/-- Reference value of `Δ(z)⁻¹` in the `q`-variable: `q⁻¹ + 24`. -/
def DeltaInvRef (z : ℍ) : ℂ := (Work.Kernels.qParamFun z)⁻¹ + 24

/-- Deviation of `Δ(z)⁻¹` from `DeltaInvRef`. -/
def Donly (z : ℍ) : ℂ := (Work.Kernels.DeltaFun z)⁻¹ - DeltaInvRef z

lemma DeltaFun_inv_ref_split (z : ℍ) :
    (Work.Kernels.DeltaFun z)⁻¹ = DeltaInvRef z + Donly z := by
  simp only [Donly]; ring

/-- Deviation of `E₄(z)³`, written as `(E₄ - E4Ref)·(E₄² + E₄·E4Ref + E4Ref²)`. -/
def dE4c (z : ℍ) : ℂ :=
  dE4 z * (Work.Kernels.E4Fun z ^ 2 + Work.Kernels.E4Fun z * E4Ref z + E4Ref z ^ 2)

lemma E4Fun_cube_ref_add (z : ℍ) :
    Work.Kernels.E4Fun z ^ 3 = E4Ref z ^ 3 + dE4c z := by
  simp only [dE4c, dE4]; ring

/-- Reference value of `Φ - Φ_ref - q Q₁`. -/
def W0' (τ z : ℍ) : ℂ := PhiRef τ z - Work.Asymptotics.K24F.Phiref τ z
  - Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Q1 τ z

/-- `Φ - Φ_ref - q Q₁` itself. -/
def W1' (τ z : ℍ) : ℂ := Work.Asymptotics.K24F.Phi τ z - Work.Asymptotics.K24F.Phiref τ z
  - Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Q1 τ z

/-- The reference part of `K24F.Sm1`. -/
def Sm1Ref (τ z : ℍ) : ℂ :=
  Work.Kernels.jInvariantFun τ * (PhiRef τ z - Work.Asymptotics.K24F.Phiref τ z)
    - E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z
        * (Work.Kernels.qParamFun z * DeltaInvRef z - 1)
    - E4Ref z ^ 3 * W0' τ z * DeltaInvRef z

/-- The deviation part of `K24F.Sm1`. -/
def dSm1 (τ z : ℍ) : ℂ :=
  Work.Kernels.jInvariantFun τ * dPhi τ z
    - (dE4c z * Work.Asymptotics.K24F.Q1 τ z
          * (Work.Kernels.qParamFun z * DeltaInvRef z - 1)
        + E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z
            * (Work.Kernels.qParamFun z * Donly z)
        + dE4c z * Work.Asymptotics.K24F.Q1 τ z
            * (Work.Kernels.qParamFun z * Donly z))
    - (E4Ref z ^ 3 * dPhi τ z * DeltaInvRef z + dE4c z * W1' τ z * DeltaInvRef z
        + E4Ref z ^ 3 * W1' τ z * Donly z + dE4c z * W1' τ z * Donly z)

/-! ## The three summand identities

`Sm1` is `j(τ)(Φ - Φ_ref) - E₄(z)³Q₁(q/Δ - 1) - E₄(z)³(Φ - Φ_ref - qQ₁)/Δ`.  Each summand is
split on its own — small enough for a single `ring` — and the three are then combined. -/

/-- Summand 1: `j(τ)(Φ - Φ_ref)`. -/
lemma Sm1_term1 (τ z : ℍ) :
    Work.Kernels.jInvariantFun τ
        * (Work.Asymptotics.K24F.Phi τ z - Work.Asymptotics.K24F.Phiref τ z)
      = Work.Kernels.jInvariantFun τ
          * (PhiRef τ z - Work.Asymptotics.K24F.Phiref τ z)
        + Work.Kernels.jInvariantFun τ * dPhi τ z := by
  rw [Phi_eq_ref_add τ z]; ring

/-- Summand 2: `E₄(z)³ Q₁ (q/Δ - 1)`. -/
lemma Sm1_term2 (τ z : ℍ) :
    Work.Kernels.E4Fun z ^ 3 * Work.Asymptotics.K24F.Q1 τ z
        * (Work.Kernels.qParamFun z / Work.Kernels.DeltaFun z - 1)
      = E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z
          * (Work.Kernels.qParamFun z * DeltaInvRef z - 1)
        + (dE4c z * Work.Asymptotics.K24F.Q1 τ z
              * (Work.Kernels.qParamFun z * DeltaInvRef z - 1)
            + E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z
                * (Work.Kernels.qParamFun z * Donly z)
            + dE4c z * Work.Asymptotics.K24F.Q1 τ z
                * (Work.Kernels.qParamFun z * Donly z)) := by
  rw [div_eq_mul_inv, DeltaFun_inv_ref_split z, E4Fun_cube_ref_add z]
  ring

/-- `Φ - Φ_ref - qQ₁ = W0' + dPhi`, i.e. the reference/deviation split of `W1'`. -/
lemma W1'_eq (τ z : ℍ) : W1' τ z = W0' τ z + dPhi τ z := by
  simp only [W1', W0']
  rw [Phi_eq_ref_add τ z]
  ring

/-- Summand 3: `E₄(z)³(Φ - Φ_ref - qQ₁)/Δ`. -/
lemma Sm1_term3 (τ z : ℍ) :
    Work.Kernels.E4Fun z ^ 3
        * (Work.Asymptotics.K24F.Phi τ z - Work.Asymptotics.K24F.Phiref τ z
          - Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Q1 τ z)
        / Work.Kernels.DeltaFun z
      = E4Ref z ^ 3 * W0' τ z * DeltaInvRef z
        + (E4Ref z ^ 3 * dPhi τ z * DeltaInvRef z + dE4c z * W1' τ z * DeltaInvRef z
            + E4Ref z ^ 3 * W1' τ z * Donly z + dE4c z * W1' τ z * Donly z) := by
  have hW1 : Work.Asymptotics.K24F.Phi τ z - Work.Asymptotics.K24F.Phiref τ z
      - Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Q1 τ z = W1' τ z := rfl
  have hW := W1'_eq τ z
  rw [hW1, div_eq_mul_inv, DeltaFun_inv_ref_split z, E4Fun_cube_ref_add z, hW]
  ring

/-- **The `Sm1`-split**: `Sm1 = Sm1Ref + dSm1`, exactly. -/
lemma Sm1_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Sm1 τ z = Sm1Ref τ z + dSm1 τ z := by
  have h1 := Sm1_term1 τ z
  have h2 := Sm1_term2 τ z
  have h3 := Sm1_term3 τ z
  simp only [Work.Asymptotics.K24F.Sm1, Sm1Ref, dSm1]
  rw [h1, h2, h3]
  ring

end

end Work.Asymptotics.KhatE1Core
