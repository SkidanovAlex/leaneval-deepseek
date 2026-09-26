import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm45Split

/-!
# The `Sm3`-slice: `Sm3 = Sm3Ref + dSm3`

`Sm3 = 3456·R₀(τ)·(E₄(z)³·S0(z) - E₆(z)E₂ˢ(z)/E₄(z))`.

The third summand is the only place where a plain `1/E₄(z)` (rather than `E₄(z)³`) occurs, so
this slice introduces its reference `I4zRef = 1 - 240q + 55440q²` together with
`dI4z = (E₄(z))⁻¹ - I4zRef`.  (The `q²`-coefficient check: `1/(1+240q+2160q²) = 1 - 240q +
(240² - 2160)q² = 1 - 240q + 55440q²`.)

With `E₄(z)³ = E4Ref³ + dE4c`, `E₆(z) = E6Ref + dE6`, `E₂ˢ(z) = E2SRef + dE2S` and
`(E₄(z))⁻¹ = I4zRef + dI4z`, the product `E₆(z)E₂ˢ(z)/E₄(z)` is `E6Ref·E2SRef·I4zRef` plus

  `dE6·E₂ˢ/E₄ + E6Ref·dE2S/E₄ + E6Ref·E2SRef·dI4z`,

since `dE6·E₂ˢ·(E₄)⁻¹ + E6Ref·dE2S·(E₄)⁻¹` expands to the six cross terms and
`E6Ref·E2SRef·dI4z` is the seventh.  Hence

  `Sm3Ref = 3456 R₀ (E4Ref³·S0 - E6Ref·E2SRef·I4zRef)`,
  `dSm3   = 3456 R₀ (dE4c·S0 - (dE6·E₂ˢ·(E₄)⁻¹ + E6Ref·dE2S·(E₄)⁻¹ + E6Ref·E2SRef·dI4z))`.

Every summand is again one deviation times a reference cofactor.  Note `E4Ref³·S0 ≈ S0` and
`E6Ref·E2SRef·I4zRef ≈ S0`, so `Sm3Ref` starts at order `E²` (the leading `S0` parts cancel
exactly) — which is why `KhatE1Z.E6_E2S_div_E4_second_three` (the proved cusp expansion of
`E₆E₂ˢ/E₄`) is the natural input for bounding `dSm3`; the bound of `dI4z` is the one small new
obligation this slice introduces.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- Reference value of `(E₄(z))⁻¹` at the cusp. -/
def I4zRef (z : ℍ) : ℂ := 1 - 240 * Work.Kernels.qParamFun z
  + 55440 * (Work.Kernels.qParamFun z) ^ 2

/-- Deviation of `(E₄(z))⁻¹` from `I4zRef`. -/
def dI4z (z : ℍ) : ℂ := (Work.Kernels.E4Fun z)⁻¹ - I4zRef z

lemma E4Fun_inv_ref_add (z : ℍ) :
    (Work.Kernels.E4Fun z)⁻¹ = I4zRef z + dI4z z := by
  simp only [dI4z]; ring

/-- The reference part of `K24F.Sm3`. -/
def Sm3Ref (τ z : ℍ) : ℂ :=
  3456 * Work.Asymptotics.K24F.R0 τ
    * (E4Ref z ^ 3 * Work.Asymptotics.K24F.S0 z
        - E6Ref z * E2SRef z * I4zRef z)

/-- The deviation part of `K24F.Sm3`. -/
def dSm3 (τ z : ℍ) : ℂ :=
  3456 * Work.Asymptotics.K24F.R0 τ
    * (dE4c z * Work.Asymptotics.K24F.S0 z
        - (dE6 z * Work.Kernels.E2S z * (Work.Kernels.E4Fun z)⁻¹
            + E6Ref z * dE2S z * (Work.Kernels.E4Fun z)⁻¹
            + E6Ref z * E2SRef z * dI4z z))

/-- **The `Sm3`-split**: `Sm3 = Sm3Ref + dSm3`, exactly. -/
lemma Sm3_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Sm3 τ z = Sm3Ref τ z + dSm3 τ z := by
  have hE4 := E4Fun_cube_ref_add z
  have hE6 := E6Fun_ref_split z
  have hE2S := E2S_ref_split z
  have hI4 := E4Fun_inv_ref_add z
  simp only [Work.Asymptotics.K24F.Sm3, Sm3Ref, dSm3]
  simp only [div_eq_mul_inv]
  rw [hE4, hE6, hE2S, hI4]
  ring

end

end Work.Asymptotics.KhatE1Core
