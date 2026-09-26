import Mathlib
import Submission.Work.CKFinal.U0Defs
import Submission.Work.CKFinal.U0ArcSetup
import Submission.Work.CKFinal.gam1_smul_mem_DomainD
import Submission.Work.CKFinal.gam2_smul_mem_DomainD
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.CKFinal

open scoped MatrixGroups
open UpperHalfPlane

/-
THE GEOMETRY OF `U₀`: which points of `U₀` have an `SL(2,ℤ)`-translate on the imaginary axis.

`Work.CKFinal.U0` is the strip `-1 < Re τ < 1` minus the four closed discs of radius `1/4`
centred at `±1/4`, `±3/4`.  It is the union of the four open Farey triangles `(-1,0,∞)`, `(0,1,∞)`,
`(0,1/2,1)`, `(-1,-1/2,0)` together with their three common edges, the imaginary axis and the two
bottom arcs `|τ ∓ 1/2| = 1/2` (the geodesics `0 ↔ ±1`).  The `SL(2,ℤ)`-translates of `iℝ` are
exactly the Farey geodesics, and the only ones meeting `U₀` are those three.

NOTE (double-checked by two reviewers): the element `!![1,0;1,-1]` has determinant `-1`; the
element of `SL(2,ℤ)` with that Möbius action is its negative `!![1,0;-1,1]` (determinant `1`).
Similarly `!![1,0;1,1]` (determinant `1`) is the mirror.

ROUTE.  If `‖τ - 1/2‖ > 1/2` and `‖τ + 1/2‖ > 1/2` then `τ ∈ DomainD`
(`Work.Asymptotics.DomainD`) and `Work.Asymptotics.orbit_imagAxis_of_mem_DomainD` gives
`τ.re = 0`.  If `‖τ - 1/2‖ = 1/2` (resp. `‖τ + 1/2‖ = 1/2`) we are on an arc: return that
disjunct.  Otherwise `τ` lies in the open Farey triangle `(0,1/2,1)` (resp. `(-1,-1/2,0)`); use the
element `γ' = !![1,0;-1,1]` (resp. `!![1,0;1,1]`) of `SL(2,ℤ)`, whose Möbius action is
`τ ↦ τ/(1-τ)` (resp. `τ ↦ τ/(1+τ)`) and which maps that triangle onto `(0,1,∞) ⊆ DomainD`
(resp. `(-1,0,∞)`).  Apply `orbit_imagAxis_of_mem_DomainD` to `γ' • τ` with the element
`γ * γ'⁻¹` to get `(γ' • τ).re = 0`, then check by a coordinate computation that
`(γ' • τ).re = 0` is equivalent to `‖τ - 1/2‖ = 1/2` (resp. `‖τ + 1/2‖ = 1/2`).
The two "region" statements `τ ∈ U0 → ‖τ - 1/2‖ < 1/2 → γ' • τ ∈ DomainD` (and the mirror) are
elementary inequalities in `x = τ.re`, `y = τ.im`, using `x^2 + y^2 < x/2` together with the four
disc inequalities of `U0`.
-/
theorem orbit_imagAxis_of_mem_U0 (τ : UpperHalfPlane) (hτ : τ ∈ Work.CKFinal.U0)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : ((γ • τ : UpperHalfPlane) : ℂ).re = 0) :
    τ.re = 0 ∨ ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2 ∨ ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2 := by
  by_cases h1 : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2
  · exact Or.inr (Or.inl h1)
  by_cases h2 : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2
  · exact Or.inr (Or.inr h2)
  by_cases h3 : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2
  · -- `τ` lies strictly inside the Farey triangle `(0, 1/2, 1)`.  Then `Gam1 • τ ∈ 𝒟`, so
    -- `orbit_imagAxis_of_mem_DomainD` applies to the conjugate element `γ * Gam1⁻¹` and yields
    -- `(Gam1 • τ).re = 0`, which is equivalent to `‖τ - 1/2‖ = 1/2`, a contradiction.
    have hD : Gam1 • τ ∈ Work.Asymptotics.DomainD := gam1_smul_mem_DomainD τ hτ h3
    have hzero : (((Gam1 • τ : ℍ) : ℂ)).re = 0 := by
      have h' : (Gam1 • τ).re = 0 :=
        Work.Asymptotics.orbit_imagAxis_of_mem_DomainD (Gam1 • τ) hD (γ * Gam1⁻¹) (by
          rw [mul_smul, inv_smul_smul]; exact h)
      rwa [UpperHalfPlane.coe_re]
    exact Or.inr (Or.inl ((re_Gam1_smul_eq_zero_iff τ).mp hzero))
  by_cases h4 : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2
  · -- The mirror image of the previous case: `τ` lies in the triangle `(-1, -1/2, 0)` and
    -- `Gam2 • τ ∈ 𝒟`, which forces `‖τ + 1/2‖ = 1/2`.
    have hD : Gam2 • τ ∈ Work.Asymptotics.DomainD := gam2_smul_mem_DomainD τ hτ h4
    have hzero : (((Gam2 • τ : ℍ) : ℂ)).re = 0 := by
      have h' : (Gam2 • τ).re = 0 :=
        Work.Asymptotics.orbit_imagAxis_of_mem_DomainD (Gam2 • τ) hD (γ * Gam2⁻¹) (by
          rw [mul_smul, inv_smul_smul]; exact h)
      rwa [UpperHalfPlane.coe_re]
    exact Or.inr (Or.inr ((re_Gam2_smul_eq_zero_iff τ).mp hzero))
  · -- `τ` lies outside both open discs `‖τ ∓ 1/2‖ < 1/2`, hence in `𝒟` itself.
    have hAgt : 1 / 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ :=
      lt_of_le_of_ne (not_lt.mp h3) (fun hh => h1 hh.symm)
    have hBgt : 1 / 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ :=
      lt_of_le_of_ne (not_lt.mp h4) (fun hh => h2 hh.symm)
    exact Or.inl
      (Work.Asymptotics.orbit_imagAxis_of_mem_DomainD τ ⟨hτ.1, hτ.2.1, hAgt, hBgt⟩ γ h)

end Work.CKFinal
