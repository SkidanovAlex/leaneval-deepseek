/-
# `Work.FTS.RegPkgGal.Der.jet_LGammaT`

The `Jet`-regularity of the linearized-with-transport coercivity operator `𝓛_Γ^T` of Elgindi's
paper (`Work.Coercivity.LGammaT`), evaluated on the `τ`-slice `g(·,·,τ)` of the profile
perturbation.  This is the node `Der.jet_LGammaT` of the R5 program of
`Submission/Work/FTS/RegPkgGal/NOTES_RegPkgGal.md` §14: the `Jet` of the first constituent
`-𝓛_Γ^T(g)(τ)` of the right-hand side of the fake-time equation.

The argument is the `Jet`-calculus of `Submission/Work/FTS/Regularity/regPkg_inhabited.lean`
(`Jet.add`, `Jet.neg`, `Jet.mul`) applied to the expansion of `𝓛_Γ^T` into its five elementary
pieces (`LGammaT_eq_expansion` below):

    𝓛_Γ^T(f) = f + D_z f - 2f/(1+z) - (2zΓ/(c(1+z)²))·L₁₂(f)
                  - 3D_θf/(1+z) + (Γ/c)(2z²/(1+z)³)·L₁₂(Transport f)(0),

together with the elementary boundedness/`α`-Hölder estimates of the coefficient functions

* `z ↦ 2/(1+z)`, `z ↦ 3/(1+z)`, `z ↦ 2z/(1+z)²`,
* `θ ↦ Γ(θ)/c(3α)`,
* the `(z,θ)`-coefficient `2zΓ(θ)/(c(3α)(1+z)²)` of the `L₁₂`-term,
* and `AK (pExp α) = (Γ(θ)/c(3α))·2z²/(1+z)³`,

which are collected in the companion module `Submission.Work.FTS.RegPkgGal.Der.jet_coeff_all`
(`Work.FTS.RegPkgGal.Der.jet_coeff_all`), proved in parallel.  This file is the *assembly*: the
expansion, the `Jet`-calculus, and the identification of the two `L₁₂`-arguments with the given
hypotheses.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.regPkg_inhabited
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.RegPkgGal.Der.rhs_jet_aux
import Submission.Work.FTS.RegPkgGal.Der.jet_coeff_all

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The pointwise expansion of `𝓛_Γ^T` -/

/-- The operator `𝓛_Γ^T = 𝓛_Γ - 𝕡∘Transport` written out in its five elementary pieces:
the two `𝓛`-terms, the `L₁₂`-term with the coefficient `2zΓ(θ)/(c(α)(1+z)²)`, the angular
transport term `3D_θf/(1+z)`, and the projection correction with the coefficient
`(Γ(θ)/c(α))·2z²/(1+z)³`. -/
theorem LGammaT_eq_expansion (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.LGammaT α f z θ
      = f z θ + Work.Spaces.Dz f z θ - (2 / (1 + z)) * f z θ
        - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
            * Work.Coercivity.L12f f z
        - (3 / (1 + z)) * Work.Spaces.Dth f z θ
        + (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.Proj,
    Work.Coercivity.Transport, Work.Coercivity.L]
  ring

/-! ## 2. The `Jet` of `𝓛_Γ^T(g(τ))` -/

theorem jet_LGammaT {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hg : Work.FTS.Regularity.Jet α S N₁ g)
    (hDzg : Work.FTS.Regularity.Jet α S N₂ (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hDthg : Work.FTS.Regularity.Jet α S N₃ (fun z θ τ => Work.Spaces.Dth (fun z θ => g z θ τ) z θ))
    (hL12 : Work.FTS.Regularity.Jet α S N₄
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z))
    (hL12T : Work.FTS.Regularity.Jet α S N₅
      (fun z θ τ => Work.Coercivity.L12f
        (fun z θ' => 3 * Work.Spaces.Dth (fun z θ => g z θ τ) z θ' / (1 + z)) 0)) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z θ) := by
  -- the given `Jet`s, in the `gSlice`-form in which the expansion of `𝓛_Γ^T` is written
  have hg' : Work.FTS.Regularity.Jet α S N₁
      (fun z θ τ => Work.FTS.Regularity.gSlice g τ z θ) := hg
  have hDz' : Work.FTS.Regularity.Jet α S N₂
      (fun z θ τ => Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ) := hDzg
  have hDth' : Work.FTS.Regularity.Jet α S N₃
      (fun z θ τ => Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ) := hDthg
  have hL12' : Work.FTS.Regularity.Jet α S N₄
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z) := hL12
  have hL12T' : Work.FTS.Regularity.Jet α S N₅
      (fun z θ τ => Work.Coercivity.L12f
        (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0) := hL12T
  -- the coefficient estimates (the `jet_coeff_all` aggregation)
  obtain ⟨_, h2, h3, _, hcoef, hAK0⟩ := jet_coeff_all (S := S) hα hα13
  have hAK' : Work.FTS.Regularity.Jet α S 100
      (fun z θ _ => (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * (2 * z ^ 2 / (1 + z) ^ 3)) :=
    rhsJet_congr (fun z θ τ => rfl) hAK0
  -- the five pieces of the expansion, as `Jet`s of the family `(z,θ,τ) ↦ ·(z,θ)`
  have Pg := Work.FTS.Regularity.Jet.mul (Work.FTS.Regularity.Jet.neg h2) hg'
  have P12 := Work.FTS.Regularity.Jet.mul hcoef hL12'
  have Pth := Work.FTS.Regularity.Jet.mul (Work.FTS.Regularity.Jet.neg h3) hDth'
  have PAK := Work.FTS.Regularity.Jet.mul hAK' hL12T'
  -- the sum, in the order of the expansion
  have hE := Work.FTS.Regularity.Jet.add
    (Work.FTS.Regularity.Jet.add
      (Work.FTS.Regularity.Jet.add
        (Work.FTS.Regularity.Jet.add
          (Work.FTS.Regularity.Jet.add hg' hDz')
          Pg)
        (Work.FTS.Regularity.Jet.neg P12))
      Pth)
    PAK
  refine ⟨_, rhsJet_congr (fun z θ τ => ?_) hE⟩
  rw [LGammaT_eq_expansion]
  field_simp
  ring

end Work.FTS.RegPkgGal.Der
