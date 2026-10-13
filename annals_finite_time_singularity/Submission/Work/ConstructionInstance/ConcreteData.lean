/-
# `Work.ConstructionInstance.ConcreteData` — the explicit inhabitant data

This module fixes the concrete data of the inhabited `ModulatedData` instance
(`ModulatedData`/`modulatedData_inhabited`, whose time horizon is `T = 1`); the *different*
inhabitant of `ProfileData` (`profileData_inhabited`) uses `g = 0`, `T = 2`,
`λ̄(t) = 1 - t/2` and is built directly in that module.  The two are unrelated interfaces.

* the modulation `lamZero t = (1-t)/2`;
* the zero perturbation `gZero`;
* the physical vorticity `omegaZero p x t = lamZero t⁻¹ • omegaSz p gZero (ρ(x)^p/lamZero t) x`
  (the exact self-similar ansatz with `g = 0`);
* the `St5` constant `cStar α = 3·Γ(p,π/4)/(4c(p))`, `p = profExp α = 3α`.

The facts recorded here are the elementary ones: the derivative of `lamZero`, its sign/bounds on
the windows, the positivity of `cStar`, the `St5` normalisation `cStar α · α = pΓ(p,π/4)/(4c(p))`,
and the `L^∞` box `lamZero t · ‖omegaZero p y t‖ ≤ 20p` in the self-similar variable.  The two
analytic boxes (`∂ₜω` and `St5`) are proved in the sibling modules
`omegaZero_dt_box` and `omegaZero_exists_low`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.ConstructionInstance.Boxes

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- The zero perturbation of the profile. -/
def gZero : ℝ → ℝ → ℝ := fun _ _ => 0

/-- The modulation `λ̄(t) = (1-t)/2` of the inhabited `ModulatedData` instance (`T = 1`).
(This is *not* the modulation of the `ProfileData` inhabitant, which is `λ̄(t) = 1 - t/2` with
`T = 2`.) -/
def lamZero : ℝ → ℝ := fun t => (1 - t) / 2

/-- **The explicit self-similar vorticity** of the inhabited instance: the self-similar ansatz
`ω(x,t) = λ̄(t)⁻¹·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)` with the zero perturbation, in the form of
`omegaSz`: `omegaZero p x t = lamZero t⁻¹ • omegaSz p gZero (ρ(x)^p/lamZero t) x`. -/
def omegaZero (p : ℝ) : R3 → ℝ → R3 :=
  fun x t => (lamZero t)⁻¹ • omegaSz p gZero (Work.Cyl.rho x ^ p / lamZero t) x

/-- **The `St5` constant** of the inhabited instance: `cStar α = 3Γ(p,π/4)/(4c(p))` with
`p = profExp α`, i.e. `cStar α · α = pΓ(p,π/4)/(4c(p))`, half the profile's value at the
maximising point `(z,θ) = (1,π/4)`. -/
def cStar (α : NNReal) : ℝ :=
  3 * Work.Spaces.Gam (profExp α) (Real.pi / 4) / (4 * Work.Spaces.c (profExp α))

@[simp] theorem gZero_apply (z θ : ℝ) : gZero z θ = 0 := rfl

@[simp] theorem lamZero_apply (t : ℝ) : lamZero t = (1 - t) / 2 := rfl

theorem omegaZero_apply (p : ℝ) (x : R3) (t : ℝ) :
    omegaZero p x t = (lamZero t)⁻¹ • omegaSz p gZero (Work.Cyl.rho x ^ p / lamZero t) x := rfl

/-- `∂_z` of the zero perturbation vanishes. -/
@[simp] theorem pz_gZero (z θ : ℝ) : Work.Spaces.pz gZero z θ = 0 := by
  simp [Work.Spaces.pz, gZero]

theorem hasDerivAt_lamZero' (t : ℝ) : HasDerivAt lamZero (-1 / 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := (hasDerivAt_id t).const_sub 1
  change HasDerivAt (fun s : ℝ => (1 - s) / 2) (-1 / 2) t
  exact h1.div_const 2

theorem deriv_lamZero (t : ℝ) : deriv lamZero t = -1 / 2 :=
  (hasDerivAt_lamZero' t).deriv

theorem hasDerivAt_lamZero (t : ℝ) : HasDerivAt lamZero (deriv lamZero t) t := by
  have h2 := hasDerivAt_lamZero' t
  exact h2.congr_deriv h2.deriv.symm

theorem abs_deriv_lamZero_le (t : ℝ) : |deriv lamZero t| ≤ 1 / 2 := by
  rw [deriv_lamZero t]; norm_num

theorem lamZero_pos {t : ℝ} (ht : t < 1) : 0 < lamZero t := by
  rw [lamZero_apply]; linarith

theorem lamZero_nonneg {t : ℝ} (ht : t ≤ 1) : 0 ≤ lamZero t := by
  rw [lamZero_apply]; linarith

theorem cStar_pos {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    0 < cStar α := by
  have hp : 0 < profExp α := profExp_pos hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith
  have hc := (Work.Spaces.c_bounds (profExp α) hp hp1).1
  have hcpos : 0 < Work.Spaces.c (profExp α) := by linarith
  have hGam : 0 < Work.Spaces.Gam (profExp α) (Real.pi / 4) := by
    rw [Work.Spaces.Gam]
    refine Real.rpow_pos_of_pos ?_ _
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    norm_num
  rw [cStar]
  positivity

theorem cStar_mul_alpha (α : NNReal) :
    cStar α * (α : ℝ)
      = profExp α * Work.Spaces.Gam (profExp α) (Real.pi / 4)
          / (4 * Work.Spaces.c (profExp α)) := by
  rw [cStar, profExp]; ring

/-- **The `L^∞` box in the self-similar variable** for the explicit data: with `g = 0` the
perturbation bound is `Cg = 0`, so `lamZero t · ‖omegaZero p y t‖ ≤ 20p`. -/
theorem lamZero_mul_omegaZero_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ t ∈ Set.Ioo (-2) (1 : ℝ), ∀ y : R3, lamZero t * ‖omegaZero p y t‖ ≤ 20 * p := by
  intro t ht y
  have hlt : 0 < lamZero t := lamZero_pos ht.2
  rw [omegaZero_apply, mul_norm_inv_smul hlt]
  have h := omegaSz_norm_le (g := gZero) (Cg := 0) hp hp1 (le_refl (0 : ℝ))
    (by intro z θ hz hθ; simp)
    (div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg y) p) hlt.le) y
  simpa using h

end Work.ConstructionInstance
