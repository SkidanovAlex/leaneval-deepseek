/-
# `Work.FTS.MeridianDyn.Const` — the constant-rate case (sanity check)

The design (`FTS_PHYS_BRIDGE.md` §3, item 9) requires that the dynamic profile equation `(E)`
*reproduce* the constant-rate profile equation `Work.CoreResiduals.DynEqConst p (2κ) 1 F Φ` of the
Construction area, the equation that `Work.CoreResiduals.meridianEq_of_dynEqConst` reduces the
meridian equation to.

Contents:

* `ssVort_eq_dynVort`, `ssPsi_eq_dynPsi` — the constant-rate self-similar pair of
  `Work.CoreResiduals` is *definitionally* the dynamical ansatz `dynVort`/`dynPsi` at amplitude
  `λ⁻¹`, scale `λ` and clock `σ = id`;
* `dynEqF_const_iff` — `(E)` for a `τ`-independent profile at constant modulation `μ` is the
  pointwise profile equation `(1+μ)F + (1-μ)·D_zF + UVR α F Φ = 0`;
* `dynEqF_const_iff_DynEqConst` — **the sanity check**: at `μ ≡ 0` this is exactly
  `Work.CoreResiduals.DynEqConst p 1 1 F Φ`, i.e. `DynEqConst p (2κ) 1 F Φ` at the model rate
  `2κ = 1` (whose `κ = 1/2 = -λ̄'` is the rate of the paper's model `λ̄ = 1 - t/2`, the rate at
  which `Work.CoreResiduals.meridianEq_of_dynEqConst` is applied at the inhabitant);
* `dynEqF_const_mu_iff` — the general constant-modulation case: with `λ = lamfun μ₀` (so that
  `b = 1+λ = (1-μ₀)/(1+μ₀)`), `(E)` is `DynEqConst p (1+μ₀) (1+lamfun μ₀) F Φ`.

## A remark on the clock normalisation

The meridian identity `meridianResid_dyn` additionally assumes the *clock normalisation*
`2σ'(t) = a(t)` (the algebraic form of the design's `C.A = 2A_v` in the reconstruction).  That
normalisation is *not* compatible with the constant-rate parametrisation `σ = id` together with a
constant amplitude: it forces `a' = (1+μ)σ'a = (1+μ)a/2`, i.e. the amplitude grows like
`e^{(1+μ)t/2}`, and correspondingly the constant-rate residual identity reads
`resid = a σ' (F_τ + (1+μ)F + (1-μ)D_zF) + (a²/2)·UVR` (see `ResidDyn.meridianResid_dyn`, which is
proved for arbitrary data satisfying `a' = (1+μ)σ'a`, `b'/b = -(1-μ)σ'` and `2σ' = a`).  The
constant-rate comparison with `Work.CoreResiduals.meridianResid_algebra` is therefore carried by
the *algebraic core* `Algebra.meridianResid_algebra_dyn`, whose non-linear part is exactly
`(a²/2)·UVR` — the same coefficient `(2λ²)⁻¹` as in the constant-rate identity with `λ = a⁻¹`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.ResidDyn
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-! ## The self-similar pair of `CoreResiduals` as an instance of the dynamical ansatz -/

/-- The constant-rate self-similar vorticity `Work.CoreResiduals.ssVort` is the dynamical ansatz
`dynVort` at amplitude `λ⁻¹`, scale `λ`, clock `id` and `τ`-independent profile. -/
theorem ssVort_eq_dynVort (p : ℝ) (lam : ℝ → ℝ) (F : ℝ → ℝ → ℝ) :
    Work.CoreResiduals.ssVort p lam F
      = dynVort p (fun t => (lam t)⁻¹) lam id (fun z θ _ => F z θ) := rfl

/-- The constant-rate self-similar stream function `Work.CoreResiduals.ssPsi` is the dynamical
ansatz `dynPsi` at amplitude `λ⁻¹`, scale `λ`, clock `id` and `τ`-independent profile. -/
theorem ssPsi_eq_dynPsi (p : ℝ) (lam : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) :
    Work.CoreResiduals.ssPsi p lam Φ
      = dynPsi p (fun t => (lam t)⁻¹) lam id (fun z θ _ => Φ z θ) := by
  funext r z t
  simp only [Work.CoreResiduals.ssPsi, dynPsi_apply, id_eq]
  ring

/-! ## `(E)` at the constant rate -/

/-- **`(E)` at a `τ`-independent profile.**  For a profile that does not depend on the fake time,
the dynamic profile equation `(E)` at constant modulation `μ` is the pointwise profile equation

  `(1+μ)·F + (1-μ)·D_zF + UVR α F Φ = 0`

on the open quadrant. -/
theorem dynEqF_const_iff {p μ : ℝ} {F Φ : ℝ → ℝ → ℝ} :
    DynEqF p (fun _ => μ) (fun z θ _ => F z θ) (fun z θ _ => Φ z θ)
      ↔ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
          (1 + μ) * F z θ + (1 - μ) * Work.Spaces.Dz F z θ
            + Work.Construction.UVR p F Φ z θ = 0 := by
  constructor
  · intro h z θ hzθ
    have h1 := h z θ 1 hzθ (by norm_num)
    have e1 : deriv (fun s : ℝ => (fun z θ _ => F z θ) z θ s) 1 = 0 := deriv_const 1 (F z θ)
    have e2 : slice (fun z θ _ => F z θ) 1 = F := rfl
    have e3 : slice (fun z θ _ => Φ z θ) 1 = Φ := rfl
    rw [e1, e2, e3] at h1
    linarith [h1]
  · intro h z θ τ hzθ hτ
    have h1 := h z θ hzθ
    have e1 : deriv (fun s : ℝ => (fun z θ _ => F z θ) z θ s) τ = 0 := deriv_const τ (F z θ)
    have e2 : slice (fun z θ _ => F z θ) τ = F := rfl
    have e3 : slice (fun z θ _ => Φ z θ) τ = Φ := rfl
    rw [e1, e2, e3]
    linarith [h1]

/-- **The sanity check: the constant-rate case reproduces `DynEqConst p (2κ) 1`.**  At zero
modulation (`μ ≡ 0`, so `κ = 1+μ = 1` and `b = 1`) and for a `τ`-independent profile, `(E)` is
*exactly* the constant-rate profile equation `Work.CoreResiduals.DynEqConst p 1 1 F Φ` — i.e.
`DynEqConst p (2κ) 1 F Φ` at the model rate `2κ = 1`, the equation solved in the Construction area
at the inhabitant (`λ̄ = 1 - t/2`, `κ = -λ̄' = 1/2`). -/
theorem dynEqF_const_iff_DynEqConst {p : ℝ} {F Φ : ℝ → ℝ → ℝ} :
    DynEqF p (fun _ => 0) (fun z θ _ => F z θ) (fun z θ _ => Φ z θ)
      ↔ Work.CoreResiduals.DynEqConst p 1 1 F Φ := by
  rw [dynEqF_const_iff, Work.CoreResiduals.DynEqConst]
  constructor
  · intro h z θ hzθ
    have h1 := h z θ hzθ
    linarith [h1]
  · intro h z θ hzθ
    have h1 := h z θ hzθ
    linarith [h1]

/-- **The general constant-modulation case.**  With `μ ≡ μ₀` constant, `λ = lamfun μ₀` (so that
`b = 1+λ = (1-μ₀)/(1+μ₀)`) and a `τ`-independent profile, `(E)` is the constant-rate equation
`DynEqConst p (1+μ₀) (1+lamfun μ₀) F Φ` of `Work.CoreResiduals.meridianEq_of_dynEqConst`'s
dictionary (`κ = 1+μ`, `b = 1+λ`). -/
theorem dynEqF_const_mu_iff {p μ₀ : ℝ} (hμ : 1 + μ₀ ≠ 0) {F Φ : ℝ → ℝ → ℝ} :
    DynEqF p (fun _ => μ₀) (fun z θ _ => F z θ) (fun z θ _ => Φ z θ)
      ↔ Work.CoreResiduals.DynEqConst p (1 + μ₀)
          (1 + Work.Construction.lamfun μ₀) F Φ := by
  have hkey : (1 + μ₀) * (1 + Work.Construction.lamfun μ₀) = 1 - μ₀ := by
    have h := Work.Stability.kappaStar_mul_bStar μ₀ hμ
    rwa [Work.Stability.kappaStar_eq, Work.Stability.bStar_eq_lamfun] at h
  rw [dynEqF_const_iff, Work.CoreResiduals.DynEqConst]
  constructor
  · intro h z θ hzθ
    have h1 := h z θ hzθ
    have h2 : (1 - μ₀) * Work.Spaces.Dz F z θ
        = (1 + μ₀) * (1 + Work.Construction.lamfun μ₀) * Work.Spaces.Dz F z θ := by
      rw [hkey]
    rw [h2] at h1
    linarith [h1]
  · intro h z θ hzθ
    have h1 := h z θ hzθ
    have h2 : (1 - μ₀) * Work.Spaces.Dz F z θ
        = (1 + μ₀) * (1 + Work.Construction.lamfun μ₀) * Work.Spaces.Dz F z θ := by
      rw [hkey]
    rw [h2]
    linarith [h1]

end Work.FTS.MeridianDyn
