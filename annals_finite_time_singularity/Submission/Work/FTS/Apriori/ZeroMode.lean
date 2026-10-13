/-
# The `L₁₂` zero-mode identity (design §4 L-N5.8)

`L₁₂(g)(0) = ∫₀^∞ ∫₀^{π/2} K(θ) g(s,θ)/s dθ ds` is the zero mode that the modulation equation
drives (`Work.Construction.mufun`).  This module proves the identity N6 needs for its `hDetermines`
on `V₀ = {f : L₁₂(f)(0) = 0}`:

  `L₁₂(∂_τg)(0) = (1 − μ(τ))·L₁₂(g(τ))(0)`,

i.e. **`L₁₂(-𝓛_Γ^T g + gRHS)(0) = (1−μ)L₁₂(g)(0)`**.

The computation is the paper's (tex 1366–1381) and splits into three facts, each of which is an
input here (they belong to the `L₁₂` chapter of the coercivity/construction area):

* `hlin` — `L₁₂(𝓛_Γ^T f)(0) = −L₁₂(f)(0)`: the paper's Lemma `(L12L)`
  (`L₁₂(𝓛_Γ f) = 𝓛(L₁₂ f)`, so at `z = 0` it is `−L₁₂ f(0)`) together with the projector identity
  `L₁₂(𝕡h)(0) = 0`.  (For `dynLin = −𝓛_Γ^T` this gives `L₁₂(dynLin)(0) = L₁₂(g)(0)`.)
* `hstar` — `L₁₂(N_*)(0) = −μ·L₁₂(g)(0)`, from `N_* = −μ g − (μ+λ+μλ)D_zg` with `λ = lamfun μ`
  (whence `−(μ+λ+μλ) = μ`, `Nstar_lamfun` below) and the elementary identity
  `L₁₂(D_z f)(0) = −(f,K)_{L²_θ}(0) = 0` for profiles vanishing at `z = 0`.
* `hadd` — additivity of the `L₁₂` integral over the five summands of the right-hand side
  (which is the integrability statement of design L-N5.8; see `L12_sum_zero` for the finset form).

The remaining content, `L₁₂(-μ̄·AK + N₀ + N)(0) = 0` (the `μ̄`-cancellation) and
`L₁₂(AK)(0) = 1` (`Work.Construction.L12_AK_eq_one`), is pure algebra and is proved here.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.Apriori.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false

/-- **`N_*` at the paper's modulation**: with `λ = lamfun μ`, the linear term collapses to
`μ(D_zg − g)` (the `μ + λ + μλ = −μ` identity of the paper, tex 1356). -/
theorem Nstar_lamfun {μ : ℝ} (hμ : μ ≠ -1) (g : Fn) :
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g
      = fun z θ => μ * (Work.Spaces.Dz g z θ - g z θ) := by
  have h1μ : (1 : ℝ) + μ ≠ 0 := by intro h; exact hμ (by linarith)
  have hkey : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
    simp only [Work.Construction.lamfun]
    field_simp
    ring
  funext z θ
  simp only [Work.Construction.Nstar, hkey]
  ring

/-- **The `L₁₂` zero-mode identity** (design §4 L-N5.8): along any solution of the dynamic
modulated equation, `L₁₂(RHS)(0) = (1 − μ)L₁₂(g)(0)`.  See the module docstring for the three
inputs `hlin`, `hstar`, `hadd`. -/
theorem L12_zero_rhs {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (g Φ : Fam) (τ : ℝ)
    (hg : GalClass α (slice g τ)) (hμ : muDyn α Φ g τ ≠ -1)
    (hadd : Work.Construction.L12 (dynLin α g τ + dynRHS α Φ g τ) 0
      = Work.Construction.L12 (dynLin α g τ) 0
        - Work.Construction.mubar
            (Work.Construction.N0 α (Work.Construction.Ftot α (slice g τ)) (slice g τ))
            (Work.Construction.N α (Work.Construction.Ftot α (slice g τ)) (slice Φ τ))
          * Work.Construction.L12 (Work.Construction.AK α) 0
        + Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α (slice g τ)) (slice g τ)) 0
        + Work.Construction.L12
            (Work.Construction.N α (Work.Construction.Ftot α (slice g τ)) (slice Φ τ)) 0
        + Work.Construction.L12 (Work.Construction.Nstar (muDyn α Φ g τ)
            (Work.Construction.lamfun (muDyn α Φ g τ)) (slice g τ)) 0)
    (hlin : Work.Construction.L12 (dynLin α g τ) 0 = Work.Construction.L12 (slice g τ) 0)
    (hstar : Work.Construction.L12 (Work.Construction.Nstar (muDyn α Φ g τ)
        (Work.Construction.lamfun (muDyn α Φ g τ)) (slice g τ)) 0
      = - muDyn α Φ g τ * Work.Construction.L12 (slice g τ) 0) :
    Work.Construction.L12 (dynLin α g τ + dynRHS α Φ g τ) 0
      = (1 - muDyn α Φ g τ) * Work.Construction.L12 (slice g τ) 0 := by
  have hmubar : Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α (slice g τ)) (slice g τ))
      (Work.Construction.N α (Work.Construction.Ftot α (slice g τ)) (slice Φ τ))
      = Work.Construction.L12
          (Work.Construction.N0 α (Work.Construction.Ftot α (slice g τ)) (slice g τ)) 0
        + Work.Construction.L12
          (Work.Construction.N α (Work.Construction.Ftot α (slice g τ)) (slice Φ τ)) 0 := rfl
  have hAK : Work.Construction.L12 (Work.Construction.AK α) 0 = 1 :=
    Work.Construction.L12_AK_eq_one hα hα1
  rw [hadd, hlin, hstar, hmubar, hAK]
  ring

end Work.FTS.Apriori
