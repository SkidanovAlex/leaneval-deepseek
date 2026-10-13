/-
# `Work.FTS.RegPkgGal.R5Slot` — the R5 input (the a-priori regularity of the right-hand side)

`R5f.jet_dtg_of_rhs` (delegated) produces `RegPkg'.hgdoth` — the fake-time jet of `g̃` — from the
identification `∂_τg̃ = dynLin α g τ + dynRHS α Φ g τ` on the open quadrant plus the *a-priori
regularity* of that right-hand side: it is a `Jet` on the closed domain, and it vanishes at
`z = 0` and on the two angular boundary lines (where `g̃`'s `τ`-derivative vanishes).

That is exactly the interface the paper's estimates deliver: the right-hand side
`-𝓛_Γ^T(g) + N₀ + N + N_*` is bounded and jointly `α`-Hölder once the profile and the stream
function are in the class (the `Rop α Φ̃`-jet of `NOTES_RegPkgGal.md` §7 is one of its ingredients,
not a separate requirement).

**This interface is also stable under the pending `mufun` sign fix** (lead's message of 19:45): the
bundle never unfolds `muDyn`/`mufun`, it treats `dynLin + dynRHS` as an opaque family.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.RVocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- **THE R5 INPUT**: the a-priori regularity of the right-hand side of the fake-time equation,
together with its boundary values. -/
structure R5Slot (α S : ℝ) (g Φ : Fam) (N0 : ℝ) : Prop where
  /-- the dynamic equation (`IsDynEqOn`, the one-sided-in-`τ` form produced by Open2) -/
  hsol : Work.FTS.Galerkin.IsDynEqOn (pExp α) Φ g
  /-- the two-sided `τ = 0` equation, which glues the extension at `τ = 0` -/
  h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
    HasDerivAt (fun s => g z θ s)
      (Work.FTS.Galerkin.dynLin (pExp α) g 0 z θ
        + Work.FTS.Galerkin.dynRHS (pExp α) Φ g 0 z θ) 0
  /-- the right-hand side is a `Jet` on the closed quadrant -/
  hRHS : Jet α S N0
    (fun z θ τ => Work.FTS.Galerkin.dynLin (pExp α) g τ z θ
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z θ)
  /-- **the right-hand side is `C¹` in `z` with a uniformly bounded derivative** on the open
  quadrant: at every point of `(0,∞) × Iθ × [0,S]` the map `z ↦ dynLin + dynRHS` is differentiable
  with derivative bounded by `N1`, uniformly in `τ` (and in `θ`).  This is the *only* extra piece of
  the right-hand side's regularity that the fake-time `z`-modulus of `∂_zg̃` needs: since
  `∂_τg̃ = dynLin + dynRHS` (`R5f.deriv_extG_eq_rhs_of_jet`), it gives `∂_z∂_τg̃ = ∂_z(dynLin+dynRHS)`
  and hence, by differentiating under the `τ`-integral, the `τ`-Lipschitz continuity of `z ↦ ∂_zg̃`
  (`Der.htaumodp`). -/
  hRHz : ∃ N1 : ℝ, 0 ≤ N1 ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    ∀ z ∈ Set.Ioi (0 : ℝ),
    ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS.Galerkin.dynLin (pExp α) g τ z' θ
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z' θ) d z ∧ |d| ≤ N1
  /-- the right-hand side vanishes at `z = 0` -/
  hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ 0 θ
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ 0 θ = 0
  /-- the right-hand side vanishes at `θ = 0` -/
  hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ z 0
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z 0 = 0
  /-- the right-hand side vanishes at `θ = π/2` -/
  hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
    Work.FTS.Galerkin.dynLin (pExp α) g τ z (Real.pi / 2)
      + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z (Real.pi / 2) = 0

end Work.FTS.RegPkgGal
