/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/PZeroScheme.lean` — the `P₀`-corrected `ε`-scheme

The lead's design (`FTS_HARD_DESIGN.md`, §(B)) specifies the scheme

  `∂_τ g = P₀ J_ε [𝓛 + 𝓡] (P₀ J_ε g)`,   `P₀ f = f − L₁₂(f)(0) · b`.

The statement file `FTS_HARD_STMTS.lean.txt` omits `P₀`; without it the class-`C` clause
`L₁₂(g)(0) = 0` — which `EpsDatum`, `StrongPersist.H6Adm`/`L6Ctx`, `hEll`, `EllLimOK` and
`MuLamOK` all consume — is **false** along the scheme (the log-coordinate mollifier `J_ε` is a
two-dimensional convolution whose angular half shifts `tan θ`, and the angular weight `K(θ)dθ` of
`L₁₂` is not invariant under that shift; see `NOTES_Pzero.md` §1).

This module records the corrected scheme in the vocabulary of
`Submission/Work/FTS/StrongEps/PZero.lean`:

* `JfamP ρ ε g := fun z θ τ => Pz (Jeps ρ ε (slice g τ)) z θ` — the *inner* projection, which keeps
  the profile that the elliptic solution operator `E` is applied to inside the class `ClassC` at
  every fake time **by construction**;
* `IsEpsSolP … g₀ g` — the design's scheme: the fake-time derivative of `g` is the *projection* of
  the mollified right-hand side evaluated at the projected family;
* `epsWP`/`epsRHSP` — the pre-mollified right-hand side and the right-hand side of the projected
  scheme, with the definitional identity `epsRHSP = Pz (J_ε (epsWP))`.

Everything here is `sorry`-free: the module only *fixes vocabulary* (definitions and `rfl`-lemmas).
The E2–E5 chain is to be restated against these objects; see `NOTES_Pzero.md` §3 for the plan and
the five already-delegated analytic lemmas about `Pz`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false

/-! ## The projected family -/

/-- **The `P₀`-projected mollified family**: `JfamP ρ ε g = P₀ ∘ J_ε (slice g ·)`.

This is the family whose slices the elliptic solution operator `E`, the level-four/level-six
contexts (`L6Ctx`) and the modulation package (`MuLamOK`) are evaluated at.  Thanks to the
projection its slices lie in `ClassC` at every fake time (`Pz_l12` + `classC_Pz`), which is what
the un-projected `Jfam` cannot provide. -/
noncomputable def JfamP (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) : Fam :=
  fun z θ τ => Pz (Jeps ρ ε (slice g τ)) z θ

/-- The definitional identity of the projected family. -/
theorem JfamP_apply (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (z θ τ : ℝ) :
    JfamP ρ ε g z θ τ = Pz (Jeps ρ ε (slice g τ)) z θ := rfl

/-- The projected family has the projected profile at every fake time. -/
theorem slice_JfamP (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fam) (τ : ℝ) :
    slice (JfamP ρ ε g) τ = Pz (Jeps ρ ε (slice g τ)) := rfl

/-- The projection is invisible on a family whose slices already have vanishing zero mode. -/
theorem JfamP_eq_Jfam_of_l12 {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {g : Fam}
    (h : ∀ τ, Work.Construction.L12 (Jeps ρ ε (slice g τ)) 0 = 0) :
    JfamP ρ ε g = Jfam ρ ε g := by
  funext z θ τ
  show Pz (Jeps ρ ε (slice g τ)) z θ = Jeps ρ ε (slice g τ) z θ
  rw [Pz_self_of_l12 (h τ)]

/-! ## The projected scheme -/

/-- The pre-mollified right-hand side of the projected scheme at `τ`: the paper's right-hand side
evaluated at the projected family.  It is the analogue of `Gdot.epsW` with `Jfam` replaced by
`JfamP`. -/
noncomputable def epsWP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) : Fn :=
  fun z θ => dynLin α (JfamP ρ ε g) τ z θ
    + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ z θ

/-- The right-hand side of the projected scheme: `P₀` applied to the mollified pre-mollified
right-hand side. -/
noncomputable def epsRHSP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) : Fn :=
  Pz (Jeps ρ ε (epsWP α ρ ε Φs E g τ))

/-- The scheme's right-hand side is the projection of the mollified pre-mollified right-hand
side (definitional). -/
theorem epsRHSP_eq_Pz_Jeps_epsWP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) :
    epsRHSP α ρ ε Φs E g τ = Pz (Jeps ρ ε (epsWP α ρ ε Φs E g τ)) := rfl

/-- **The `P₀`-corrected `ε`-scheme of the design's §(B)**:
`∂_τ g = P₀ J_ε [𝓛 + 𝓡] (P₀ J_ε g)`.

The two occurrences of the projection are both load-bearing:
* the *inner* one (inside `JfamP`) keeps the profiles at which `E`, `L6Ctx` and `MuLamOK` are
  evaluated inside `ClassC`;
* the *outer* one makes `L₁₂(∂_τ g)(0) = 0`, hence `L₁₂(slice g τ)(0) = L₁₂ g₀ 0` for all `τ`
  (`Pz_l12`), so that the limit family has `P₀(slice g τ) = slice g τ` — which is what turns the
  limiting equation into the *unprojected* `IsDynEqOn` of the conclusion. -/
def IsEpsSolP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (g : Fam) : Prop :=
  (∀ z θ, g z θ 0 = g₀ z θ) ∧
  ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
    HasDerivWithinAt (fun s => g z θ s) (epsRHSP α ρ ε Φs E g τ z θ) (Set.Icc 0 T) τ

/-- The scheme's initial condition. -/
theorem IsEpsSolP.init {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T Φs E g₀ g) : ∀ z θ, g z θ 0 = g₀ z θ := h.1

/-- The scheme's equation, pointwise on the open quadrant. -/
theorem IsEpsSolP.eq {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T Φs E g₀ g) {z θ τ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun s => g z θ s) (epsRHSP α ρ ε Φs E g τ z θ) (Set.Icc 0 T) τ :=
  h.2 z θ τ hz hθ hτ

end Work.FTS.StrongEps
