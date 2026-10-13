/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/OpenClass.lean` — the *open* coercivity class

## Why this file exists

The level-four barrier of the a-priori estimate pairs the projected mollified slice
`x = Pz (J_ε (slice g τ))` against itself with the frozen inner product
`Work.FTS.Nonlin.UnifIP`.  Every clause of `UnifIP` is guarded by the frozen classes
`RegQ α k` / `CoerAdm α` (`Vocab.lean`), and

  `RegQ α k f = LocData.SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f`,

where `SmoothQuad f` is `C^∞` of `f` on the **strip** `z > -1, 0 < θ < π/2`.  Since `J_ε f` is
defined to be *zero* off the open quadrant, `SmoothQuad (J_ε f)` demands that all `z`-derivatives
of `J_ε f` tend to `0` at `z = 0⁺` — a *flatness* condition which the honest data class
(`SmoothOpen`, `HkMem`, `BdryTraces`) does **not** imply (see
`EpsE4Thr/CoerAdmSlice.lean` and the owner message: the class-`C` clause of `EpsDatumP` gives
`SmoothOpen` at every fake time, never `SmoothQuad`).  So `CoerAdm α (slice (JfamP ρ ε g) τ)` is
*not* reachable along the route, and with it the frozen `UnifIP` cannot be applied to the
projected family at all.

The repair follows the precedent of the level-three/six chapter (`StrongPersist/Clauses.lean`):
replace the unsatisfiable `SmoothQuad`-based class by the *open* class

  `RegQo α k f := SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f`,

which is exactly the part of `RegQ` that an integration by parts on the open quadrant uses, and
which **is** available along the route: the class-`C` clause of `EpsDatumP` supplies all three
ingredients of `RegQo α 5 (slice (JfamP ρ ε g) τ)` (`coerAdmO_slice_JfamP`, in `OpenBarrier.lean`).

This file fixes the vocabulary: the classes `RegQo`/`CoerAdmO`, their elementary API, the
open-class analogue `UnifIPO` of the frozen `UnifIP`, and the implication
`UnifIPO → UnifIP` (the open interface is *stronger*, because `CoerAdm f → CoerAdmO f`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The open classes -/

/-- **The open-quadrant version of `RegQ`**: `C^∞` on the open quadrant `(0,∞) × (0,π/2)` (instead
of the strip `(-1,∞) × (0,π/2)`), honesty of the `ℋ^k`-integrand, and the vanishing of the
integration-by-parts boundary terms up to order `k`.

`RegQo` is exactly what the interior integration by parts of the coercivity needs, and — unlike
`RegQ` — it *is* a consequence of the class-`C` clause carried by the route's data. -/
def RegQo (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α k f ∧
    Work.FTS.Nonlin.BdryTraces α k f

/-- **The open-quadrant version of `CoerAdm`**: the four clauses (regularity, angular vanishing,
the two axis values and the vanishing `L₁₂`-zero-mode), with `RegQo` in place of `RegQ`. -/
def CoerAdmO (α : ℝ) (f : Fn) : Prop :=
  RegQo α 5 f ∧ Work.Spaces.VanishTheta f ∧
    (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) ∧
    Work.Construction.L12 f 0 = 0

/-! ## Elementary API -/

/-- `RegQo` is monotone in the order. -/
theorem regQo_mono {α : ℝ} {f : Fn} {k l : ℕ} (hkl : k ≤ l) (h : RegQo α l f) :
    RegQo α k f :=
  ⟨h.1, Work.FTS.OpenPkg.HkMem_mono_open h.1 k hkl h.2.1,
    fun a b hab => h.2.2 a b (le_trans hab hkl)⟩

/-- `RegQ` refines `RegQo`: `SmoothQuad` restricts to `SmoothOpen` on the open quadrant. -/
theorem regQo_of_regQ {α : ℝ} {k : ℕ} {f : Fn} (h : Work.FTS.Nonlin.RegQ α k f) :
    RegQo α k f :=
  ⟨Work.FTS.OpenPkg.smoothOpen_of_smoothQuad h.1, h.2.1, h.2.2⟩

/-- `CoerAdm` refines `CoerAdmO`. -/
theorem coerAdmO_of_coerAdm {α : ℝ} {f : Fn} (h : Work.FTS.Nonlin.CoerAdm α f) :
    CoerAdmO α f :=
  ⟨regQo_of_regQ h.reg, h.vanish, h.axis, h.l12⟩

/-- `RegQo α 5 f` gives the `RegQo α 4` instance (used by the algebraic clauses). -/
theorem CoerAdmO.regQoFour {α : ℝ} {f : Fn} (h : CoerAdmO α f) : RegQo α 4 f :=
  regQo_mono (by norm_num) h.1

/-- The coercion `CoerAdmO α f → RegQo α 4 f` (the class at which the frozen `UnifIP`'s algebraic
clauses are stated). -/
theorem regQoFour_of_coerAdmO {α : ℝ} {f : Fn} (h : CoerAdmO α f) : RegQo α 4 f :=
  h.regQoFour

/-! ## The open-class analogue of `UnifIP` -/

/-- **The open-class analogue of `Work.FTS.Nonlin.UnifIP`**: the same clause list, with the frozen
classes `RegQ α 4` / `CoerAdm α` replaced by `RegQo α 4` / `CoerAdmO α`.

This is the interface the level-four barrier can actually be run against: `UnifIPO` implies the
frozen `UnifIP` (`UnifIPO.toUnifIP`), and — unlike `UnifIP` — it is *satisfiable at the projected
slices of the route* (`OpenBarrier.coerAdmO_slice_JfamP`). -/
structure UnifIPO (IP : ℝ → Fn → Fn → ℝ) (α₂ cc clo Cup Ccs : ℝ) : Prop where
  pos : 0 < α₂ ∧ 0 < cc ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Ccs
  symm : ∀ α f g, IP α f g = IP α g f
  add_fst : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g, RegQo α 4 f₁ → RegQo α 4 f₂ → RegQo α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  smul_fst : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) f g, RegQo α 4 f → RegQo α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  congr_qd : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g, RegQo α 4 f → RegQo α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  nonneg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, RegQo α 4 f → 0 ≤ IP α f f
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g, RegQo α 4 f → RegQo α 4 g →
    |IP α f g| ≤ Ccs * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g
  lo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f → clo * Work.Spaces.HkSq α 4 f ≤ IP α f f
  up : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f → IP α f f ≤ Cup * Work.Spaces.HkSq α 4 f
  coer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f →
    cc * Work.Spaces.HkSq α 4 f ≤ IP α (Work.Coercivity.LGammaT α f) f
  Dz_self : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdmO α f →
    |IP α (Work.Spaces.Dz f) f| ≤ Ccs * Work.FTS.Nonlin.Xn α f ^ 2

/-- **`UnifIPO` implies the frozen `UnifIP`**: every `CoerAdm` profile is a `CoerAdmO` profile, so
the open-class clauses are stronger.  Consequently a re-run of the coercivity chapter against the
open class *delivers* the frozen interface on its own (smaller) class. -/
theorem UnifIPO.toUnifIP {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (h : UnifIPO IP α₂ cc clo Cup Ccs) : Work.FTS.Nonlin.UnifIP IP α₂ cc clo Cup Ccs where
  pos := h.pos
  symm := h.symm
  add_fst := fun α hα f₁ f₂ g h₁ h₂ h₃ =>
    h.add_fst α hα f₁ f₂ g (regQo_of_regQ h₁) (regQo_of_regQ h₂) (regQo_of_regQ h₃)
  smul_fst := fun α hα c f g h₁ h₂ =>
    h.smul_fst α hα c f g (regQo_of_regQ h₁) (regQo_of_regQ h₂)
  congr_qd := fun α hα f f' g h₁ h₂ hc =>
    h.congr_qd α hα f f' g (regQo_of_regQ h₁) (regQo_of_regQ h₂) hc
  nonneg := fun α hα f h₁ => h.nonneg α hα f (regQo_of_regQ h₁)
  cs := fun α hα f g h₁ h₂ => h.cs α hα f g (regQo_of_regQ h₁) (regQo_of_regQ h₂)
  lo := fun α hα f h₁ => h.lo α hα f (coerAdmO_of_coerAdm h₁)
  up := fun α hα f h₁ => h.up α hα f (coerAdmO_of_coerAdm h₁)
  coer := fun α hα f h₁ => h.coer α hα f (coerAdmO_of_coerAdm h₁)
  Dz_self := fun α hα f h₁ => h.Dz_self α hα f (coerAdmO_of_coerAdm h₁)

end Work.FTS.StrongEps.EpsE4Thr
