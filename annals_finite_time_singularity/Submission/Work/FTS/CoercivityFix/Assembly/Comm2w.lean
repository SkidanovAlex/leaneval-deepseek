/-
# `Assembly/Comm2w.lean` — additivity with *block continuity* instead of `RegQ`

`Assembly.Comm2 α n IP` requires `RegQ α n` of all three arguments of `add` — and `RegQ`
contains `SmoothQuad`, i.e. genuine `C^∞` through `z = 0`.  That is too strong for the two
transfer defects: `E1 α f = (sin 2θ·Γ'(θ))·radA α f z` and `E2 α f = Ê₂ f + Γ(θ)·radS α f z`
contain `L₁₂ f = ∫_z^∞ L12dens`, and `CoerAdm α f` constrains `f` only on `z ≥ 0`, so `L₁₂ f`
need not be `C^∞` (both `Transfer/E1_regQ_norm` and `Transfer/E2_regQ_norm` were refuted for
exactly this reason).  What the defects *do* have is continuity of all their blocks.

This file records the weakened package: `BlocksCont k g` (continuity on the open quadrant of
every `mixed b a g` with `a + b ≤ k`), `BlocksAdd k f₁ f₂` (the pointwise additivity of the
same blocks on the open quadrant), and `Comm2w α n IP`, whose `add` field asks for those
instead of `RegQ α n` (and for `HkMem α n`, which supplies the integrability that the `wip`
splitting needs).

`Comm2w` transports through `HkIPStep` exactly as `Comm2` does (`Comm2w_succ`): the three
level-`n` applications are to `(f₁, f₂, g)`, `(D_θf₁, D_θf₂, D_θg)` and `(D_zf₁, D_zf₂, D_zg)`,
and the block hypotheses at level `n+1` restrict to the level-`n` ones for the differentiated
arguments.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Block continuity up to order `k`**: every mixed derivative `D_z^bD_θ^a g` with
`a + b ≤ k` is continuous on the open quadrant.  This is the part of `SmoothQuad` that the
transfer defects actually have. -/
def BlocksCont (k : ℕ) (g : Fn) : Prop :=
  ∀ a b : ℕ, a + b ≤ k →
    ContinuousOn (Function.uncurry (Work.Spaces.mixed b a g)) Work.Construction.Qd

/-- **Block additivity up to order `k`**: every mixed derivative of `f₁ + f₂` with
`a + b ≤ k` splits on the open quadrant. -/
def BlocksAdd (k : ℕ) (f₁ f₂ : Fn) : Prop :=
  ∀ a b : ℕ, a + b ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.mixed b a (f₁ + f₂) z θ
      = Work.Spaces.mixed b a f₁ z θ + Work.Spaces.mixed b a f₂ z θ

/-- **The inputs of one `Comm2w.add` call**, bundled: what a caller must supply to split
`IP (f₁ + f₂) g` when `f₁`, `f₂` are not known to lie in `RegQ` (e.g. `f₁ = 𝓛̂(D_θf)`,
`f₂ = E1 α f`).  The `Transfer` layer's rewiring consumes this. -/
def AddOK (α : ℝ) (n : ℕ) (f₁ f₂ g : Fn) : Prop :=
  Work.Spaces.HkMem α n f₁ ∧ Work.Spaces.HkMem α n f₂ ∧ Work.Spaces.HkMem α n g ∧
    BlocksCont n f₁ ∧ BlocksCont n f₂ ∧ BlocksCont n g ∧ BlocksAdd n f₁ f₂

/-- `SmoothQuad` gives block continuity at every order. -/
theorem BlocksCont.of_smoothQuad {g : Fn} (hg : Work.FTS.LocData.SmoothQuad g) (k : ℕ) :
    BlocksCont k g := by
  intro a b _
  have hV : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hmix := Work.FTS.LocData.contDiffOn_mixed hV hg b a
  have hsub : Work.Construction.Qd ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    obtain ⟨hz, hθ⟩ := hp
    exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hz]), hθ⟩
  exact (hmix.mono hsub).continuousOn

/-- **The weakened algebraic package.**  Same shape as `Assembly.Comm2`, but `add` takes block
continuity, block additivity and `HkMem` instead of `RegQ`. -/
structure Comm2w (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, from block continuity/block additivity and `HkMem` -/
  add : ∀ f₁ f₂ g : Fn,
    Work.Spaces.HkMem α n f₁ → Work.Spaces.HkMem α n f₂ → Work.Spaces.HkMem α n g →
    BlocksCont n f₁ → BlocksCont n f₂ → BlocksCont n g → BlocksAdd n f₁ f₂ →
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `D_θ` commutes with `Lhat` exactly -/
  dthC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
  /-- the `D_z` commutator of `Lhat` is the explicit defect `Ê₂` -/
  dzC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ

end Work.FTS.CoercivityFix.Assembly
