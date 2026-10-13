/-
# `Transfer/Q0Sm.lean` — the finite-order smooth class on the open quadrant

The transfer of the coercivity of the clean operator `𝓛̂` to the paper's operator
`𝓛_Γ^T = 𝓛̂ + Corr` runs the slot-by-slot argument of `Transfer/stepT.lean`, and the two
defects of that transfer,

  `E1 α f = (sin 2θ · Γ'(θ)) · radA α f z`,   `E2 α f = Ê₂ f + Γ(θ) · radS α f z`,

are **not** analytic on a neighbourhood of the closed quadrant: `radA`, `radS` contain
`L₁₂ f`, whose smoothness stops at `C³` on `(0,∞)` (`Transfer/L12f_contDiffOn.lean`).  The
class `Work.Spaces.SmoothNbhd` (order `⊤`, i.e. real-analyticity) and the class
`Work.FTS.LocData.SmoothQuad` (smoothness on `z > -1`) are therefore both unusable for the
defects.

What *is* true of every function occurring in the transfer is a **finite order of
differentiability on the open quadrant** `Qd = (0,∞) × (0,π/2)`.  This module fixes that
class,

  `Q0Sm k X  ≜  X ∈ C^k` on `Qd`,

together with the API the slot argument consumes:

* `Q0Sm.mono`, `Q0Sm.dth`, `Q0Sm.dz` — restriction in the order and the two derivatives;
* `Q0Sm.mixed_continuousOn`, `Q0Sm.blocksCont` — continuity of the blocks `D_z^bD_θ^a X`
  of total order `a + b ≤ k` (the finite-order version of
  `Work.FTS.LocData.contDiffOn_mixed`, not needing `SmoothQuad`);
* `Q0Sm.continuousOn_HkIntegrand` — continuity of the `ℋ^k`-integrand, the measurability
  input of the majorant criterion `HkMem_of_majorant_ae`;
* `Q0Sm.dth_add`, `Q0Sm.dz_add` — the additivity of the two derivatives on `Qd`, which is
  what turns the pointwise splitting `D_θ(f₁+f₂) = D_θf₁ + D_θf₂` into an identity of the
  pairings.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Vocab
import Submission.Work.Construction.Defs
import Submission.Work.FTS.CoercivityFix.Transfer.E2_blocks
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The open quadrant, on which every function of the transfer is differentiable. -/
abbrev Qd : Set (ℝ × ℝ) := Work.Construction.Qd

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-- **The finite-order smooth class on the open quadrant.**  `Q0Sm k X` says that the
uncurried profile `X` is `C^k` on `Qd`.  It is the transfer's replacement for
`Work.FTS.LocData.SmoothQuad`, which is not available for `E1`, `E2`. -/
def Q0Sm (k : ℕ) (X : Fn) : Prop :=
  ContDiffOn ℝ (((k : ℕ)) : WithTop ℕ∞) (Function.uncurry X) Qd

theorem q0Sm_iff (k : ℕ) (X : Fn) :
    Q0Sm k X ↔ ContDiffOn ℝ (((k : ℕ)) : WithTop ℕ∞) (Function.uncurry X) Qd := Iff.rfl

/-! ## The order calculus -/

theorem Q0Sm.mono {k l : ℕ} {X : Fn} (h : Q0Sm k X) (hl : l ≤ k) : Q0Sm l X :=
  h.of_le (m := (((l : ℕ)) : WithTop ℕ∞)) (by exact_mod_cast hl)

theorem Q0Sm.dth {k : ℕ} {X : Fn} (h : Q0Sm (k + 1) X) : Q0Sm k (Work.Spaces.Dth X) :=
  contDiffOn_Dth_nat isOpen_Qd h

theorem Q0Sm.dz {k : ℕ} {X : Fn} (h : Q0Sm (k + 1) X) : Q0Sm k (Work.Spaces.Dz X) :=
  contDiffOn_Dz_nat isOpen_Qd h

/-! ## Continuity of the blocks -/

/-- Every block `D_z^bD_θ^a X` of total order `a + b ≤ k` is continuous on the open
quadrant. -/
theorem Q0Sm.mixed_continuousOn {k : ℕ} {X : Fn} (h : Q0Sm k X) {a b : ℕ} (hab : a + b ≤ k) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed b a X)) Qd :=
  contDiffOn_mixed_nat isOpen_Qd (m := k) h (a := a) (b := b) hab

/-- The block-continuity package of `Assembly.Comm2w`, from `Q0Sm`. -/
theorem Q0Sm.blocksCont {k : ℕ} {X : Fn} (h : Q0Sm k X) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont k X :=
  fun a b hab => h.mixed_continuousOn (a := a) (b := b) hab

/-- Continuity of the `ℋ^k`-integrand of `X` on the open quadrant. -/
theorem Q0Sm.continuousOn_HkIntegrand {k : ℕ} {X : Fn} (h : Q0Sm k X) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k X p.1 p.2) Qd :=
  Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont
    h.blocksCont α

/-! ## Additivity of the two derivatives on the open quadrant -/

/-- The `z`-slice of a `C^1` profile on the open quadrant is differentiable. -/
theorem Q0Sm.differentiableAt_slice_z {X : Fn} (h : Q0Sm 1 X) {z θ : ℝ} (hzθ : (z, θ) ∈ Qd) :
    DifferentiableAt ℝ (fun z' : ℝ => X z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hzθ)
  have hproj : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z :=
    (differentiableAt_id.prodMk (differentiableAt_const θ))
  simpa only [Function.uncurry, Function.comp_def] using hd.comp z hproj

/-- The `θ`-slice of a `C^1` profile on the open quadrant is differentiable. -/
theorem Q0Sm.differentiableAt_slice_θ {X : Fn} (h : Q0Sm 1 X) {z θ : ℝ} (hzθ : (z, θ) ∈ Qd) :
    DifferentiableAt ℝ (fun θ' : ℝ => X z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hzθ)
  have hproj : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ :=
    (differentiableAt_const z).prodMk differentiableAt_id
  simpa only [Function.uncurry, Function.comp_def] using hd.comp θ hproj

/-- **`D_θ` is additive on the open quadrant** for `C^1` summands. -/
theorem Q0Sm.dth_add {f₁ f₂ : Fn} (h₁ : Q0Sm 1 f₁) (h₂ : Q0Sm 1 f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.Dth (f₁ + f₂) z θ = Work.Spaces.Dth f₁ z θ + Work.Spaces.Dth f₂ z θ := by
  intro z θ hzθ
  have d1 := h₁.differentiableAt_slice_θ hzθ
  have d2 := h₂.differentiableAt_slice_θ hzθ
  have hderiv : deriv (fun θ' : ℝ => f₁ z θ' + f₂ z θ') θ
      = deriv (fun θ' : ℝ => f₁ z θ') θ + deriv (fun θ' : ℝ => f₂ z θ') θ :=
    deriv_add d1 d2
  simp only [Work.Spaces.Dth, Work.Spaces.pth, Pi.add_apply]
  rw [hderiv]
  ring

/-- **`D_z` is additive on the open quadrant** for `C^1` summands. -/
theorem Q0Sm.dz_add {f₁ f₂ : Fn} (h₁ : Q0Sm 1 f₁) (h₂ : Q0Sm 1 f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.Dz (f₁ + f₂) z θ = Work.Spaces.Dz f₁ z θ + Work.Spaces.Dz f₂ z θ := by
  intro z θ hzθ
  have d1 := h₁.differentiableAt_slice_z hzθ
  have d2 := h₂.differentiableAt_slice_z hzθ
  have hderiv : deriv (fun z' : ℝ => f₁ z' θ + f₂ z' θ) z
      = deriv (fun z' : ℝ => f₁ z' θ) z + deriv (fun z' : ℝ => f₂ z' θ) z :=
    deriv_add d1 d2
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Pi.add_apply]
  rw [hderiv]
  ring

/-- `Q0Sm k X` is equivalent to smoothness at every lower order, in the form in which the
block bookkeeping consumes it. -/
theorem Q0Sm.dth_of_le {k : ℕ} {X : Fn} (h : Q0Sm k X) (hk : 1 ≤ k) : Q0Sm (k - 1) (Work.Spaces.Dth X) := by
  have h1 : Q0Sm (k - 1 + 1) X := by
    rwa [Nat.sub_add_cancel hk]
  exact h1.dth

theorem Q0Sm.dz_of_le {k : ℕ} {X : Fn} (h : Q0Sm k X) (hk : 1 ≤ k) : Q0Sm (k - 1) (Work.Spaces.Dz X) := by
  have h1 : Q0Sm (k - 1 + 1) X := by
    rwa [Nat.sub_add_cancel hk]
  exact h1.dz

end Work.FTS.CoercivityFix.Transfer
