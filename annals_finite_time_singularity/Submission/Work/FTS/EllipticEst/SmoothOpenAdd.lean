/-
Copyright: work module for the Elgindi finite-time singularity project.

# Additivity of the iterated operators on the open quadrant

The elliptic estimates of §'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

are stated for data which are `C^∞` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)` and in the
weighted space `ℋ^k` (`Work.FTS.EllipticEst.SmoothOpen` / `Work.Spaces.HkMem`).  In this
chapter the closure of `ℋ^k` under addition is needed, whose only analytic input is the
pointwise additivity of the iterated operators `D_z^i` and `D_z^j D_θ^i` on the open quadrant:
the `D`-operators are linear where the data are differentiable, i.e. on `Q0`.

This module provides that additivity, in the internal `(0 < z, 0 < θ, θ < π/2)` shape used by
the pointwise estimates of the chapter:

* `SmoothOpen.DzIter_congr` — two functions agreeing on `Q0` have the same `D_z`-iterates there
  (no smoothness needed: this is the locality of `deriv`);
* `SmoothOpen.DzIter_add`, `SmoothOpen.DthIter_add` — additivity of the iterated `D`-operators
  for two `SmoothOpen` data;
* `SmoothOpen.mixed_add` — additivity of `D_z^j D_θ^i`;
* `SmoothOpen.add` — `SmoothOpen` is closed under pointwise addition.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

variable {f g F G : ℝ → ℝ → ℝ}

/-- `SmoothOpen` is closed under pointwise addition.

(Named `smoothOpen_add`, not `SmoothOpen.add`: the latter would be picked up by the dot
notation `hf.add` for `hf : SmoothOpen f`, and would then be its own recursive call.) -/
theorem smoothOpen_add (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ + g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; rfl
  rw [SmoothOpen, hfun]
  exact ContDiffOn.add hf hg

/-- Two functions agreeing on the open quadrant have the same `D_z`-iterates there. -/
theorem SmoothOpen.DzIter_congr
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

/-- The iterated `D_z`-operator is additive on the open quadrant for `SmoothOpen` data. -/
theorem SmoothOpen.DzIter_add (hf : SmoothOpen f) (hg : SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated `D_θ`-operator is additive on the open quadrant for `SmoothOpen` data. -/
theorem SmoothOpen.DthIter_add (hf : SmoothOpen f) (hg : SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        (((hf.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        (((hg.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant for `SmoothOpen`
data. -/
theorem SmoothOpen.mixed_add (hf : SmoothOpen f) (hg : SmoothOpen g) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  intro z θ hz h1 h2
  have hcongr := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => f z θ + g z θ))
    (G := fun z θ => Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ)
    (fun z θ hz h1 h2 => SmoothOpen.DthIter_add hf hg i z θ hz h1 h2) j z θ hz h1 h2
  have hadd := SmoothOpen.DzIter_add (hf.DthIter i) (hg.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

end Work.FTS.EllipticEst
