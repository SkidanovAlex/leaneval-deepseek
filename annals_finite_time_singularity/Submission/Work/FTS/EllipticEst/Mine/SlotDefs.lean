/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Mine.SlotDefs`: the vocabulary of the top-angular-slot estimate at level `2`

This small (sorry-free) module fixes the notation used by `Mine/TopSlotTwo.lean` and by the
auxiliary lemmas it consumes:

* `Gsrc α F Ψ` — the *angular source* of the equation, i.e. the function `G` with
  `Lzero1 (Ψ z ·) = G z ·`; by (PolarBSL) it is `F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` on the open
  quadrant (note that the workspace's `Lzero1` already contains the `-6u` term);
* `sig4 γ`, `sig2 γ` — the two angular weights `sin(2θ)^{4-γ}` and `sin(2θ)^{2-γ}` of the
  paper's Steps 5 and 4.

The only mathematical content of the module is `Lzero1_slice_eq_Gsrc`, which rewrites the
equation `bslOp α Ψ = F` as `Lzero1 (Ψ z ·) = Gsrc α F Ψ z ·` for `z > 0`, and the helper
`pthIter_eq_iteratedDeriv`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false

/-- **The angular source.**  The function `G` for which the equation `bslOp α Ψ = F` reads
`Lzero1 (Ψ z ·) = G z ·`, namely `G = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` (the radial part of `bslOp`
moved to the right hand side). -/
def Gsrc (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    + α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)

/-- The angular weight `sin(2θ)^{4-γ}` of the paper's Step 5. -/
def sig4 (γ : ℝ) (θ : ℝ) : ℝ := Real.rpow (Real.sin (2 * θ)) (4 - γ)

/-- The angular weight `sin(2θ)^{2-γ}` of the paper's Step 4. -/
def sig2 (γ : ℝ) (θ : ℝ) : ℝ := Real.rpow (Real.sin (2 * θ)) (2 - γ)

/-- `pthIter n f z θ` is the iterated `∂_θ`-derivative of the slice `θ ↦ f z θ`. -/
theorem pthIter_eq_iteratedDeriv (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n f = fun z θ => iteratedDeriv n (fun t => f z t) θ := by
  induction n with
  | zero => funext z θ; simp
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih]
      funext z θ
      rw [iteratedDeriv_succ]
      rfl

/-- **The equation in `Lzero1` form.**  If `bslOp α Ψ = F` on the open quadrant then the
angular profile `θ ↦ Ψ z θ` solves `Lzero1 u = (Gsrc α F Ψ) z ·` for every `z > 0`. -/
theorem Lzero1_slice_eq_Gsrc {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Gsrc α F Ψ z θ := by
  have h := heq z hz θ hθ hθ'
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at h
  have hpth2 : Work.Spaces.pthIter 2 Ψ z θ =
      deriv (fun t => deriv (fun t => Ψ z t) t) θ := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ]
    rfl
  have hpth1 : Work.Spaces.pth (fun x t => Real.tan t * Ψ x t) z θ =
      deriv (fun t => Real.tan t * Ψ z t) θ := rfl
  rw [hpth2, hpth1] at h
  simp only [Work.FTS.EllipticEst.Lzero1, Gsrc] at h ⊢
  linarith [h]

end Work.FTS.EllipticEst.Mine
