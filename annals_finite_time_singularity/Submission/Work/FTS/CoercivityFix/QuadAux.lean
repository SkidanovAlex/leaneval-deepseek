/-
# The commutator identities of the clean operator `Lhat = 𝓛 − Transport`

The mathematical heart of the fix of node N2 (design `FTS/N45_DESIGN_LEAD.md` §5 T2): the
paper's induction breaks because `D_θ` of the *nonlocal* term of `𝓛_Γ^T` produces
`(2zΓ/(c(1+z)²)) L₁₂(D_θ f)`, which lies in `ℋⁿ` only when `L₁₂(D_θ f)(0) = 0` — a
condition the flow does not preserve.  Splitting off the nonlocal term,

  `𝓛_Γ^T f = Lhat f + Corr α f`,   `Lhat f = 𝓛 f − Transport f = f + D_zf − 2f/(1+z) − 3D_θ f/(1+z)`,

the obstruction disappears: `D_θ` commutes with `Lhat` **exactly** (`Dth_Lhat`), and the
`D_z`-commutator is the explicit bounded function `E2hat f = (2zf + 3z D_θ f)/(1+z)²`
(`Dz_Lhat`).  Neither identity contains an `L₁₂`-term, which is why the modified induction
of this directory needs *no* zero-mode hypothesis on all fifteen mixed derivatives, only
the single `L₁₂(f)(0) = 0` of the class `Work.FTS.Nonlin.CoerAdm`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Coercivity.dth_LGammaT_expansion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The open quadrant on which `Work.FTS.LocData.SmoothQuad` is stated. -/
def Quad : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

theorem isOpen_Quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Quad_iff {z θ : ℝ} : ((z, θ) ∈ Quad) ↔ -1 < z ∧ 0 < θ ∧ θ < π / 2 := by
  simp only [Quad, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Prod.fst, Prod.snd]

/-- `SmoothQuad` gives `C^∞` (hence `C^2`) at every interior point of the open quadrant. -/
theorem SmoothQuad.contDiffAt {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) := by
  have hmem : (z, θ) ∈ Quad := mem_Quad_iff.mpr ⟨by linarith, hθ, hθ2⟩
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Quad from hf).contDiffAt
    (isOpen_Quad.mem_nhds hmem)

theorem SmoothQuad.contDiffAt_two {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (SmoothQuad.contDiffAt hf hz hθ hθ2).of_le (by simp [Work.Stability.smoothOrder])

/-- `SmoothQuad` is a local statement: it gives differentiability of both slices. -/
theorem SmoothQuad.diff_slice {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun z' => f z' θ) z ∧ DifferentiableAt ℝ (fun θ' => f z θ') θ :=
  ⟨Work.Spaces.differentiableAt_curry_left
      ((SmoothQuad.contDiffAt hf hz hθ hθ2).differentiableAt (by simp [Work.Stability.smoothOrder])),
    Work.Spaces.differentiableAt_curry_right
      ((SmoothQuad.contDiffAt hf hz hθ hθ2).differentiableAt (by simp [Work.Stability.smoothOrder]))⟩

/-- Clairaut/Schwarz for the slice derivatives, from the interior class `SmoothQuad`. -/
theorem pz_pth_comm {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pz (Work.Spaces.pth f) z θ = Work.Spaces.pth (Work.Spaces.pz f) z θ :=
  Work.Spaces.pz_pth_comm (SmoothQuad.contDiffAt_two hf hz hθ hθ2)

/-- `D_z` and `D_θ` commute, from `SmoothQuad`. -/
theorem Dz_Dth_comm {f : Fn} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.Dz (Work.Spaces.Dth f) z θ = Work.Spaces.Dth (Work.Spaces.Dz f) z θ :=
  Work.Spaces.Dz_Dth_comm (SmoothQuad.contDiffAt_two hf hz hθ hθ2)

/-- The `z`-partial of a `SmoothQuad` function is `SmoothQuad` on the same quadrant. -/
theorem contDiffOn_uncurry_pz_quad {G : Fn}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) Quad) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz G)) Quad := by
  have hchain : ∀ p ∈ Quad, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder)
        (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_Quad.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) Quad := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) isOpen_Quad.uniqueDiffOn
      (by simp [Work.Stability.smoothOrder])
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen isOpen_Quad hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) Quad := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a `SmoothQuad` function is `SmoothQuad` on the same quadrant. -/
theorem contDiffOn_uncurry_pth_quad {G : Fn}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) Quad) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth G)) Quad := by
  have hchain : ∀ p ∈ Quad, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder)
        (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_Quad.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) Quad := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) isOpen_Quad.uniqueDiffOn
      (by simp [Work.Stability.smoothOrder])
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen isOpen_Quad hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) Quad := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

end Work.FTS.CoercivityFix
