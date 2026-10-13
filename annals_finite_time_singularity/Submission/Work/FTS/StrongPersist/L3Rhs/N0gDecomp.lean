/-
# `Work.FTS.StrongPersist.L3Rhs.N0gDecomp` — the structure of the block `N0gSum`

`N0gSum α f = N03g + N04aF + N04bF + N05aF + N05bF + N06F` is the `g`-dependent block of `N₀`
(rows 2–7 of the table of §8 of Elgindi's paper), at the profile `F = F_* + f`.

This module records the *structure* of the block, in the form in which its two estimate
halves are stated:

  `N0gSum α f = L₁₂(f) · Bf α f - Wf α f`

with

* `Bf α f = Vf α f + Vfs α` — the factor multiplying `L₁₂(f)`, split into the `f`-dependent
  part `Vf` and the profile part `Vfs` (which involves `F_*` only);
* `Wf α f = c₂(θ)·L₁₂(F_*)(z)·D_z f` — the row-7 term (the only one in which `L₁₂(f)` does
  not occur).

All the declarations of this module are `sorry`-free; it is the import point of the two
estimate halves (`N0gCoupled`, `N0gLocal`) and of the target file.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.StrongPersist.Degen.FstarSqAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two halves -/

/-- The `f`-dependent part of the factor multiplying `L₁₂(f)` in `N0gSum`. -/
def Vf (α : ℝ) (f : Fn) : Fn := fun z θ =>
  (1 / α) * f z θ
    + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth f z θ
    - Work.Construction.c2m θ * Work.Spaces.Dz f z θ

/-- The `F_*`-dependent part of the factor multiplying `L₁₂(f)` in `N0gSum`. -/
def Vfs (α : ℝ) : Fn := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- The factor multiplying `L₁₂(f)` in the block `N0gSum`. -/
def Bf (α : ℝ) (f : Fn) : Fn := fun z θ => Vf α f z θ + Vfs α z θ

/-- The row-7 term of the block: `c₂(θ)·L₁₂(F_*)(z)·D_z f`. -/
def Wf (α : ℝ) (f : Fn) : Fn := fun z θ =>
  Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
    * Work.Spaces.Dz f z θ

/-- The radial factor `z ↦ L₁₂(f)(z)`. -/
def Mf (f : Fn) : Fn := fun z _ => Work.Construction.L12 f z

/-- **The decomposition of `N0gSum`.** -/
theorem N0gSum_eq (α : ℝ) (f : Fn) :
    N0gSum α f = fun z θ => Mf f z θ * Bf α f z θ - Wf α f z θ := by
  funext z θ
  simp only [N0gSum, Bf, Vf, Vfs, Wf, Mf,
    Work.FTS.Nonlin.N03g, Work.FTS.Nonlin.N04aF, Work.FTS.Nonlin.N04bF,
    Work.FTS.Nonlin.N05aF, Work.FTS.Nonlin.N05bF, Work.FTS.Nonlin.N06F,
    Work.Construction.N03, Work.Construction.N04a, Work.Construction.N04b,
    Work.Construction.N05a, Work.Construction.N05b, Work.Construction.N06]
  ring

/-! ## The `C³`-regularity on the open quadrant -/

private theorem contDiffOn_three_s2 : ContDiffOn ℝ 3 Work.Construction.s2
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  unfold Work.Construction.s2
  fun_prop

private theorem contDiffOn_three_c2m : ContDiffOn ℝ 3 Work.Construction.c2m
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  unfold Work.Construction.c2m
  fun_prop

/-- The `(z,θ) ↦ R z` form of a radial `C³` function. -/
private theorem cd_radial {R : ℝ → ℝ} (hR : ContDiffOn ℝ 3 R (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => R p.1) Work.FTS.EllipticEst.Q0 := by
  have hc := hR.comp contDiff_fst.contDiffOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  simpa only [Function.comp_def] using hc

/-- The `(z,θ) ↦ C θ` form of a `C³` angular function. -/
private theorem cd_angular {C : ℝ → ℝ} (hC : ContDiffOn ℝ 3 C (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => C p.2) Work.FTS.EllipticEst.Q0 := by
  have hc := hC.comp contDiff_snd.contDiffOn
    (fun p hp => by
      obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ⟨h0, h1⟩)
  simpa only [Function.comp_def] using hc

/-- `Bf α f` is `C³` on the open quadrant, for `f` smooth there. -/
private theorem cd_Bf {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Bf α f p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hf3 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf 3
  have hpthf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.pth f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf.pth 3
  have hDzf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.Dz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf.Dz 3
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.Degen.smoothOpen_Fstar α
  have hpthF : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hF.pth 3
  have hDzF : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hF.Dz 3
  have hs2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      Work.FTS.EllipticEst.Q0 := cd_angular contDiffOn_three_s2
  have hc2m : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      Work.FTS.EllipticEst.Q0 := cd_angular contDiffOn_three_c2m
  have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (1 / α) * f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul hf3
  have h2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * (Work.Construction.s2 p.2 * Work.Spaces.pth f p.1 p.2))
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul (hs2.mul hpthf)
  have h3 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Spaces.Dz f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hc2m.mul hDzf
  have h4 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * (Work.Construction.s2 p.2
        * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (hs2.mul hpthF)
  have h5 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hc2m.mul hDzF
  refine (((h1.add h2).sub h3).add h4).sub h5 |>.congr (fun p _ => ?_)
  simp only [Bf, Vf, Vfs]
  ring

/-- **The smoothness of the coupled half** `Mf f · Bf α f`, `C³` on the open quadrant. -/
theorem contDiffOn_three_Mf_mul_Bf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : H6Adm α f) :
    ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Mf f z θ * Bf α f z θ))
      Work.FTS.EllipticEst.Q0 := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem3 : Work.Spaces.HkMem α 3 f :=
    HkMem_of_le_of_smoothOpen α (by norm_num) hsm hf.reg.2
  have hL12 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 3 f hα hα1 hsm hmem3 (by norm_num)
  have hMf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12 f p.1)
      Work.FTS.EllipticEst.Q0 := cd_radial hL12
  have hBf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Bf α f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := cd_Bf hsm
  refine (hMf.mul hBf).congr (fun p _ => ?_)
  simp only [Function.uncurry, Mf]

/-- **The smoothness of the local half** `Wf α f`, `C³` on the open quadrant. -/
theorem contDiffOn_three_Wf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 3 (Function.uncurry (Wf α f)) Work.FTS.EllipticEst.Q0 := by
  have hDzf : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Spaces.Dz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm.Dz 3
  have hc2m : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      Work.FTS.EllipticEst.Q0 := cd_angular contDiffOn_three_c2m
  have hL12F : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => Work.Construction.L12 (Work.Construction.Fstar α) p.1)
      Work.FTS.EllipticEst.Q0 := by
    have hrad : ContDiffOn ℝ 3 (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := by
      have hnum : ContDiffOn ℝ 3 (fun _ : ℝ => 2 * α) (Set.Ioi 0) := contDiffOn_const
      have hden : ContDiffOn ℝ 3 (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
        contDiffOn_const.add contDiffOn_id
      have hdiv := hnum.div hden
        (fun z hz => ne_of_gt (by linarith [show (0 : ℝ) < z from hz]))
      refine hdiv.congr (fun z _ => ?_)
      simp only [Pi.div_apply]
    refine (cd_radial hrad).congr (fun p hp => ?_)
    obtain ⟨hz, -, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)
  refine (hc2m.mul (hL12F.mul hDzf)).congr (fun p _ => ?_)
  simp only [Function.uncurry, Wf]
  ring

/-- **The smoothness conjunct**: `N0gSum α f` is `C³` on the open quadrant. -/
theorem contDiffOn_three_N0gSum {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : H6Adm α f) :
    ContDiffOn ℝ 3 (Function.uncurry (N0gSum α f)) Work.FTS.EllipticEst.Q0 := by
  have h1 := contDiffOn_three_Mf_mul_Bf (f := f) hα hα1 hf
  have h2 := contDiffOn_three_Wf (f := f) hα hα1 hf.reg.1
  rw [N0gSum_eq α f]
  exact (h1.sub h2).congr (fun p _ => by simp only [Function.uncurry])

end Work.FTS.StrongPersist.L3Rhs
