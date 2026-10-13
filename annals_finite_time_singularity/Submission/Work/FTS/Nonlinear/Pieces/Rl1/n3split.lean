import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.Pieces.Rl1

/-!
# `n3split` — the four-way split of the transport term `N₃`

`N₃ = -2α V(Φ̃) D_z F` with `F = F_* + g` and `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F)`.  Writing
`Φ̃ = Φ̃_* + Φ̃_g` with `Φ̃_* = PhiTil α (Fstar α) Φs` and `Φ̃_g = PhiTil α g Φg`
(which uses the additivity `L₁₂(F_* + g) = L₁₂(F_*) + L₁₂(g)` of `hL`, together with the
linearity of `Theta` in `F`) and `F = F_* + g`, the product splits into the four pieces
`N₃^{gg} + N₃^{gs} + N₃^{sg} + N₃^{ss}` of `Work.FTS.Nonlin.Defs`.

This is the `N₃` component of the split in `Work.FTS.Nonlinear.Pieces.splitsDiff`,
restated with the local (`z > 0`) hypotheses available in the `rl1` row.
-/

/-- The additive split of the transport term `N₃` into its four pieces. -/
theorem n3split {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.LocData.SmoothQuad g) (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΦg : Work.FTS.LocData.SmoothQuad Φg)
    (hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N3 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
          + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ := by
  intro z θ hq
  have hz : 0 < z := hq.1
  have hzI : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  have hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  -- the `θ`-slices of the two straightened stream functions are differentiable
  have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hPsi1 : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
      = fun z' θ' => Φs z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 (Work.Construction.Fstar α) z' := rfl
  have hPsi2 : Work.Construction.PhiTil α g Φg
      = fun z' θ' => Φg z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 g z' := rfl
  have hts1 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ := by
    rw [hPsi1]
    exact (Work.FTS.Nonlinear.Pieces.differentiableAt_slice_θ hΦs hzI hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  have hts2 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α g Φg z θ') θ := by
    rw [hPsi2]
    exact (Work.FTS.Nonlinear.Pieces.differentiableAt_slice_θ hΦg hzI hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  -- the `θ`-slice at `z` of `Φ̃(F_tot, Φs + Φg)` is the sum of the two pieces
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α g Φg z θ') := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z hz]
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α g Φg z θ := congrFun hsliceθ θ
  have hpthP : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := congrArg (fun F : ℝ → ℝ => deriv F θ) hsliceθ
    have hsum : Work.Spaces.pth (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ :=
      Work.FTS.Nonlinear.Pieces.pth_add_of_diff hts1 hts2
    simp only [Work.Spaces.pth] at hsum hderiv ⊢
    exact hderiv.trans hsum
  -- additivity of `V` and of `D_z`
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Vop]
    rw [hval, hpthP]
    ring
  have hDzF : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.Nonlinear.Pieces.pz_add_of_smoothQuad hF hreg hzI hθ)
  simp only [Work.Construction.N3, Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.N3gs,
    Work.FTS.Nonlin.N3sg, Work.FTS.Nonlin.N3ss, Work.FTS.Nonlin.PhiTg,
    Work.FTS.Nonlin.PhiTs]
  rw [hVop, hDzF]
  ring

end Work.FTS.Nonlinear.Pieces.Rl1
