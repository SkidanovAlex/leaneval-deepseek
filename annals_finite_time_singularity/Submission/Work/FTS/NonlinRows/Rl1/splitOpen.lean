/-
# `splitOpen` — the four-way split of `N` on the open quadrant

The paper's term `N` (`Work.Construction.N`) is

  `2ℛ(Φ̃)F - 2U(Φ̃)∂_θF - 2αV(Φ̃)D_zF - …`   with `F = F_* + g` and
  `Φ̃ = Φ - (1/(4α)) sin(2θ)L₁₂(F)`.

Writing `Φ̃ = Φ̃_* + Φ̃_g` (`PhiTil α (Fstar α) Φs + PhiTil α g Φg`) and `F = F_* + g`, the
identity splits `N` into the sixteen pieces `N_i^{gg} + N_i^{gs} + N_i^{sg} + N_i^{ss}`,
`i = 1..5`, of `Work.FTS.Nonlin.Defs`.

This is the middle conjunct of `Work.FTS.NonlinRows.SplitsData` (the second field of
`Work.FTS.OpenPkg.N4Rows'`), restated with the *local* (only `z > 0`) hypotheses that are
actually available in the open-quadrant row: the identity of the two straightened stream
functions is needed only near a point `z > 0` of the open quadrant; there the additivity
`hL` of `L₁₂`, together with `hL12` (differentiability of `z ↦ L₁₂(g)(z)` for `z > 0`),
identifies the `z`-slice of `Φ̃` with that of `Φ̃_* + Φ̃_g` on a neighbourhood of `z` and the
`θ`-slice at `z` *exactly*.  Hence `∂_zΦ̃ = ∂_zΦ̃_* + ∂_zΦ̃_g` and `∂_θΦ̃ = ∂_θΦ̃_* + ∂_θΦ̃_g`
at `(z,θ)`, which is all the split needs.

The proof is the `SmoothOpen`-analogue of `Work.FTS.Nonlinear.Pieces.rl1Tools.Nsplit`
(which assumes the stronger `SmoothQuad`, i.e. `C^∞` on `z > -1`): the only change is that
the slice differentiability of the data is read off from `SmoothOpen.hasDerivAt_slice` and
`SmoothOpen.curry_θ` (the open-quadrant API) instead of `SmoothQuad`, so the additivity of
`∂_z`, `∂_θ` and `D_z` is obtained through the generic `pz_add_of_diff`/`pth_add_of_diff`
helpers of `splitsDiff.lean`.  Everything else is the same algebra.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Nsplit
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.LocData.SmoothQuad_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The open-quadrant slice API used by the split

The four elementary facts that the `SmoothQuad`-based split obtains from
`Work.FTS.Nonlinear.Pieces.differentiableAt_slice_z`/`_θ`/`pth_add_of_smoothQuad`/
`pz_add_of_smoothQuad`, in the (weaker) class `SmoothOpen` of the primed rows. -/

/-- The `z`-slice of a `SmoothOpen` function is differentiable at every `z > 0`, at every
`θ ∈ (0, π/2)`. -/
theorem openSlice_diffZ {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun z' => f z' θ) z :=
  (hf.hasDerivAt_slice hθ hz).differentiableAt

/-- The `θ`-slice of a `SmoothOpen` function is differentiable at every `θ ∈ (0, π/2)`, at
every `z > 0`. -/
theorem openSlice_diffT {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ :=
  (((hf.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioo.mem_nhds hθ))

/-- `∂_θ` is additive on a sum of two `SmoothOpen` functions, on the open quadrant. -/
theorem openSlice_pth_add {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hh : Work.FTS.EllipticEst.SmoothOpen h) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pth (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth h z θ :=
  Work.FTS.Nonlinear.Pieces.pth_add_of_diff (openSlice_diffT hf hz hθ)
    (openSlice_diffT hh hz hθ)

/-- `∂_z` is additive on a sum of two `SmoothOpen` functions, on the open quadrant. -/
theorem openSlice_pz_add {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hh : Work.FTS.EllipticEst.SmoothOpen h) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ :=
  Work.FTS.Nonlinear.Pieces.pz_add_of_diff (openSlice_diffZ hf hz hθ)
    (openSlice_diffZ hh hz hθ)

theorem splitOpen {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hFK : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
            + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
          + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
          + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
            + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
          + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
            + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
          + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
            + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
  intro z θ hq
  have hz : 0 < z := hq.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  -- ## the identity of the straightened stream functions, near (in `z`) and at (in `θ`) the point
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α g Φg z θ') := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z hz]
    ring
  have hslicez : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α g Φg z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hq.1] with z' hz'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z' hz']
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α g Φg z θ :=
    congrFun hsliceθ θ
  -- ## differentiability of the `z`- and `θ`-slices of the two pieces
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
  have hzs1 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ) z := by
    rw [hPsi1]
    exact (openSlice_diffZ hΦs hz hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (Work.FTS.Nonlinear.Pieces.differentiableAt_L12_Fstar hα hα1 hz))
  have hzs2 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α g Φg z' θ) z := by
    rw [hPsi2]
    exact (openSlice_diffZ hΦg hz hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (hL12 z hz))
  have hts1 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ := by
    rw [hPsi1]
    exact (openSlice_diffT hΦs hz hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  have hts2 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α g Φg z θ') θ := by
    rw [hPsi2]
    exact (openSlice_diffT hΦg hz hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  -- ## additivity of `∂_z` and `∂_θ` at the point
  have hpzP : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := hslicez.deriv_eq
    have hsum : Work.Spaces.pz (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ :=
      Work.FTS.Nonlinear.Pieces.pz_add_of_diff hzs1 hzs2
    simp only [Work.Spaces.pz] at hsum hderiv ⊢
    exact hderiv.trans hsum
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
  -- ## the additivity of the three operators
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Rop]
    rw [hval, hpzP, hpthP]
    ring
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Uop]
    rw [hval, hpzP]
    ring
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Vop]
    rw [hval, hpthP]
    ring
  -- ## additivity of `∂_θ` and `D_z` on `F = F_* + g`
  have hpthF : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
    openSlice_pth_add hF hgs hz hθ
  have hDzF : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff (openSlice_pz_add hF hgs hz hθ)
  -- ## the five groups
  have hN1 : Work.Construction.N1 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
        + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ := by
    simp only [Work.Construction.N1, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N1gs,
      Work.FTS.Nonlin.N1sg, Work.FTS.Nonlin.N1ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs, Work.Construction.Ftot]
    rw [hRop]
    ring
  have hN2 : Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
        + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ := by
    simp only [Work.Construction.N2, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N2gs,
      Work.FTS.Nonlin.N2sg, Work.FTS.Nonlin.N2ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hUop, hpthF]
    ring
  have hN3 : Work.Construction.N3 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
        + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ := by
    simp only [Work.Construction.N3, Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.N3gs,
      Work.FTS.Nonlin.N3sg, Work.FTS.Nonlin.N3ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hVop, hDzF]
    ring
  have hN4 : Work.Construction.N4 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ)
        + (Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ) := by
    simp only [Work.Construction.N4, Work.FTS.Nonlin.N4gg, Work.FTS.Nonlin.N4gs,
      Work.FTS.Nonlin.N4sg, Work.FTS.Nonlin.N4ss, Work.Construction.Ftot]
    simp only [Work.FTS.Nonlinear.Pieces.Dth_eq_s2_mul]
    rw [hFK z hz, hpthF]
    ring
  have hN5 : Work.Construction.N5 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ)
        + (Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
    simp only [Work.Construction.N5, Work.FTS.Nonlin.N5gg, Work.FTS.Nonlin.N5gs,
      Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.N5ss, Work.Construction.Ftot]
    rw [hFK z hz]
    ring
  rw [Work.Construction.N_eq_sum]
  simp only [Pi.add_apply, hN1, hN2, hN3, hN4, hN5]
  ring

end Work.FTS.NonlinRows.Rl1
